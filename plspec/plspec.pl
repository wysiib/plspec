:- module(plspec,[spec_pre/2,spec_post/3,
                  setup_uber_check/3,which_posts/4,check_posts/2,
                  some/2, error_not_matching_any_pre/3]).

:- dynamic le_spec_pre/2, le_spec_invariant/2, le_spec_post/3.

%% set up facts

spec_pre(Pred,PreSpec) :-
    assert(le_spec_pre(Pred,PreSpec)).
spec_invariant(Pred, InvariantSpec) :-
    assert(le_spec_invariant(Pred, InvariantSpec)).
spec_post(Pred,PreSpec,PostSpec) :-
    assert(le_spec_post(Pred,PreSpec,PostSpec)).


%% check coroutine magic
setup_uber_check(Location,A,B) :-
    setup_check(Location,Res,A,B),
    freeze(Res, ((Res == true) -> true ; throw(Res))).

setup_check(Location,Res,A,B) :-
    setup_check_aux(A,Location,B,Res).

setup_check_aux(any,_,_,true) :- !.

%% the following two checks should be done instantly (?)
setup_check_aux(ground,_,X,true) :- ground(X), !.
setup_check_aux(ground,Location,V,false(Reason)) :- reason(ground, Location, V, Reason), !.

setup_check_aux(nonvar,_,X,true) :- nonvar(X), !.
setup_check_aux(nonvar,Location,V,false(Reason)) :- reason(nonvar, Location, V, Reason), !.

setup_check_aux(Spec,Location,Var,R) :-
    when(nonvar(Var),check(Spec,Location,Var,R)).


both_eventually_true(V1, V2, Res) :-
    when((nonvar(V1); nonvar(V2)),
          (nonvar(V1), V1 = true -> freeze(V2, Res = V2) %% look at the other co-routined variable
         ; nonvar(V1) -> Res = V1 %% since it is not true
         ; nonvar(V2), V2 = true -> freeze(V1, Res = V1)
         ; nonvar(V2) -> Res = V2)).


recursive_check_list([], _, _, true).
recursive_check_list([HA|TA], T, Location, R) :-
    setup_check(Location, ResElement, T, HA),
    freeze(TA, recursive_check_list(TA, T, Location, ResTail)),
    both_eventually_true(ResElement, ResTail, R).

recursive_check_tuple([], [], _, true).
recursive_check_tuple([HT|TT], [HA|TA], Location, R) :-
    setup_check(Location, ResElement,HT, HA),
    freeze(TA, recursive_check_tuple(TT, TA, Location, ResTail)),
    both_eventually_true(ResElement, ResTail, R).


setup_and([], _, _, _).
setup_and([H|T], V, Location, UberVar) :-
    setup_check(Location, ResMustBe, H, V),
    freeze(ResMustBe, ((ResMustBe == true ; nonvar(UberVar)) -> true ; reason(H, Location, V, Reason), UberVar = false(Reason))),
    setup_and(T, V, Location, UberVar).


setup_one_of([], V, Acc, OrigPattern, Location, UberVar) :-
    freeze(Acc, Acc == fail -> (reason(OrigPattern, Location, V, Reason), UberVar = false(Reason)) ; true).
setup_one_of([H|T], V, Prior, OrigPattern, Location, UberVar) :-
    setup_check(Location, ResOption, H, V),
    freeze(ResOption, (ResOption == true -> (UberVar = true, Current = true) ; freeze(Prior, (Prior == true -> true; Current = fail)))),
    setup_one_of(T, V, Current, OrigPattern, Location, UberVar).


check(var, L, X, Res) :- reason(var, L, X, Reason), !, Res = false(Reason). % vars should never be bound

check([_],_,[], true) :- !. % empty lists fulfill all list specifications of any type
check([X],Location,[H|T], R) :- !, % TODO: this cut feels iffy (pk, 2017-03-17)
    recursive_check_list([H|T], X, Location, R).
check([X],Location,[H|T], Res) :- reason([X], Location, [H|T], Reason), !, Res = false(Reason).

check(compound(TCompound), Location, VCompound, Res) :-
    compound(TCompound), compound(VCompound),
    TCompound =.. [TFunctor|TArgs],
    VCompound =.. [TFunctor|VArgs], !,
    recursive_check_tuple(TArgs, VArgs, Location, Res).
check(compound(TCompound), Location, VCompound, Res) :-
    reason(compound(TCompound), Location, VCompound, Reason), !, Res = false(Reason).

check(atom,_,X, Res) :- atom(X), !, Res = true.
check(atom,Location,X, Res) :- reason(atom, Location, X, Reason), !, Res = false(Reason).

check(number,_,X, Res) :- number(X), !, Res = true.
check(number,Location,X, Res) :- reason(number, Location, X, Reason), !, Res = false(Reason).

check(int,_,X, Res) :- integer(X), !, Res = true.
check(int,Location,X, Res) :- reason(integer, Location, X, Reason), !, Res = false(Reason).

check(TTuple, Location, VTuple, Res) :-
    TTuple =.. [tuple|TArgs], length(TArgs, L), length(VTuple, L),
    recursive_check_tuple(TArgs, VTuple, Location, FutureRes), !,
    freeze(FutureRes, Res = FutureRes).
check(TTuple, Location, VTuple, Result) :-
    TTuple =.. [tuple|_], !,  reason(TTuple, Location, VTuple, Reason), Result = false(Reason), !.

check(TOneOf, Location, V, Res) :-
    TOneOf =.. [one_of|TArgs],
    setup_one_of(TArgs, V, [], TOneOf, Location, FutureRes), !,
    freeze(FutureRes, Res = FutureRes).
check(TOneOf, Location, V, Res) :-
    TOneOf =.. [one_of|_],
    reason(TOneOf, Location, V, Reason), !,
    Res = false(Reason).

check(TAnd, Location, V, Res) :-
    TAnd =.. [and|TArgs],
    setup_and(TArgs, V, Location, Res), !,
    freeze(FutureRes, Res = FutureRes).
check(TAnd, Location, V, Res) :-
    TAnd =.. [and|_],
    reason(TAnd, Location, V, Reason), !,
    Res = false(Reason).


check(T,Location,V, Result) :-
    reason(T, Location, V, Reason),
    Result = false(Reason).

reason(T, Location, V, Reason) :-
    copy_term(Location, LocationWithoutAttributes, _Goals),
    Reason = ['radong','expected',T,'but got',V,'in',LocationWithoutAttributes].


which_posts([],[],_,[]).
which_posts([Pre|Pres],[Post|Posts],Args,[Post|T]) :-
    maplist(cond_is_true,Pre,Args), !,
    which_posts(Pres,Posts,Args,T).
which_posts([_|Pres],[_|Posts],Args,T) :-
    which_posts(Pres,Posts,Args,T).

check_posts(Args,Posts) :-
    maplist(cond_is_true,Posts,Args), !.
check_posts(_,_) :-
    throw(['radong','postcondition violated']).


cond_is_true(any,_) :- !.
cond_is_true([X],A) :- !,
    nonvar(A),
    maplist(cond_is_true(X),A).
cond_is_true(ground,A) :- !,
    ground(A).
cond_is_true(var,A) :- !,
    var(A).
cond_is_true(atom,A) :- !,
    atom(A).
cond_is_true(int, A) :- !,
    integer(A).
cond_is_true(compound(TCompound), VCompound) :- !,
    compound(TCompound), compound(VCompound),
    TCompound =.. [TFunctor|TArgs],
    VCompound =.. [TFunctor|VArgs],
    maplist(cond_is_true, TArgs, VArgs).
cond_is_true(TTuple, VTuple) :-
    TTuple =.. [tuple|TArgs], !,
    maplist(cond_is_true, TArgs, VTuple).
cond_is_true(TOneOf, V) :-
    TOneOf =.. [one_of|R], !,
    some(cond_is_true1(V), R).
cond_is_true(TAnd, V) :-
    TAnd =.. [and|R],
    maplist(cond_is_true1(V), R).

cond_is_true1(A, B) :-
    cond_is_true(B, A).


:- begin_tests(cond_is_true).

test(any) :-
    cond_is_true(any, _),
    cond_is_true(any, 1),
    cond_is_true(any, []),
    cond_is_true(any, foo(_, _)),
    cond_is_true(any, foo).

test(ground) :-
    \+ cond_is_true(ground, _),
    cond_is_true(ground, 1),
    cond_is_true(ground, []),
    \+ cond_is_true(ground, foo(_, _)),
    cond_is_true(ground, foo(1, 2)),
    cond_is_true(ground, foo).

test(list) :-
    \+ cond_is_true([any], _),
    cond_is_true([any], []),
    cond_is_true([any], [a]),
    cond_is_true([any], [1]),
    cond_is_true([any], [_]),
    cond_is_true([any], [[]]),
    cond_is_true([any], [any]).

test(list_of_list) :-
    \+ cond_is_true([[any]], _),
    \+ cond_is_true([[any]], [a]),
    \+ cond_is_true([[any]], [_]),
    cond_is_true([[any]], []),
    cond_is_true([[any]], [[1]]),
    cond_is_true([[any]], [[a]]),
    cond_is_true([[any]], [[]]).

test(compounds) :-
    cond_is_true(compound(foo(any)), foo(_)),
    cond_is_true(compound(foo(any)), foo(a)),
    \+ cond_is_true(compound(foo(any)), bar(a)),
    \+ cond_is_true(compound(foo(any, any)), foo(a)),
    cond_is_true(compound(foo(any, any)), foo(a, a)),
    \+ cond_is_true(compound(foo(any, var)), foo(a, a)).

test(tuples) :-
    cond_is_true(tuple(any), [_]),
    \+ cond_is_true(tuple(any), []),
    \+ cond_is_true(tuple(any), [_, _]),
    cond_is_true(tuple(any, any), [_, _]).

:- end_tests(cond_is_true).



%% term expansion
:- meta_predicate some(1, +).
some(Goal, List) :-
    some1(List, Goal).
some1([], _) :- fail.
some1([H|_], Goal) :-
    call(Goal,H), !.
some1([_|T], Goal) :-
    some1(T, Goal).

spec_matches(Args, Spec) :-
    maplist(cond_is_true, Spec, Args).


error_not_matching_any_pre(Functor, Args, PreSpecs) :-
    throw(['Radong', Args, 'does not match any spec of', PreSpecs, 'in', Functor]).



expansion(Head,Goal,PreSpecs,InvariantSpecOrEmpty,PrePostSpecs,PostSpecs,NewHead,NewBody) :-
    Head =.. [Functor|Args],
    length(Args, Lenny),
    length(NewArgs, Lenny),
    NewHead =.. [Functor|NewArgs],
    NewBody = (% determine if at least one precondition is fulfilled
               (plspec:some(spec_matches(NewArgs), PreSpecs) -> true ; !, plspec:error_not_matching_any_pre(Functor, NewArgs, PreSpecs), fail),
               (InvariantSpecOrEmpty = [InvariantSpec] -> maplist(plspec:setup_uber_check(Head),InvariantSpec,Args) ; true),
               % unify with pattern matching of head
               NewArgs = Args,
               % TODO: setup coroutiness
               % gather all matching postconditions
               plspec:which_posts(PrePostSpecs,PostSpecs,Args,PostsToCheck),
               Goal,
               maplist(plspec:check_posts(Args),PostsToCheck)).

should_expand(A, F, Arity, PreSpecs) :-
    functor(A,F,Arity),
    findall(PreSpec, le_spec_pre(F/Arity,PreSpec), PreSpecs).

expandeur(':-'(A, B), ':-'(NA, NB)) :-
    should_expand(A, F, Arity, PreSpecs), PreSpecs \= [], !,
    findall(InvSpec,le_spec_invariant(F/Arity,InvSpec),InvariantSpecOrEmpty),
    findall(PreSpec2,le_spec_post(F/Arity,PreSpec2,_),PrePostSpecs),
    findall(PostSpec,le_spec_post(F/Arity,_,PostSpec),PostSpecs),
    expansion(A,B,PreSpecs,InvariantSpecOrEmpty,PrePostSpecs,PostSpecs,NA,NB).

do_expand(':-'(A, B), ':-'(NA, NB)) :-
    expandeur(':-'(A, B), ':-'(NA, NB)).
do_expand(A, ':-'(NA, NB)) :-
    expandeur(':-'(A, true), ':-'(NA, NB)).
do_expand(A,A).

:- multifile term_expansion/2.
user:term_expansion(A, B) :-
    do_expand(A,B).
