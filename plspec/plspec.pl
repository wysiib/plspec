:- module(plspec,[spec_pre/2,spec_post/3,
                  setup_uber_check/3,which_pres/4,check_posts/2]).

:- dynamic le_spec_pre/2, le_spec_post/3.

%% set up facts

spec_pre(Pred,PreSpec) :-
    assert(le_spec_pre(Pred,PreSpec)).
spec_post(Pred,PreSpec,PostSpec) :-
    assert(le_spec_post(Pred,PreSpec,PostSpec)).


%% check magic
setup_uber_check(Location,A,B) :-
    setup_check(Location,Res,A,B),
    freeze(Res, (Res == true) -> true ; throw(Res)).

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


check(var, L, X, Res) :- reason(var, L, X, Reason), !, Res = false(Reason). % vars should never be bound

check([_],_,[], true) :- !. % empty lists fulfill all list specifications of any type
check([X],Location,[H|T], R) :-
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

check(TTuple, Location, VTuple, Res) :-
    TTuple =.. [tuple|TArgs], length(TArgs, L), length(VTuple, L),
    recursive_check_tuple(TArgs, VTuple, Location, FutureRes), !,
    freeze(FutureRes, Res = FutureRes).
check(TTuple, Location, VTuple, Result) :-
    TTuple =.. [tuple|_], !,  reason(TTuple, Location, VTuple, Reason), Result = false(Reason), !.

check(T,Location,V, Result) :-
    reason(T, Location, V, Reason),
    Result = false(Reason).

reason(T, Location, V, Reason) :-
    Reason = ['radong','expected',T,'but got',V,'in',Location].


which_pres([],[],_,[]).
which_pres([Pre|Pres],[Post|Posts],Args,[Post|T]) :-
    maplist(cond_is_true,Pre,Args), !,
    which_pres(Pres,Posts,Args,T).
which_pres([_|Pres],[_|Posts],Args,T) :-
    which_pres(Pres,Posts,Args,T).

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
cond_is_true(compound(TCompound), VCompound) :- !,
    compound(TCompound), compound(VCompound),
    TCompound =.. [TFunctor|TArgs],
    VCompound =.. [TFunctor|VArgs],
    maplist(cond_is_true, TArgs, VArgs).
cond_is_true(TTuple, VTuple) :-
    TTuple =.. [tuple|TArgs], !,
    maplist(cond_is_true, TArgs, VTuple).


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

do_expand((A:-B),(A:-NB)) :-
    expand_body(B,NB).

body_expansion(Body,PreSpec,PreSpecs,PostSpecs,NewBody) :-
    Body =.. [_|Args],
    NewBody = (maplist(plspec:setup_uber_check(Body),PreSpec,Args),
               plspec:which_pres(PreSpecs,PostSpecs,Args,PostsToCheck),
               Body,
               maplist(plspec:check_posts(Args),PostsToCheck)).

expand_body((A,B),(NA,NB)) :- !,
  expand_body(A,NA), expand_body(B,NB).
expand_body({A},{NA}) :- !,
  expand_body(A,NA).
expand_body(A,NA) :-
    functor(A,F,Arity),
    le_spec_pre(F/Arity,PreSpec), !,
    findall(PreSpec2,le_spec_post(F/Arity,PreSpec2,_),PreSpecs),
    findall(PostSpec,le_spec_post(F/Arity,_,PostSpec),PostSpecs),
    body_expansion(A,PreSpec,PreSpecs,PostSpecs,NA).
expand_body(A,A).

:- multifile term_expansion/2.
user:term_expansion(A, B) :-
    do_expand(A,B).
