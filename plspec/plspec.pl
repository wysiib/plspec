:- module(plspec,[spec_pre/2,spec_post/3,valid/2,
                  defspec/2, defspec_pred/2, defspec_pred_recursive/4,
                  setup_uber_check/3,which_posts/5,check_posts/3,
                  some/2, error_not_matching_any_pre/3,
                  set_error_handler/1]).
                  
:- use_module(library(plunit)).
:- use_module(library(lists), [maplist/2, maplist/3, maplist/4]).

:- dynamic le_spec_pre/2, le_spec_invariant/2, le_spec_invariant/3, le_spec_post/3.
:- dynamic spec_indirection/2, spec_predicate/2, spec_predicate_recursive/2.

%% set up facts

named_spec(Name:Spec, Name, Spec).

le_spec_invariant(Pred, Spec) :-
    le_spec_invariant(Pred, _, Spec).

spec_pre(Pred,PreSpec) :-
    assert(le_spec_pre(Pred,PreSpec)).
spec_invariant(Pred, InvariantSpec) :-
    (maplist(named_spec, InvariantSpec, Names, Specs)
     -> assert(le_spec_invariant(Pred, Names, Specs))
      ; assert(le_spec_invariant(Pred, InvariantSpec))).
spec_post(Pred,PreSpec,PostSpec) :-
    assert(le_spec_post(Pred,PreSpec,PostSpec)).

defspec(SpecId, OtherSpec) :-
    assert(spec_indirection(SpecId, OtherSpec)).
:- meta_predicate defspec_pred(+, 1).
defspec_pred(SpecId, Predicate) :-
    assert(spec_predicate(SpecId, Predicate)).
:- meta_predicate defspec_pred_recursive(+, 1).
defspec_pred_recursive(SpecId, Predicate, MergePred, MergePredInvariant) :-
    assert(spec_predicate_recursive(SpecId, Predicate, MergePred, MergePredInvariant)).



spec_predicate(atomic, atomic).
spec_predicate(integer, integer).
spec_predicate(number, number).
spec_predicate(var, var).
spec_predicate(ground, ground).
spec_predicate(nonvar, nonvar).
spec_predicate(any, true).

true(_).

spec_indirection(int, integer).
spec_indirection([X], list(X)).

spec_predicate_recursive(compound(X), compound(X), and, and_invariant).
spec_predicate_recursive(list(X), list(X), and, and_invariant).
spec_predicate_recursive(and(X), spec_and(X), and, and_invariant).
spec_predicate_recursive(tuple(X), tuple(X), and, and_invariant).
spec_predicate_recursive(one_of(X), spec_and(X), or, or_invariant).

:- dynamic error_handler/1.
error_handler(throw).

:- meta_predicate set_error_handler(+, 0).
set_error_handler(Pred) :-
    retractall(error_handler(_)),
    assert(error_handler(Pred)).



%% built-in recursive specs
compound(Spec, Val, NewSpecs, NewVars) :-
    Spec =.. [Functor|NewSpecs],
    Val =.. [Functor|NewVars].

list(Spec, Val, NewSpecs, NewVals) :-
    nonvar(Val), list1(Val, Spec, NewSpecs, NewVals).
%% list1 only ensures that the value is a list.
%% The type of its members is checked later on in a seperate step.
%% list1 will return a spec for each member.
%% If a tail is a variable, the bound value should be
%% of the same type as the list itself.
list1(L, Spec, [Spec|ST], [H|VT]) :-
    nonvar(L), L = [H|T], !,
    list1(T, Spec, ST, VT).
list1(L, _, [], []) :-
    nonvar(L), L = [], !.
list1(Var, Spec, [list(Spec)], [Var]) :- var(Var).

:- begin_tests(lists).

test(empty_list) :-
    list(Spec, [], Specs, Vals), !,
    var(Spec), Specs == [], Vals == [].

test(list1) :-
    list(int, [1,2,3], Specs, Vals), !,
    Specs == [int, int, int], Vals == [1, 2, 3].

test(list2) :-
    list(list(int), [1,2,3], Specs, Vals), !,
    Specs == [list(int), list(int), list(int)], Vals == [1, 2, 3].

test(list3) :-
    list(int, [X,Y,Z], Specs, Vals), !,
    Specs == [int, int, int], Vals == [X, Y, Z].

:- end_tests(lists).


spec_and(SpecList, Var, SpecList, VarRepeated) :-
    %% this is actually repeat
    length(SpecList,L),
    length(VarRepeated,L),
    maplist(=(Var), VarRepeated).

:- begin_tests(spec_and).

test(empty) :-
    spec_and([], Var, List, VarRepeated), !,
    var(Var), List == [], VarRepeated == [].

test(instantiated_var) :-
    spec_and([int, atomic], X, List, VarRepeated), !,
    List == [int, atomic], VarRepeated == [X, X].

:- end_tests(spec_and).

tuple(SpecList, VarList, SpecList, VarList).


%% merge recursive specs
both_eventually_true(V1, V2, Res) :-
    when((nonvar(V1); nonvar(V2)),
          (nonvar(V1), V1 = true -> freeze(V2, Res = V2) %% look at the other co-routined variable
         ; nonvar(V1) -> Res = V1 %% since it is not true
         ; nonvar(V2), V2 = true -> freeze(V1, Res = V1)
         ; nonvar(V2) -> Res = V2)).


invariand([], [], _, true).
invariand([HSpec|TSpec], [HVal|TVal], Location, R) :-
    setup_check(Location, ResElement,HSpec, HVal),
    freeze(TVal, invariand(TSpec, TVal, Location, ResTail)),
    both_eventually_true(ResElement, ResTail, R).

and_invariant(Specs, Vals, Location, R) :-
    invariand(Specs, Vals, Location, R).

or_invariant([], [], Acc, OrigVals, OrigPattern, Location, UberVar) :-
    freeze(Acc, (Acc == fail -> (reason(OrigPattern, Location, OrigVals, Reason), UberVar = fail(Reason)) ; true)).
or_invariant([H|T], [V|VT], Prior, OrigVals, OrigPattern, Location, UberVar) :-
    setup_check(Location, ResOption, H, V),
    freeze(ResOption, (ResOption == true -> (UberVar = true, Current = true) ; freeze(Prior, (Prior == true -> true; Current = fail)))),
    or_invariant(T, VT, Current, OrigVals, OrigPattern, Location, UberVar).

or_invariant(NewSpecs, NewVals, Location, FutureRes) :-
    or_invariant(NewSpecs, NewVals, [], NewVals, or(NewSpecs), Location, FutureRes).

and([], [], true).
and([S|Specs], [V|Vals], Res) :-
    (evaluate_spec_match(S, V, true)
     -> and(Specs, Vals, Res)
      ; Res = fail(spec_not_matched(S, V))).
or2([HSpec|TSpec], [HVal|TVal]) :-
    (evaluate_spec_match(HSpec, HVal, true)
      -> true
      ;  or2(TSpec, TVal)).
or(Specs, Vals, true) :-
    or2(Specs, Vals), !.
or(Specs, Vals, fail(spec_not_matched_merge(or(Specs), Vals))).



%% check coroutine magic
setup_uber_check(Location,Spec,Val) :-
    setup_check(Location,Res,Spec,Val),
    freeze(Res, ((Res == true) -> true ; error_handler(X), call(X, Res))).

setup_check(Location,Res,Spec,Val) :-
    setup_check_aux(Spec,Location,Val,Res).

setup_check_aux(Spec, Location, Val, Res) :-
    spec_predicate(Spec, Pred), !,
    freeze(Val, (call(Pred, Val) -> true ; reason(Spec, Location, Val, Res))).
setup_check_aux(Spec, Location, Val, Res) :-
    spec_indirection(Spec, OtherSpec), !,
    setup_check_aux(OtherSpec, Location, Val, Res).
setup_check_aux(Spec, Location, Val, Res) :-
    spec_predicate_recursive(Spec, Pred, _MergePred, MergePredInvariant), !,
    freeze(Val, (call(Pred, Val, NewSpecs, NewVals)
                    -> call(MergePredInvariant, NewSpecs, NewVals, Location, Res)
                    ;  reason(Spec, Location, Val, Res))).
setup_check_aux(Spec, Location, _, fail(spec_not_found_in(Spec, Location))).

:- begin_tests(invariants).

test(conform) :-
    setup_uber_check(here, int, _).

test(conform2) :-
    setup_uber_check(here, int, X), !, X = 2.

test(nonconform, [throws(_)]) :-
    setup_uber_check(here, int, X), !, X = a.

test(list_empty) :-
    setup_uber_check(here, list(int), _).

test(list_ground) :-
    setup_uber_check(here, list(int), [1,2,3]).

test(list_ground_later) :-
    setup_uber_check(here, list(int), X), !, X = [1,2,3].

test(partial_list_instantiation) :-
    setup_uber_check(here, list(int), X), !, X = [1,_,3].

test(partial_list_instantiation2) :-
    setup_uber_check(here, list(int), X), !, X = [_,_,3].

test(partial_list_instantiation3) :-
    setup_uber_check(here, list(int), X), !, X = [_|_].

test(partial_list_instantiation4, [throws(_)]) :-
    setup_uber_check(here, list(int), X), !, X = [a|_].

test(partial_list_instantiation5, [throws(_)]) :-
    setup_uber_check(here, list(int), X), !, X = [_, a|_].

test(partial_list_instantiation6, [throws(_)]) :-
    setup_uber_check(here, list(int), X), !, X = [_, _|a].

test(partial_list_instantiation7, [throws(_)]) :-
    setup_uber_check(here, list(int), X), !, X = [1, _|[4,5,a]].

test(partial_list_instantiation8) :-
    setup_uber_check(here, list(int), X), !, X = [1, _|[4,5,6]].

test(one_of1) :-
    setup_uber_check(here, one_of([int, atomic]), _).

test(one_of2) :-
    setup_uber_check(here, one_of([int, atomic]), X), !, X = 1.

test(one_of3) :-
    setup_uber_check(here, one_of([int, atomic]), X), !, X = a.

test(one_of4, throws(_)) :-
    setup_uber_check(here, one_of([int, atomic]), X), !, X = [1].

:- end_tests(invariants).



reason(T, Location, V, Reason) :-
    copy_term(Location, LocationWithoutAttributes, _Goals),
    Reason = ['radong','expected',T,'but got',V,'in',LocationWithoutAttributes].


%% non-coroutine non-magic
which_posts([],[],_,[],[]).
which_posts([Pre|Pres],[Post|Posts],Args,[Pre|PreT],[Post|T]) :-
    maplist(valid,Pre,Args), !,
    which_posts(Pres,Posts,Args,PreT, T).
which_posts([_|Pres],[_|Posts],Args,PreT,T) :-
    which_posts(Pres,Posts,Args,PreT,T).

check_posts([], [], []).
check_posts([Arg|ArgT], [Pre|PreT], [Post|PostT]) :-
    evaluate_spec_match(Post, Arg, Res),
    (Res == true
     -> check_posts(ArgT, PreT, PostT)
      ; error_handler(X),
        call(X, fail(postcondition_violated(matched_pre(Pre), violated_post(Post), value(Arg))))).
    

valid(Spec, Val) :-
    evaluate_spec_match(Spec, Val, true).

evaluate_spec_match(Spec, Val, Res) :-
    spec_predicate(Spec, Predicate), !,
    (call(Predicate, Val)
     -> Res = true
      ; Res = fail(spec_not_matched(Spec, Val))).
evaluate_spec_match(Spec, Val, Res) :-
    spec_predicate_recursive(Spec, Predicate, MergePred, _MergePredInvariant), !,
    (call(Predicate, Val, NewSpecs, NewVals)
     -> call(MergePred, NewSpecs, NewVals, Res)
      ; Res = fail(spec_not_matched(Spec, Val))).
evaluate_spec_match(Spec, Val, Res) :-
    spec_indirection(Spec, NewSpec), !,
    evaluate_spec_match(NewSpec, Val, Res).
evaluate_spec_match(Spec, _, fail(spec_not_found(Spec))).



:- begin_tests(valid).

test(any) :-
    valid(any, _),
    valid(any, 1),
    valid(any, []),
    valid(any, foo(_, _)),
    valid(any, foo).

test(ground) :-
    \+ valid(ground, _),
    valid(ground, 1),
    valid(ground, []),
    \+ valid(ground, foo(_, _)),
    valid(ground, foo(1, 2)),
    valid(ground, foo).

test(list) :-
    \+ valid([any], _),
    valid([any], []),
    valid([any], [a]),
    valid([any], [1]),
    valid([any], [_]),
    valid([any], [[]]),
    valid([any], [any]).

test(list2) :-
    valid([int], [1,2]).

test(list_of_list) :-
    \+ valid([[any]], _),
    \+ valid([[any]], [a]),
    \+ valid([[any]], [_]),
    valid([[any]], []),
    valid([[any]], [[1]]),
    valid([[any]], [[a]]),
    valid([[any]], [[]]).

test(compounds) :-
    valid(compound(foo(any)), foo(_)),
    valid(compound(foo(any)), foo(a)),
    \+ valid(compound(foo(any)), bar(a)),
    \+ valid(compound(foo(any, any)), foo(a)),
    valid(compound(foo(any, any)), foo(a, a)),
    \+ valid(compound(foo(any, var)), foo(a, a)).

test(tuples) :-
    valid(tuple([any]), [_]),
    \+ valid(tuple([any]), []),
    \+ valid(tuple([any]), [_, _]),
    valid(tuple([any, any]), [_, _]).

test(indirection) :-
    valid(int, 3).

test(one_of) :-
    valid(one_of([int, atomic]), 3),
    valid(one_of([int, atomic]), abc),
    \+ valid(one_of([int, atomic]), [1]),
    \+ valid(one_of([int, atomic]), _).

test(and) :-
    valid(and([int, ground]), 3),
    \+ valid(and([int, var]), 3).

:- end_tests(valid).



%% term expansion
:- meta_predicate some(1, +).
some(Goal, List) :-
    some1(List, Goal).
some1([], _) :- fail.
some1([H|_], Goal) :-
    call(Goal,H), !.
some1([_|T], Goal) :-
    some1(T, Goal).


spec_matches([], true, []).
spec_matches([Arg|ArgsT], Res, [Spec|SpecT]) :-
    evaluate_spec_match(Spec, Arg, R),
    (R == true
    -> spec_matches(ArgsT, Res, SpecT)
     ; Res = spec_not_matched(Spec, Arg, in(R))).
    


error_not_matching_any_pre(Functor, Args, PreSpecs) :-
    error_handler(X),
    call(X, ['Radong', Args, 'does not match any spec of', PreSpecs, 'in', Functor]).



expansion(Head,Goal,PreSpecs,InvariantSpecOrEmpty,PrePostSpecs,PostSpecs,NewHead,NewBody) :-
    Head =.. [Functor|Args],
    length(Args, Lenny),
    length(NewArgs, Lenny),
    NewHead =.. [Functor|NewArgs],
    NewBody = (% determine if at least one precondition is fulfilled
               (plspec:some(spec_matches(NewArgs, true), PreSpecs) -> true ; !, plspec:error_not_matching_any_pre(Functor, NewArgs, PreSpecs), fail),
               (InvariantSpecOrEmpty = [InvariantSpec] -> lists:maplist(plspec:setup_uber_check(pred_specs_args(Head, InvariantSpec, Args)),InvariantSpec,Args) ; true),
               % unify with pattern matching of head
               NewArgs = Args,
               % gather all matching postconditions
               plspec:which_posts(PrePostSpecs,PostSpecs,Args,ValidPrePostSpecs,PostsToCheck),
               Goal,
               lists:maplist(plspec:check_posts(Args),ValidPrePostSpecs,PostsToCheck)).

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

:- multifile user:term_expansion/6.
user:term_expansion(Term1, Layout1, Ids, Term2, Layout1, [plspec_token|Ids]) :-
    nonmember(plspec_token, Ids),
    do_expand(Term1, Term2).
