:- module(plspec,[spec_pre/2,spec_post/3,spec_invariant/2,valid/2,
                  defspec/2, defspec_pred/2, defspec_pred_recursive/4, defspec_connective/4,
                  setup_uber_check/3,which_posts/5,check_posts/3,
                  plspec_some/2, error_not_matching_any_pre/3,
                  enable_spec_check/1, enable_all_spec_checks/0,
                  spec_set_debug_mode/0,
                  set_error_handler/1,
                  le_spec_pre/2, le_spec_invariant/2, le_spec_post/3, check_predicate/1 % called by term expander
               ]).

:- use_module(library(plunit)).
:- use_module(library(lists), [maplist/2, maplist/3, maplist/4, is_list/1]).
:- use_module(library(terms), [variant/2]).

:- dynamic le_spec_pre/2, le_spec_invariant/2, le_spec_invariant/3, le_spec_post/3.
:- dynamic spec_indirection/2, spec_predicate/2, spec_predicate_recursive/4, spec_connective/4.

%% set up facts

named_spec(Name:Spec, Name, Spec).

le_spec_invariant(Pred, Spec) :-
    le_spec_invariant(Pred, _, Spec).

spec_pre(Pred,PreSpec) :-
    (ground(PreSpec) -> true ; format('plspec: a pre spec should be ground, got ~w in ~w~n', [PreSpec, Pred]), fail),
    (Pred = _:_/Arity),
    (length(PreSpec, Arity) -> true ; format('plspec: a pre spec of ~w does not match in length~n', [Pred])),
    assert(le_spec_pre(Pred,PreSpec)).
spec_invariant(Pred, InvariantSpec) :-
    (ground(InvariantSpec) -> true ; format('plspec: an invariant spec should be ground, got ~w in ~w~n', [InvariantSpec, Pred]), fail),
    Pred = _:_/Arity,
    (length(InvariantSpec, Arity) -> true ; format('plspec: invariant spec of ~w does not match in length~n', [Pred])),
    (maplist(named_spec, InvariantSpec, Names, Specs)
     -> assert(le_spec_invariant(Pred, Names, Specs))
      ; assert(le_spec_invariant(Pred, InvariantSpec))).
spec_post(Pred,PreSpec,PostSpec) :-
    (ground(PreSpec) -> true ; format('plspec: an post spec should be ground, got ~w in ~w~n', [PreSpec, Pred]), fail),
    (ground(PostSpec) -> true ; format('plspec: an post spec should be ground, got ~w in ~w~n', [PostSpec, Pred]), fail),
    Pred = _:_/Arity,
    (length(PreSpec, Arity) -> true ; format('plspec: a post spec (precondition) of ~w does not match in length~n', [Pred])),
    (length(PostSpec, Arity) -> true ; format('plspec: a post spec (postcondition) of ~w does not match in length~n', [Pred])),
    assert(le_spec_post(Pred,PreSpec,PostSpec)).

spec_exists(X) :- spec_indirection(X, _).
spec_exists(X) :- spec_predicate(X, _).
spec_exists(X) :- spec_predicate_recursive(X, _, _, _).
spec_exists(X) :- spec_connective(X, _, _, _).
spec_exists(X, indirection(Y)) :- spec_indirection(X, Y).
spec_exists(X, predicate(Y)) :- spec_predicate(X, Y).
spec_exists(X, predicate_recursive(A,B,C)) :- spec_predicate_recursive(X, A, B, C).
spec_exists(X, connective(A,B,C)) :- spec_connective(X, A, B, C).

:- dynamic spec_debug/0.
debug_format(Format, Args) :-
    (spec_debug -> format(Format, Args) ; true).

spec_set_debug_mode :-
    assert(spec_debug).

defspec(SpecId, OtherSpec) :-
    (spec_exists(SpecId, Existing)
      %% we use variant in order to determine whether it is actually the same spec;
      % for example, consider defspec(foo(X,Y), bar(X,Y)), defspec(foo(X,Y), bar(Y,X)).
      % we do not want to unify X = Y but also notice these are not the same specs.
      -> (variant(spec(SpecId, Existing), spec(SpecId, indirection(OtherSpec)))
          -> debug_format('spec is overwritten with itself, proceeding~n', [SpecId])
           ; format('plspec: spec ~w already exists, will not be redefined~n', [SpecId]))
       ; assert(spec_indirection(SpecId, OtherSpec))).
:- meta_predicate defspec_pred(+, 1).
defspec_pred(SpecId, Predicate) :-
    (spec_exists(SpecId, Existing)
      -> (variant(spec(SpecId, Existing), spec(SpecId, predicate(Predicate)))
          -> debug_format('spec is overwritten with itself, proceeding~n', [SpecId])
           ; format('plspec: spec ~w already exists, will not be redefined~n', [SpecId]))
       ; assert(spec_predicate(SpecId, Predicate))).
:- meta_predicate defspec_pred_recursive(+, 3,3,4).
defspec_pred_recursive(SpecId, Predicate, MergePred, MergePredInvariant) :-
    (spec_exists(SpecId, Existing)
      -> (variant(spec(SpecId, Existing), spec(SpecId, predicate_recursive(Predicate, MergePred, MergePredInvariant)))
          -> debug_format('spec is overwritten with itself, proceeding~n', [SpecId])
           ; format('plspec: spec ~w already exists, will not be redefined~n', [SpecId]))
       ; assert(spec_predicate_recursive(SpecId, Predicate, MergePred, MergePredInvariant))).
:- meta_predicate defspec_connective(+, 3,3,4).
defspec_connective(SpecId, Predicate, MergePred, MergePredInvariant) :-
    (spec_exists(SpecId, Existing)
      -> (variant(spec(SpecId, Existing), spec(SpecId, connective(Predicate, MergePred, MergePredInvariant)))
          -> debug_format('spec is overwritten with itself, proceeding~n', [SpecId]))
           ; format('plspec: spec ~w already exists, will not be redefined~n', [SpecId])
       ; assert(spec_connective(SpecId, Predicate, MergePred, MergePredInvariant))).


:- dynamic check_predicate/1.
enable_spec_check([H|T]) :- !,
    maplist(enable_spec_check, [H|T]).
enable_spec_check(X) :-
    assert(check_predicate(X)).
enable_all_spec_checks :-
    assert(check_predicate(_)).



spec_predicate(atomic, atomic).
spec_predicate(atom, atom).
spec_predicate(atom(X), atom(X)).
spec_predicate(integer, integer).
spec_predicate(number, number).
spec_predicate(float, float).
spec_predicate(var, var).
spec_predicate(ground, ground).
spec_predicate(nonvar, nonvar).
spec_predicate(any, true).

:- public true/1.
true(_).
:- public atom/2.
atom(X, Y) :- atom(Y), X = Y.

spec_indirection(int, integer).
spec_indirection([X], list(X)).

spec_predicate_recursive(compound(X), compound(X), and, and_invariant).
spec_predicate_recursive(list(X), list(X), and, and_invariant).
spec_predicate_recursive(tuple(X), tuple(X), and, and_invariant).

spec_connective(and([H|T]), spec_and([H|T]), and, and_invariant).
spec_connective(one_of(X), spec_and(X), or, or_invariant).


pretty_print_error(fail(postcondition_violated(matched_pre(Pre), violated_post(Post), value(Val)))) :-
    format('~n! plspec: a postcondition was violated!~n', []),
    format('! plspec: the matched precondition was "~w"~n', [Pre]),
    format('! plspec: however, the postcondition "~w" does not hold~n', [Post]),
    format('! plspec: the offending value was: ~w~n', [Val]).
pretty_print_error(fail(prespec_violated(specs(PreSpecs), values(Vals), location(Functor)))) :-
    format('~n! plspec: no precondition was matched in ~w~n', [Functor]),
    format('! plspec: specified preconditions were: ~w~n', [PreSpecs]),
    format('! plspec: however, none of these is matched by: ~w~n', [Vals]).
pretty_print_error(fail(spec_violated(spec(T), value(V), location(Location)))) :-
    format('~n! plspec: an invariant was violated in ~w~n', [Location]),
    format('! plspec: the spec was: ~w~n', [T]),
    format('! plspec: however, the value was bound to: ~w~n', [V]).
pretty_print_error(fail(spec_not_found(spec(Spec)))) :-
    %% TODO: not all failures include a location
    format('~n! plspec: spec "~w" was not found~n', [Spec]).
pretty_print_error(fail(spec_not_found(spec(Spec), location(Location)))) :-
    format('~n! plspec: a spec for ~w was not found~n', [Location]),
    format('! plspec: spec "~w" was not found~n', [Spec]).
pretty_print_error(X) :-
    format('~n! plspec: plspec raised an error that is unhandled.~n', []),
    format('! plspec: ~w.~n', [X]).

pretty_print_error(fail(postcondition_violated(matched_pre(Pre), violated_post(Post), value(Val)))) :-
    format('~n! plspec: a postcondition was violated!~n', []),
    format('! plspec: the matched precondition was "~w"~n', [Pre]),
    format('! plspec: however, the postcondition "~w" does not hold~n', [Post]),
    format('! plspec: the offending value was: ~w~n', [Val]).
pretty_print_error(fail(prespec_violated(specs(PreSpecs), values(Vals), location(Functor)))) :-
    format('~n! plspec: no precondition was matched in ~w~n', [Functor]),
    format('! plspec: specified preconditions were: ~w~n', [PreSpecs]),
    format('! plspec: however, none of these is matched by: ~w~n', [Vals]).
pretty_print_error(fail(spec_violated(spec(T), value(V), location(Location)))) :-
    format('~n! plspec: an invariant was violated in ~w~n', [Location]),
    format('! plspec: the spec was: ~w~n', [T]),
    format('! plspec: however, the value was bound to: ~w~n', [V]).
pretty_print_error(fail(spec_not_found(spec(Spec)))) :-
    %% TODO: not all failures include a location
    format('~n! plspec: spec "~w" was not found~n', [Spec]).
pretty_print_error(fail(spec_not_found(spec(Spec), location(Location)))) :-
    format('~n! plspec: a spec for ~w was not found~n', [Location]),
    format('! plspec: spec "~w" was not found~n', [Spec]).
pretty_print_error(X) :-
    format('~n! plspec: plspec raised an error that is unhandled.~n', []),
    format('! plspec: ~w.~n', [X]).

pretty_print_error(fail(postcondition_violated(matched_pre(Pre), violated_post(Post), value(Val)))) :-
    format('~n! plspec: a postcondition was violated!~n', []),
    format('! plspec: the matched precondition was "~w"~n', [Pre]),
    format('! plspec: however, the postcondition "~w" does not hold~n', [Post]),
    format('! plspec: the offending value was: ~w~n', [Val]).
pretty_print_error(fail(prespec_violated(specs(PreSpecs), values(Vals), location(Functor)))) :-
    format('~n! plspec: no precondition was matched in ~w~n', [Functor]),
    format('! plspec: specified preconditions were: ~w~n', [PreSpecs]),
    format('! plspec: however, none of these is matched by: ~w~n', [Vals]).
pretty_print_error(fail(spec_violated(spec(T), value(V), location(Location)))) :-
    format('~n! plspec: an invariant was violated in ~w~n', [Location]),
    format('! plspec: the spec was: ~w~n', [T]),
    format('! plspec: however, the value was bound to: ~w~n', [V]).
pretty_print_error(fail(spec_not_found(spec(Spec)))) :-
    %% TODO: not all failures include a location
    format('~n! plspec: spec "~w" was not found~n', [Spec]).
pretty_print_error(fail(spec_not_found(spec(Spec), location(Location)))) :-
    format('~n! plspec: a spec for ~w was not found~n', [Location]),
    format('! plspec: spec "~w" was not found~n', [Spec]).
pretty_print_error(X) :-
    format('~n! plspec: plspec raised an error that is unhandled.~n', []),
    format('! plspec: ~w.~n', [X]).

:- dynamic error_handler/1.
error_handler(plspec_default_error_handler).

:- public plspec_default_error_handler/1.
plspec_default_error_handler(X) :-
    pretty_print_error(X),
    throw(plspec_error).

:- meta_predicate set_error_handler(1).
set_error_handler(Pred) :-
    retractall(error_handler(_)),
    assert(error_handler(Pred)).



%% built-in recursive specs
:- public compound/4.
compound(Spec, Val, NewSpecs, NewVars) :-
    compound(Val),
    Val =.. [Functor|NewVars],
    Functor \= '[|]',
    length(NewVars, Len),
    length(NewSpecs, Len),
    Spec =.. [Functor|NewSpecs].

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
    SpecList \= [],
    %% this is actually repeat
    length(SpecList,L),
    length(VarRepeated,L),
    maplist(=(Var), VarRepeated).

:- begin_tests(spec_and).

test(instantiated_var) :-
    spec_and([int, atomic], X, List, VarRepeated), !,
    List == [int, atomic], VarRepeated == [X, X].

:- end_tests(spec_and).

:- public tuple/4.
tuple(SpecList, VarList, SpecList, VarList) :-
    is_list(VarList).


%% merge recursive specs
both_eventually_true(V1, V2, Res) :-
    when((nonvar(V1); nonvar(V2)),
          (V1 == true -> freeze(V2, Res = V2) %% look at the other co-routined variable
         ; nonvar(V1) -> Res = V1 %% since it is not true
         ; V2 == true -> freeze(V1, Res = V1)
         ; nonvar(V2) -> Res = V2)).


invariand([], [], _, true).
invariand([HSpec|TSpec], [HVal|TVal], Location, R) :-
    setup_check(Location, ResElement,HSpec, HVal),
    freeze(TVal, invariand(TSpec, TVal, Location, ResTail)), % TODO: do we need this freeze?
    both_eventually_true(ResElement, ResTail, R).

:- public and_invariant/4.
and_invariant(Specs, Vals, Location, R) :-
    invariand(Specs, Vals, Location, R).

or_invariant([], [], Acc, OrigVals, OrigPattern, Location, UberVar) :-
    freeze(Acc, (Acc == fail -> (reason(OrigPattern, Location, OrigVals, Reason), UberVar = Reason) ; true)).
or_invariant([H|T], [V|VT], Prior, OrigVals, OrigPattern, Location, UberVar) :-
    setup_check(Location, ResOption, H, V),
    freeze(ResOption, (ResOption == true -> (UberVar = true, Current = true) ; freeze(Prior, (Prior == true -> true; Current = fail)))),
    or_invariant(T, VT, Current, OrigVals, OrigPattern, Location, UberVar).

:- public or_invariant/4.
or_invariant(NewSpecs, NewVals, Location, FutureRes) :-
    or_invariant(NewSpecs, NewVals, [], NewVals, or(NewSpecs), Location, FutureRes).

:- public and/3.
and([], [], true).
and([S|Specs], [V|Vals], Res) :-
    evaluate_spec_match(S, V, X),
    (X == true
     -> and(Specs, Vals, Res)
      ; Res = fail(spec_not_matched(spec(S), value(V)))).
or2([HSpec|TSpec], [HVal|TVal]) :-
    (evaluate_spec_match(HSpec, HVal, true)
      -> true
      ;  or2(TSpec, TVal)).
:- public or/3.
or(Specs, Vals, true) :-
    or2(Specs, Vals), !.
or(Specs, Vals, fail(spec_not_matched_merge(specs(or(Specs)), values(Vals)))).



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
setup_check_aux(Spec, Location, Val, Res) :-
    spec_connective(Spec, Pred, _MergePred, MergePredInvariant), !,
    freeze(Val, (call(Pred, Val, NewSpecs, NewVals)
                    -> call(MergePredInvariant, NewSpecs, NewVals, Location, Res)
                    ;  reason(Spec, Location, Val, Res))).
setup_check_aux(Spec, Location, _, fail(spec_not_found(spec(Spec), location(Location)))).

:- begin_tests(invariants, [setup(set_error_handler(throw)), cleanup(set_error_handler(plspec_default_error_handler))]).

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
    Reason = fail(spec_violated(spec(T), value(V), location(LocationWithoutAttributes))).


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
    evaluate_spec_match(Spec, Val, X),
    X == true.

evaluate_spec_match(Spec, _, fail(spec_not_found(spec(Spec)))) :-
    nonvar(Spec),
    \+ spec_exists(Spec), !,
    format('plspec: spec ~w not found~n', [Spec]).
evaluate_spec_match(Spec, Val, Res) :-
    %spec_exists(Spec),
    evaluate_spec_match_aux(Spec, Val, Res).
evaluate_spec_match_aux(Spec, Val, Res) :-
    spec_predicate(Spec, Predicate),
    %% HACK: copy_term does weird things to co-routines
    copy_term(Val, Vali),
    (call(Predicate, Val)
     -> Res = true
      ; Res = fail(spec_not_matched(spec(Spec), value(Val)))),
    (copy_term(Val, Valii), variant(Valii, Vali) -> true ; format('plspec: implementation of spec ~w binds variables but should not~n', [Predicate])).
evaluate_spec_match_aux(Spec, Val, Res) :-
    spec_predicate_recursive(Spec, Predicate, MergePred, _MergePredInvariant),
    copy_term(Val, Vali),
    (call(Predicate, Val, NewSpecs, NewVals)
     -> call(MergePred, NewSpecs, NewVals, Res)
      ; Res = fail(spec_not_matched(spec(Spec), value(Val)))),
    (copy_term(Val, Valii), variant(Valii, Vali) -> true ; format('plspec: implementation of spec ~w binds variables but should not~n', [Predicate])).
evaluate_spec_match_aux(Spec, Val, Res) :-
    nonvar(Spec),
    spec_connective(Spec, Predicate, MergePred, _MergePredInvariant),
    copy_term(Val, Vali),
    (call(Predicate, Val, NewSpecs, NewVals)
     -> call(MergePred, NewSpecs, NewVals, Res)
      ; Res = fail(spec_not_matched(spec(Spec), value(Val)))),
    (copy_term(Val, Valii), variant(Valii, Vali) -> true ; format('plspec: implementation of spec ~w binds variables but should not~n', [Predicate])).
evaluate_spec_match_aux(Spec, Val, Res) :-
    spec_indirection(Spec, NewSpec),
    evaluate_spec_match(NewSpec, Val, Res).




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
:- meta_predicate plspec_some(1, +).
plspec_some(Goal, List) :-
    plspec_some1(List, Goal).
plspec_some1([], _) :- fail.
plspec_some1([H|_], Goal) :-
    call(Goal,H), !.
plspec_some1([_|T], Goal) :-
    plspec_some1(T, Goal).

:- public spec_matches/3. %THIS SEEMS NOT USED - TO DO: investigate
spec_matches([], true, []).
spec_matches([Arg|ArgsT], Res, [Spec|SpecT]) :-
    evaluate_spec_match(Spec, Arg, R),
    (R == true
    -> spec_matches(ArgsT, Res, SpecT)
     ; Res = spec_not_matched(Spec, Arg, in(R))).



error_not_matching_any_pre(Functor, Args, PreSpecs) :-
    error_handler(X),
    call(X, fail(prespec_violated(specs(PreSpecs), values(Args), location(Functor)))).


expansion(Head,Goal,PreSpecs,InvariantSpecOrEmpty,PrePostSpecs,PostSpecs,NewHead,NewBody) :-
    Head =.. [Functor|Args],
    length(Args, Lenny),
    %% newargs: only relevant if head implements pattern matching:
    % consider foo(foo). then the call 'foo(bar)' would not violate the spec but only fail
    % thus, we insert a fresh variable and check the unification with the argument term later on
    length(NewArgs, Lenny),
    NewHead =.. [Functor|NewArgs],
    NewBody = (% determine if at least one precondition is fulfilled
               (PreSpecs = [] -> true ; (plspec:plspec_some(spec_matches(NewArgs, true), PreSpecs) -> true ; plspec:error_not_matching_any_pre(Functor/Lenny, NewArgs, PreSpecs))),
               (InvariantSpecOrEmpty = [InvariantSpec] -> lists:maplist(plspec:setup_uber_check(Functor/Lenny),InvariantSpec,Args) ; true), 
               % unify with pattern matching of head
               NewArgs = Args,
               % gather all matching postconditions
               plspec:which_posts(PrePostSpecs,PostSpecs,Args,ValidPrePostSpecs,PostsToCheck),
               Goal,
               lists:maplist(plspec:check_posts(Args),ValidPrePostSpecs,PostsToCheck)).

should_expand(A, F, Module, Arity) :-
    functor(A,F,Arity),
    %trace,
    (plspec:le_spec_pre(Module:F/Arity, _) ; plspec:le_spec_invariant(Module:F/Arity, _) ; plspec:le_spec_post(Module:F/Arity, _, _)), !,
    plspec:check_predicate(F/Arity).

expandeur(':-'(A, B), Module, ':-'(NA, NB)) :-
    should_expand(A, F, Module, Arity), !,
    findall(PreSpec, plspec:le_spec_pre(Module:F/Arity,PreSpec), PreSpecs),
    findall(InvSpec, plspec:le_spec_invariant(Module:F/Arity,InvSpec),InvariantSpecOrEmpty),
    findall(PreSpec2,plspec:le_spec_post(Module:F/Arity,PreSpec2,_),PrePostSpecs),
    findall(PostSpec,plspec:le_spec_post(Module:F/Arity,_,PostSpec),PostSpecs),
    expansion(A,B,PreSpecs,InvariantSpecOrEmpty,PrePostSpecs,PostSpecs,NA,NB).

do_expand(':-'(spec_pre(Predicate/Arity, Spec)), Module, ':-'(spec_pre(Module:Predicate/Arity, Spec))).
do_expand(':-'(spec_invariant(Predicate/Arity, Spec)), Module, ':-'(spec_invariant(Module:Predicate/Arity, Spec))).
do_expand(':-'(spec_post(Predicate/Arity, SpecPre, SpecPost)), Module, ':-'(spec_post(Module:Predicate/Arity, SpecPre, SpecPost))).
do_expand(':-'(plspec:spec_pre(Predicate/Arity, Spec)), Module, ':-'(plspec:spec_pre(Module:Predicate/Arity, Spec))).
do_expand(':-'(plspec:spec_invariant(Predicate/Arity, Spec)), Module, ':-'(plspec:spec_invariant(Module:Predicate/Arity, Spec))).
do_expand(':-'(plspec:spec_post(Predicate/Arity, SpecPre, SpecPost)), Module, ':-'(plspec:spec_post(Module:Predicate/Arity, SpecPre, SpecPost))).
do_expand(':-'(A, B), Module, ':-'(NA, NB)) :-
    expandeur(':-'(A, B), Module, ':-'(NA, NB)).
do_expand(A, Module, ':-'(NA, NB)) :-
    expandeur(':-'(A, true), Module, ':-'(NA, NB)).
do_expand(A, _Module, A).


:- multifile term_expansion/2.
user:term_expansion(A, B) :-
    prolog_load_context(module, Module),
    do_expand(A, Module, B).

:- multifile user:term_expansion/6.
user:term_expansion(Term1, Layout1, Ids, Term2, Layout1, [plspec_token|Ids]) :-
    nonmember(plspec_token, Ids),
    prolog_load_context(module, Module),
    do_expand(Term1, Module, Term2).
