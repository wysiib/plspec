:- use_module(plspec).
:- use_module(validator).
:- use_module(library(lists), [maplist/2, maplist/3, maplist/4, is_list/1]).

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

:- begin_tests(spec_and).

test(instantiated_var) :-
    spec_and([int, atomic], X, List, VarRepeated), !,
    List == [int, atomic], VarRepeated == [X, X].

:- end_tests(spec_and).

