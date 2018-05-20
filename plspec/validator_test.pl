:- module(validator_spec_test, []).
:- use_module(validator).
:- use_module(library(plunit)).


:- begin_tests(setup).

test(spec_predicate) :-
    spec_predicate(atom, atom),
    spec_predicate(atom(X), atom(X)),
    spec_predicate(integer, integer),
    spec_predicate(number, number),
    spec_predicate(float, float),
    spec_predicate(var, var),
    spec_predicate(ground, ground),
    spec_predicate(nonvar, nonvar),
    spec_predicate(any, true).

test(spec_exists_integer) :-
    spec_exists(integer).

test(spec_exists_list) :-
    spec_exists(list(integer)).

:- end_tests(setup).

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
    valid([integer], [1,2]).

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
    valid(integer, 3).

test(one_of) :-
    valid(one_of([integer, atomic]), 3),
    valid(one_of([integer, atomic]), abc),
    \+ valid(one_of([integer, atomic]), [1]),
    \+ valid(one_of([integer, atomic]), _).

test(and) :-
    valid(and([integer, ground]), 3),
    \+ valid(and([integer, var]), 3).

:- end_tests(valid).
