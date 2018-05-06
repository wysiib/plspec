:- module(validator_lspec2_test, []).

:- use_module(plspec2).
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

:- begin_tests(validate).

test(any) :-
    validate(any, _),
    validate(any, 1),
    validate(any, []),
    validate(any, foo(_, _)),
    validate(any, foo).

test(ground) :-
    \+ validate(ground, _),
    validate(ground, 1),
    validate(ground, []),
    \+ validate(ground, foo(_, _)),
    validate(ground, foo(1, 2)),
    validate(ground, foo).

test(list) :-
    \+ validate([any], _),
    validate([any], []),
    validate([any], [a]),
    validate([any], [1]),
    validate([any], [_]),
    validate([any], [[]]),
    validate([any], [any]).

test(list2) :-
    validate([integer], [1,2]).

test(list_of_list) :-
    \+ validate([[any]], _),
    \+ validate([[any]], [a]),
    \+ validate([[any]], [_]),
    validate([[any]], []),
    validate([[any]], [[1]]),
    validate([[any]], [[a]]),
    validate([[any]], [[]]).

test(compounds) :-
    validate(compound(foo(any)), foo(_)),
    validate(compound(foo(any)), foo(a)),
    \+ validate(compound(foo(any)), bar(a)),
    \+ validate(compound(foo(any, any)), foo(a)),
    validate(compound(foo(any, any)), foo(a, a)),
    \+ validate(compound(foo(any, var)), foo(a, a)).

test(tuples) :-
    validate(tuple([any]), [_]),
    \+ validate(tuple([any]), []),
    \+ validate(tuple([any]), [_, _]),
    validate(tuple([any, any]), [_, _]).

test(indirection) :-
    validate(integer, 3).

test(one_of) :-
    validate(one_of([integer, atomic]), 3),
    validate(one_of([integer, atomic]), abc),
    \+ validate(one_of([integer, atomic]), [1]),
    \+ validate(one_of([integer, atomic]), _).

test(and) :-
    validate(and([integer, ground]), 3),
    \+ validate(and([integer, var]), 3).

:- end_tests(validate).
