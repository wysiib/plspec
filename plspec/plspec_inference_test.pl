:- use_module(plspec_inference).

:- begin_tests(contains_spec).

test(simple_contained) :-
    contains_spec(integer, integer).

test(contained1) :-
    contains_spec(one_of([atom, integer]), integer).

test(contained2) :-
    contains_spec(one_of([atom, integer]), atom).

test(not_contained) :-
    \+ contains_spec(one_of([atom, integer]), atomic).

test(hard_contained) :-
    trace,
    contains_spec(one_of([list(one_of([integer, atom]))]), list(integer)).

%% TODO: tests with more than one variable
% e.g. compound, tuple, ...


:- end_tests(contains_spec).
:- begin_tests(merge_specs).

test(same_spec) :-
    merge_two_specs(integer, integer, X), !,
    X == integer.

test(incompatible_simple) :-
    merge_two_specs(integer, atom, X), !,
    list_to_ord_set([integer, atom], SpecSet),
    X == one_of(SpecSet).

test(incompatible_simple2) :-
    Specs = [integer, compound(foo(integer))],
    merge_two_specs(integer, compound(foo(integer)), X), !,
    list_to_ord_set(Specs, SpecSet),
    X == one_of(SpecSet).

test(somewhat_compatible) :-
    Specs = [compound(foo(integer)), compound(foo(atom))],
    merge_two_specs(compound(foo(integer)), compound(foo(atom)), X), !,
    list_to_ord_set(Specs, SpecSet),
    X == compound(foo(one_of(SpecSet))).

:- end_tests(merge_specs).
