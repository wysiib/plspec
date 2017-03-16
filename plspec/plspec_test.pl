:- use_module(plspec).
:- use_module(library(plunit)).

:- plspec:spec_pre(my_member/2,[any,[any]]).
:- plspec:spec_post(my_member/2,[any,[ground]],[ground,[ground]]).
:- plspec:spec_post(my_member/2,[any,var],[any,[any]]).
my_member(E,[E|_]).
my_member(E,[_|T]) :-
    my_member(E,T).

foo(A,B) :-
    my_member(A,B).


:- begin_tests(my_member_spec).

test(instantiated_call, [nondet]) :-
    my_member(a, [a, b, c]).

test(partly_instantiated, [nondet]) :-
    my_member(_, [a, b, c]).

test(partly_instantiated_not_conform, [nondet, throws(_)]) :-
    % second argument is not a list
    my_member(a, _).

test(partly_instantiated3, [nondet]) :-
    my_member(c, [a, _, c]).

test(all_variables_not_conform, [nondet, throws(_)]) :-
    my_member(_, _).

test(not_conform, [throws(_)]) :-
    my_member([], a).

:- end_tests(my_member_spec).



%% multiple pres
:- plspec:spec_pre(my_compound_foo/1, [compound(foo(int))]).
:- plspec:spec_pre(my_compound_foo/1, [compound(foo(atom))]).
:- plspec:spec_post(my_compound_foo/1, [compound(foo(ground))], [compound(foo(ground))]).
my_compound_foo(foo(_)).



:- begin_tests(my_compound_foo).

test(nonconform_call, [throws(_)]) :-
    my_compound_foo(foo(_)).

test(conform_call1) :-
    my_compound_foo(foo(1)).

test(conform_call2) :-
    my_compound_foo(foo(bar)).

test(not_conform, [throws(_)]) :-
    my_compound_foo(bar(_)).

:- end_tests(my_compound_foo).


:- plspec:spec_pre(my_tuple_with_incorrect_spec/1, [tuple(atom, atom)]).
:- plspec:spec_post(my_tuple_with_incorrect_spec/1, [tuple(var, var)], [tuple(atom, atom)]).
my_tuple_with_incorrect_spec([X, X]).



bar(A) :-
    my_tuple_with_incorrect_spec(A).
:- begin_tests(my_tuple).

test(conform) :-
    my_tuple_with_incorrect_spec([a, a]).

test(conform_var, [throws(_)]) :-
    my_tuple_with_incorrect_spec([a, _]).

test(conform_var2, [throws(_)]) :-
    my_tuple_with_incorrect_spec([_, a]).

test(nonconform_both_var, [throws(_)]) :-
    my_tuple_with_incorrect_spec([_, _]).

:- end_tests(my_tuple).


:- plspec:spec_pre(atom_member/2, [atom, [atom]]).
atom_member(X, [X|_]) :- !.
atom_member(X, [_|T]) :-
    atom_member(X, T).


:- begin_tests(atom_member).

test(conform, [nondet]) :-
    atom_member(a, [a,b,c]).

test(not_conform, [throws(_)]) :-
    atom_member(a, X), !,
    X = [a,b,c].

test(not_conform2, [throws(_)]) :-
    atom_member(a, [a,_|_]).

test(not_conform3, [throws(_)]) :-
    atom_member(a, [1,_|_]).


:- end_tests(atom_member).


:- plspec:spec_pre(my_atomic/1, [one_of(atom, [atom])]).
my_atomic([_|_]) :- !, fail.
my_atomic(_).

:- begin_tests(my_atomic).

test(conform) :-
    my_atomic([]).

test(conform2) :-
    \+ my_atomic([foo]).

test(conform3) :-
    my_atomic(foo).

test(not_conform, [throws(_)]) :-
    my_atomic(2).

test(not_conform2, [throws(_)]) :-
    my_atomic(foo(_)).

test(not_conform3, [throws(_)]) :-
    \+ my_atomic([_]).

test(not_conform4, [throws(_)]) :-
    my_atomic([2]).

test(not_conform5, [throws(_)]) :-
    \+ my_atomic([X]), X = 2.

:- end_tests(my_atomic).


not_my_atomic(X) :-
    \+ my_atomic(X).

if_atom_then_my_atomic(X) :-
    (atom(X) -> my_atomic(X)).

if_my_atomic_then_atom(X) :-
    (my_atomic(X) -> atom(X)).


:- plspec:spec_pre(my_or_test/1, [one_of(ground, ground)]).
my_or_test(_).

:- begin_tests(my_or_test).

test(conform) :-
    my_or_test(foo).

test(nonconform, [throws(_)]) :-
    my_or_test(_).

:- end_tests(my_or_test).


:- plspec:spec_pre(my_and_test/1, [and(atom, ground)]).
my_and_test(_).

:- begin_tests(my_and_test).

test(conform) :-
    my_and_test(foo).

test(nonconform, [throws(_)]) :-
    my_and_test([]).

test(nonconform2, [throws(_)]) :-
    my_and_test(_).

:- end_tests(my_and_test).

