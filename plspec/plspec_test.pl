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

test(partly_instantiated2, [nondet]) :-
    my_member(a, _).

test(partly_instantiated3, [nondet]) :-
    my_member(c, [a, _, c]).

test(all_variables, [nondet]) :-
    my_member(_, _).

test(not_conform, [throws(_)]) :-
    my_member([], a).

:- end_tests(my_member_spec).



:- plspec:spec_pre(my_compound_foo/1, [foo(any)]).
:- plspec:spec_post(my_compound_foo/1, [foo(ground)], [foo(ground)]).
my_compound_foo(foo(_)).



:- begin_tests(my_compound_foo).

test(conform_call) :-
    my_compound_foo(foo(_)).

test(conform_call2) :-
    my_compound_foo(foo(1)).

test(not_conform, [throws(_)]) :-
    my_compound_foo(bar(_)).

:- end_tests(my_compound_foo).
