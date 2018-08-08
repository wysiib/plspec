:- use_module(plspec_core).
:- use_module(library(plunit)).

:- enable_all_spec_checks.

fib(N,_) :-
    N < 0, !, fail.
fib(0, 0) :- !.
fib(1, 1) :- !.
fib(N, X) :-
    M is N-1,
    K is N-2,
    fib(M,A),
    fib(K,B),
    X is A+B.

is_fib(X) :-
    is_fib(0,X).
is_fib(N,X) :-
    fib(N,P),
    (P == X ->
        true
    ;
        (P < X ->
            M is N+1,
            is_fib(M,X)
        ;
            fail
        )
    ).

:- defspec_pred(fib, is_fib).


:- spec_pre(next_fib/2, [ground, var]).
:- spec_post(next_fib/2, [ground, var], [ground, fib]).
next_fib(X, Y) :-
    P is 2*X,
    between(X,P,Y),
    Y > X,
    is_fib(Y), !.

next_fib_no_annotations(X,Y) :-
    P is 2*X,
    between(X,P,Y),
    Y > X,
    is_fib(Y), !.

:- begin_tests(contain_determinism, [setup(plspec:set_error_handler(throw)), cleanup(plspec:set_error_handler(plspec_default_error_handler))]).

test(normal_next_fib) :-
    next_fib_no_annotations(8,X),
    X =:= 13.

test(spec_next_fib,[true(X=:=13)]) :-
    next_fib(8,X),
    X =:= 13.

:- end_tests(contain_determinism).
