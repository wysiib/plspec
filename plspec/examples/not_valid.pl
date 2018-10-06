 :- use_module("../plspec_core.pl").

:- enable_all_spec_checks.

:- spec_pre(foo/2,[int,int]).
foo(A,B) :-
    bar(A,B).

:- spec_pre(bar/2,[atom,atom]).
bar(A,B) :-
    A = a,
    B = b.

