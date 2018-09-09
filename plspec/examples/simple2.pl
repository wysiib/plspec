:- use_module("../plspec.pl").

:- plspec:enable_all_spec_checks.

:- plspec:spec_pre(foo/2,[number,number]).
:- plspec:spec_pre(foo/2,[atom,atom]).
foo(A,B) :-
  bar(A,B).

:- plspec:spec_pre(bar/2,[int,int]).
bar(A,B) :-
    B is A+2.


h(A,B) :-
    foo(A,B).
