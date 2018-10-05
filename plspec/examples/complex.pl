:- use_module("../plspec.pl").

:- plspec:enable_all_spec_checks.


foo(A) :-
    range(0,10,L),
    member(A,L).

:- spec_pre(range/3,[int,int,list(int)]).
range(A,B,L) :-
    findall(X,between(A,B,X),L).
