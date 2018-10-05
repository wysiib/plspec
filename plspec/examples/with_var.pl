:- use_module("../plspec.pl").

:- plspec:enable_all_spec_checks.

:- spec_pre(bind/1,[int]).
:- spec_pre(bind/1,[var]).
:- spec_post(bind/1,[int],[int]).
:- spec_post(bind/1,[var],[int]).
bind(B) :-
    between(1,10,B).


:- spec_pre(foo/2,[var,var]).
:- spec_post(foo/2,[var,var],[int,int]).
foo(X,Res) :-
    bind(X),
    add2(X,Res).


:- spec_pre(add2/2,[int,var]).
:- spec_post(add2/2,[int,var],[int,int]).
add2(X,Y) :-
    Y is X+2.


a(X,Y) :-
    b(X),
    c(Y),
    d(X,Y),
    e(Y,X).
