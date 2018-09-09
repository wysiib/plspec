:- use_module("../plspec_core.pl").

:- enable_all_spec_checks.

:- plspec:spec_pre(reverse/2,[list(X),list(X)]).
:- plspec:spec_pre(reverse/2,[var,list(any)]).
:- plspec:spec_pre(reverse/2,[list(any),var]).
reverse(L,Rev) :-
    reverse(L,[],Rev).

reverse([],Res,Res) :- !.
reverse([H|T],Acc,Res) :-
    reverse(T,[H|Acc],Res).

palindrom(L) :-
    reverse(L,L).

create_palindrom(L,Palin) :-
    print("yo"),
    reverse(L,Rev),
    append(L,Rev,Palin).
