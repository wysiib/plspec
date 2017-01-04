

var ground -> ground ground
ground var -> ground is_list

:- spec_pre(member/2,[any,list(any)]).
:- spec_post(member/2,[any,list(ground)],[ground,list(ground)]).
:- spec_post(member/2,[any,var],[any,list(any)]).
member(E,[E|_]).
member(E,[_|T]) :-
    member(E,T).

=== checking ===
setup_check(Spec,Var) :-
    when(nonvar(Var),check(Spec,Var)).

check(list(X),[]).
check(list(X),[H|T]) :-
    maplist(setup_check(X),[H|T]).
check(_,_) :-
    throw exception.

=== coro based ===
foo :-
    member(A,B).

foo :-
    maplist(setup_check,[any,list(any)],[A,B]),
    which_pre([A,B],Pres),
    member(A,B),
    check_posts([A,B],Pres).
