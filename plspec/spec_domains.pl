:- module(spec_domains,[union/3, intersect/3, simplify_and/2]).


child_parent(int,integer).
child_parent(integer,number).
child_parent(float,number).
child_parent(atom,atomic).
child_parent(atom(X),atom).
child_parent(same(X),atom(X)).
child_parent(number,atomic).
child_parent(atomic,ground).
child_parent(atomic,nonvar).
child_parent(ground,nonvar).

child_parent(nonvar,any).
child_parent(var,any).

child_parent(list(X),list(Y)) :-
    child_parent(X,Y).
child_parent(list(_),any).


ancestor(Ancestor,Me) :-
    child_parent(Me,Ancestor).
ancestor(Ancestor,Me) :-
    child_parent(Other,Ancestor),
    ancestor(Other,Me).

descendant(Desc,Me) :-
    child_parent(Desc,Me).
descendant(Desc,Me) :-
    child_parent(Desc,Other),
    descendant(Other,Me).

spec_compare(<,A,B) :-
    ancestor(B,A),!.
spec_compare(>,A,B) :-
    spec_compare(<,B,A),!.
spec_compare(=,A,A) :- !.
spec_compare(Op,A,B) :-
    compare(Op,A,B).


union(A,A,A) :- !.
union(A,empty,A) :- !.
union(empty,A,A) :- !.
union(A,B,A) :-
    ancestor(A,B),!.
union(A,B,B) :-
    ancestor(B,A),!.
union(A,B,one_of([A,B])) :- !.

intersect(A,A,A) :- !.
intersect(A,B,A) :-
    ancestor(B,A), !.
intersect(A,B,B) :-
    ancestor(A,B), !.
intersect(A,B,C) :-
    A \== B,
    not(ancestor(A,B)),
    not(ancestor(B,A)),!,
    C = empty.



intersect_elem_with_list(A,[H|L],Res) :-
    is_list(A), is_list(H),!,
    maplist(intersect,A,H,P),
    (member(empty,P) -> Res = Next ; Res = [P|Next]),
    intersect_elem_with_list(A,L,Next).
intersect_elem_with_list(_,[],[]) :- !.
intersect_elem_with_list(A,[A|L],[A|Res]) :- !,
    intersect_elem_with_list(A,L,Res).
intersect_elem_with_list(A,[H|L],Res) :-
    intersect(A,H,empty),!,
    intersect_elem_with_list(A,L,Res).
intersect_elem_with_list(A,[H|L],[AnH|Res]) :-
    intersect(A,H,AnH),
    intersect_elem_with_list(A,L,Res).

intersect_list_with_list(L1,L2,Res) :-
    intersect_list_with_list(L1,L2,[],Res).

intersect_list_with_list([],_,Acc,Acc) :- !.
intersect_list_with_list([H|L1],L2,Acc,Res) :-
    intersect_elem_with_list(H,L2,HnL2),
    append(Acc,HnL2,NewAcc),
    intersect_list_with_list(L1,L2,NewAcc,Res).


simplify_and(L,Res) :-
    maplist(simplify_one_of,L,Step1),
    list_to_set(Step1,Step2),
    simplify_and_inner(Step2,Res).

simplify_and_inner([],[]) :- !.
simplify_and_inner([one_of(L)],[one_of(L)]) :- !.
simplify_and_inner([one_of(L),one_of(P)|T],Res) :-
    intersect_list_with_list(L,P,Q),
    (Q = [] -> Res = [] ; simplify_and_inner([one_of(Q)|T],Res)).

simplify_one_of(one_of(L),one_of(Res)) :-
    simplify_or(L,Simple),
    list_to_set(Simple,Res).

simplify_or(L,Res) :-
    simplify_or(L,L,[],Res).

simplify_or([],[],Acc,Acc) :- !.
simplify_or([_|Others],[],Acc,Res) :- !,
    simplify_or(Others,Acc,[],Res).
simplify_or([A|Others],[A|T],Acc,Res) :-!,
    simplify_or([A|Others],T,[A|Acc],Res).
simplify_or([A|Others],[H|T],Acc,Res) :- % A schluckt H
    ancestor(A,H), !,
    simplify_or([A|Others],T,[A|Acc],Res).
simplify_or([A|Others],[H|T],Acc,Res) :- % H schluckt A
    ancestor(H,A),!,
    simplify_or([H|Others],T,[H|Acc],Res).
simplify_or(L,[H|T],Acc,Res) :-
    simplify_or(L,T,[H|Acc],Res).

