:- module(domain, [dom_intersect/2, dom_intersect/3]).
:- use_module(validator).

dom_super(integer,number) :- !.
dom_super(float,number) :- !.

dom_super(number,atomic) :- !.
dom_super(atom,atomic) :- !.
dom_super(atom(_),atom) :- !.

dom_super(atomic, ground).
dom_super(compound, ground).

%number = or(integer, float)
%atomic = or(number,atom)
%compound = or(list(X),compound(X),tuple(X)) ?
%TODO: Difference ground, var?
%what happens with same(X)?


dom_super(a,x).
dom_super(b,x).
dom_super(c,a).
dom_super(d,a).
dom_super(e,b).
dom_super(f,b).
dom_super(g,c).
dom_super(h,c).

% If A is from Domain X and Domain Y, we want to find the smallest
% Domain Z of a

dom_intersect(A,B,Res) :-
  dom_intersect1(A,B,R),!,
  (R = one_of(P) -> post_processing(one_of(P),Res) ; Res = R).
dom_intersect(_,_,bottom) :- !.


post_processing(one_of(P),R) :-
  sort(P,Sorted),
  (Sorted = []
    -> R = bottom
    ; (Sorted = [Only]
      -> R = Only
       ; R = one_of(P))).% Liste

dom_intersect1(List1,List2,Res) :-
    (is_list(List1); is_list(List2)), !,
    g(List1,List2,Res).

dom_intersect1(X,Y,A) :-
    (spec_indirection(X,IndX) -> true ; IndX = X),
    (spec_indirection(Y,IndY) -> true ; IndY = Y),
    (X \= IndX; Y \= IndY),!,
    dom_intersect1(IndX,IndY,A).

% There is an one_of
dom_intersect1(one_of(List1),one_of(List2),one_of(Res)) :-
  !, dom_intersect_one_ofs(List1,List2,Res).
dom_intersect1(one_of(List),X,one_of(Res)) :-
  !,dom_intersect_one_of_with_elem(List,X,Res).
dom_intersect1(X,one_of(List),one_of(Res)) :-
  !, dom_intersect_one_of_with_elem(List,X,Res).

% And
dom_intersect1(and(List),X,Res) :- !,
  dom_intersect(List,L),
  dom_intersect1(L,X,Res).
dom_intersect1(X,and(List),Res) :- !,
    dom_intersect(List,L),
    dom_intersect1(L,X,Res).


% Atomic
dom_intersect1(X,X,X) :- !.

dom_intersect1(X,any,X) :- !.
dom_intersect1(any,X,X) :- !.

dom_intersect1(X,Y,X) :- dom_super(X,Y), !.
dom_intersect1(Y,X,X) :- dom_super(X,Y), !.

dom_intersect1(X,Y,X) :-
  dom_super(X,ParentX),
  dom_intersect1(ParentX,Y,ParentX), !.
dom_intersect1(Y,X,X) :-
  dom_super(X,ParentX),
  dom_intersect1(ParentX,Y,ParentX), !.



dom_intersect_one_ofs([],_,[]) :- !.
dom_intersect_one_ofs(_,[],[]) :- !.
dom_intersect_one_ofs([Head|Tail],List2,Result) :-
  dom_intersect_one_of_with_elem(List2,Head,List2IntersectHead),
  dom_intersect_one_ofs(Tail,List2,List2IntersectTail),
  append(List2IntersectHead,List2IntersectTail,Result).

dom_intersect_one_of_with_elem([],_,[]) :- !.
dom_intersect_one_of_with_elem([H|T],X,Res) :-
  (dom_intersect1(H,X,HeadIntersect)
    -> Res = [HeadIntersect|TailIntersect]
    ;  Res = TailIntersect),
  dom_intersect_one_of_with_elem(T,X,TailIntersect).



dom_intersect([X],X) :- !.
dom_intersect([X,Y|T],Res) :- !,
  dom_intersect(X,Y,A),
  dom_intersect([A|T],Res).

dom_intersect1_list([],[],[]) :- !.
dom_intersect1_list([X|Xs],[Y|Ys],[R|Rs]) :-
  dom_intersect1(X,Y,R),
  dom_intersect1_list(Xs,Ys,Rs).
