my_last([H],H) :- !.
my_last([_|T],Res) :-
    my_last(T,Res).

last_but_one([X,_],X) :- !.
last_but_one([_,Y|T],Res) :-
    last_but_one([Y|T],Res).

k_th(0,[Elem|_],Elem) :- !.
k_th(K,[_|L],Elem) :-
    KK is K-1,
    k_th(KK,L,Elem).


my_length([],0) :- !.
my_length([_|L],K) :-
    my_length(L,N),
    K is N+1.

reverse(L,Reverse) :-
    reverse(L,[],Reverse).

reverse([],Res,Res) :- !.
reverse([H|T],Acc,Res) :-
    reverse(T,[H|Acc],Res).

palindrom(L) :-
    reverse(L,L).

my_flatten([],[]) :- !.
my_flatten([H|T],Res) :-
    is_list(H),!,
    my_flatten(H,NH),
    append(NH,T,NT),
    my_flatten(NT,Res).
my_flatten([H|T],[H|Res]) :-
    my_flatten(T,Res).

compress([],[]) :- !.
compress([X],[X]) :- !.
compress([X,X|T],S) :-
    !,
    compress([X|T],S).
compress([X,Y|T],[X|S]) :-
    compress([Y|T],S).


% trees

pre_order(empty,[]) :- !.
pre_order(node(Left,Parent,Right),[Parent|Res]) :-
    pre_order(Left,OrderLeft),
    pre_order(Right,OrderRight),
    append(OrderLeft,OrderRight,Res).

in_order(empty,[]) :- !.
in_order(node(Left,Parent,Right),Res) :-
    in_order(Left,OrderLeft),
    in_order(Right,OrderRight),
    append(OrderLeft,[Parent|OrderRight],Res).

post_order(empty,[]) :- !.
post_order(node(Left,Parent,Right),Res) :-
    post_order(Left,OrderLeft),
    post_order(Right,OrderRight),
    append(OrderLeft,OrderRight,T),
    append(T,Parent,Res).

% Binary Search Trees
insertion(empty,Elem,node(empty,Elem,empty)) :- !.
insertion(node(Left,Root,Right),Elem,node(NewLeft,Root,Right)) :-
    Elem < Root, !,
    insertion(Left,Elem,NewLeft).
insertion(node(Left,Root,Right),Elem,node(Left,Root,NewRight)) :-
    Elem > Root, !,
    insertion(Right,Elem,NewRight).
insertion(_,_,_) :-
    fail.

search(node(_,Elem,_),Elem) :- !.
search(node(Left,Root,_),Elem) :-
    Elem < Root,!,
    search(Left,Elem).
search(node(_,Root,Right),Elem) :-
    Elem > Root, !,
    search(Right,Elem).

min(node(empty,Min,_),Min) :- !.
min(node(Left,_,_),Min) :-
    min(Left,Min).

max(node(_,Max,empty),Max) :- !.
max(node(_,_,Right),Max) :-
    max(Right,Max).

delete_node(node(Left,R,empty),R,Left) :- !.
delete_node(node(empty,R,Right),R,Right) :- !.
delete_node(node(empty,R,empty),R,empty) :- !.
delete_node(node(Left,Root,Right),Elem,node(NewLeft,Root,Right)) :-
    Elem < Root,!,
    delete_node(Left,Elem,NewLeft).
delete_node(node(Left,Root,Right),Elem,node(Left,Root,NewRight)) :-
    Elem > Root,!,
    delete_node(Right,Elem,NewRight).
delete_node(node(Left,Root,Right),Root,node(NewLeft,MaxLeft,Right)) :-
    max(Left,MaxLeft),
    delete_node(Left,MaxLeft,NewLeft).


mirror(empty,empty) :- !.
mirror(node(LA,Root,RA),node(LB,Root,RB)) :-
    mirror(LA,RB),
    mirror(RA,LB).

symmetric(empty) :- !.
symmetric(node(Left,_,Right)) :-
    mirror(Left,Right).

count_leaves(empty,0) :- !.
count_leaves(node(empty,_,empty),1) :- !.
count_leaves(node(Left,_,Right),Res) :-
    count_leaves(Left,CL),
    count_leaves(Right,CR),
    Res is CL + CR.


