:- module(strength_reduction,[reduction/2]).
:- use_module(logger,[log/4,log/5]).
:- use_module(library(plunit)).

reduction([],[]) :- !.
reduction([F|Old_Ast],[H|New_Ast]) :-
    reduction(F,H),
    reduction(Old_Ast,New_Ast).
 
% Reduziere rechte Seite 
reduction(def(Line,Var,Exp),def(Line,Var,Red)) :- !,
	reduce_expr(Exp,Red,Line).

% Reduziere den auszugebenden Ausdruck
reduction(print(Line,Expr),print(Line,Red)) :- !,
	reduce_expr(Expr,Red,Line).

% Reduziere die Ausdrücke im Header,
% den Then- und den Else-Block
reduction(if(Line,pred(Op,Expr1,Expr2),Then,Else),if(Line,pred(Op,Red1,Red2),Red_Then,Red_Else)) :- !,
	reduce_expr(Expr1, Red1,Line),
	reduce_expr(Expr2, Red2,Line),
	reduction(Then,Red_Then),
	reduction(Else,Red_Else).

% Reduziere die Ausdrücke im Header und im Block
reduction(while(Line,pred(Op,Exp1,Exp2),Block),while(Line,pred(Op,R1,R2),RB)) :- !,
	reduce_expr(Exp1,R1,Line),
	reduce_expr(Exp2,R2,Line),
	reduction(Block,RB).

reduction(for(Line,id(X),From,To,Block),for(Line,id(X),RF,RT,RB)) :- !,
	reduce_expr(From,RF,Line),
	reduce_expr(To,RT,Line),
	reduction(Block,RB).
	
reduction(for(Line,def(Line,Var,Expr1), pred(Op,Expr2,Expr3), def(Line,Var,Change),Block),for(Line,def(Line,Var,RExpr1), pred(Op,RExpr2,RExpr3), def(Line,Var,RChange),RBlock)) :- !,
	reduce_expr(Expr1,RExpr1,Line),
	reduce_expr(Expr2,RExpr2,Line),
	reduce_expr(Expr3,RExpr3,Line),
	reduce_expr(Change,RChange,Line),
	reduction(Block,RBlock).
	
reduction(skip(A),skip(A)).




% B*2 = B+B
reduce_expr(expr(*,B,cst(2)),Res,Line) :- !,
    reduce_expr(B,RB,Line),
    Res = expr(+,RB,RB).
    
% 2*B = B+B    
reduce_expr(expr(*,cst(2),B),Res,Line) :- !,
    reduce_expr(B,RB,Line),
    Res = expr(+,RB,RB).

% B * 2^X = B << X
% B / 2^X = B >> X
reduce_expr(expr(Op1,B,cst(C)),expr(Op2,B,cst(Exp)),Line) :-
	op_map(Op1,Op2),
    power_of_two(C,Exp), !,
    reduce_expr(B,RB,Line),
    log("reduced %t to %t",[expr(Op1,RB,cst(C)),expr(Op2,RB,cst(Exp))],info,strength_reduction,Line).
  
% 2^X * B = B * 2^X = B << X  
reduce_expr(expr(*,cst(C),B),expr(Op2,B,cst(Exp)),Line) :-
	op_map(*,Op2),
    power_of_two(C,Exp), !,
    reduce_expr(B,RB,Line),
	log("reduced %t to %t",[expr(*,RB,cst(C)),expr(Op2,RB,cst(Exp))],info,strength_reduction,Line).
    
% (-B)**2 = B*B
reduce_expr(expr(**,neg(B),cst(2)),Res,Line) :- 
    reduce_expr(expr(*,B,B),Res,Line).

% (-B)**2 = B*B
reduce_expr(expr(**,cst(B),cst(2)),Res,Line) :-
    B < 0,
    C is -B,!,
    reduce_expr(expr(*,cst(C),cst(C)),Res,Line).  
% A** 2 = A*A
reduce_expr(expr(**,A,cst(2)),Res,Line) :- !,
    reduce_expr(expr(*,A,A),Res,Line).
    
% (-A) ** Gerade = A ** Gerade
reduce_expr(expr(**,neg(B),cst(X)),Res,Line) :-
    A is lsb(X),A \= 0,!, % X is gerade
    reduce_expr(expr(**,B,cst(X)),Res,Line).

% (-A) ** Gerade = A ** Gerade
reduce_expr(expr(**,cst(B),cst(X)),Res,Line) :-
    B < 0,
    C is -B,
    A is lsb(X),A \= 0,!, % X is gerade
    reduce_expr(expr(**,cst(C),cst(X)),Res,Line).
	

    
reduce_expr(expr(Op,A,B),Res,Line) :- 
	reduce_expr(A,RA,Line),
	reduce_expr(B,RB,Line),
    (A \= RA; B \= RB),!,
    reduce_expr(expr(Op,RA,RB),Res,Line).
	
reduce_expr(A,A,_Line).


op_map(*,<<).
op_map(/,>>).

% Wird nicht mehr benutzt, da Ausdrücke zu komplex wurden
diff_of_power_of_twos(N) :-
    N >= 0,
	Ones is popcount(N),
	M is msb(N),
	L is lsb(N),
	Ones is M-L+1. % Number is difference of two power of twos (sequence of ones, then sequence of zeros)
    

power_of_two(N,Exp) :-
    N >= 0,
	1 is popcount(N),
	Exp is msb(N).

:- begin_tests(strength_reduction).
test(pow2) :-
    power_of_two(32,5),
    power_of_two(64,6).
test(not_pow2,[fail]) :-
    power_of_two(15,_).

test(div) :-
    reduce_expr(expr(/, id(X), cst(16)),expr(>>, id(X), cst(4)),1).
 
test(mul_pow2) :-
    reduce_expr(expr(*, id(X), cst(64)),expr(<<, id(X), cst(6)),1).
    
test(powEven) :-
    reduce_expr(expr(**,neg(id(X)),cst(4)),expr(**,id(X),cst(4)),1).
   
test(pow2) :-
    reduce_expr(expr(**,cst(-8),cst(2)),expr(*,cst(8),cst(8)),-1).

test(mul_other) :-
    A = expr(*, cst(3), cst(2)),
    B = expr(+, cst(3),cst(3)),
    reduce_expr(A,B,1).

:- end_tests(strength_reduction).

