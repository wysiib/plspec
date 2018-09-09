:- module(null_pos_neg, [alpha/2,
                         abs_expr/5,
                         abs_pred/6,
                         abs_not/2,
                         abs_neg/2,
                         lub/3,
                         undef/1]).
                         
:- use_module(logger,[log/4,log/5]).


% undefiniertes Element
undef(bot) :- !.

% abstrakte Elemente für integer
% null, pos, neg, not_null, bot, top
% bot < alles, alles < top
% pos < not_null, neg < not_null

abs_int(pos).
abs_int(neg).
abs_int(not_null).
abs_int(null).
abs_int(top).

% abstrakte Elemente für boolean
% bot, true, false, maybe
% bot < alles, alles < maybe

% alpha: abstrahiere konkrete werte
alpha(0,null).
alpha(Pos,pos) :-
  Pos > 0.
alpha(Neg,neg) :-
  Neg < 0.

% Abstrakte Expressions
% abs_expr(Op,ValA,ValB,Val,Line)
% ValA Op ValB = Val in line Line
abs_expr(+,pos,pos,pos,_Line).
abs_expr(+,pos,null,pos,_Line).
abs_expr(+,pos,neg,top,_Line).
abs_expr(+,pos,not_null,top,_Line).
abs_expr(+,pos,top,top,_Line).

abs_expr(+,null,X,X,_Line) :- abs_int(X).

abs_expr(+,neg,null,neg,_Line).
abs_expr(+,neg,neg,neg,_Line).
abs_expr(+,neg,pos,top,_Line).
abs_expr(+,neg,not_null,top,_Line).
abs_expr(+,neg,top,top,_Line).

abs_expr(+,not_null,not_null,top,_Line).
abs_expr(+,not_null,null,not_null,_Line).
abs_expr(+,not_null,neg,top,_Line).
abs_expr(+,not_null,pos,top,_Line).
abs_expr(+,not_null,top,top,_Line).

abs_expr(+,top,X,top,_Line) :- abs_int(X).


abs_expr(-,X,null,X,_Line) :- abs_int(X).
abs_expr(-,null,neg,pos,_Line).
abs_expr(-,null,pos,neg,_Line).
abs_expr(-,null,not_null,not_null,_Line).
abs_expr(-,null,top,top,_Line).
abs_expr(-,top,X,top,_Line) :- abs_int(X), X\=null.
abs_expr(-,X,top,top,_Line) :- abs_int(X), X\=null.
abs_expr(-,not_null,X,top,_Line) :- X = pos; X=neg; X=not_null.
abs_expr(-,pos,pos,top,_Line).
abs_expr(-,pos,neg,pos,_Line).
abs_expr(-,pos,null,pos,_Line).
abs_expr(-,pos,not_null,top,_Line).

abs_expr(-,neg,pos,neg,_Line).
abs_expr(-,neg,neg,top,_Line).
abs_expr(-,neg,null,neg,_Line).
abs_expr(-,neg,not_null,top,_Line).

abs_expr(-,null,pos,neg,_Line).
abs_expr(-,null,neg,pos,_Line).
abs_expr(-,null,null,null,_Line).
abs_expr(-,null,not_null,not_null,_Line).

abs_expr(-,not_null,pos,top,_Line).
abs_expr(-,not_null,neg,top,_Line).
abs_expr(-,not_null,not_null,top,_Line).
abs_expr(-,not_null,null,not_null,_Line).


abs_expr(*,pos,pos,pos,_Line).
abs_expr(*,pos,neg,neg,_Line).
abs_expr(*,pos,not_null,not_null,_Line).
abs_expr(*,pos,null,null,_Line).
abs_expr(*,pos,top,top,_Line).

abs_expr(*,neg,pos,neg,_Line).
abs_expr(*,neg,neg,pos,_Line).
abs_expr(*,neg,not_null,not_null,_Line).
abs_expr(*,neg,null,null,_Line).
abs_expr(*,neg,top,top,_Line).

abs_expr(*,null,X,null,_Line) :- abs_int(X).
abs_expr(*,top,X,top,_Line) :- abs_int(X), X \= null.
abs_expr(*,top,null,null,_Line).

abs_expr(*,not_null,pos,not_null,_Line).
abs_expr(*,not_null,neg,not_null,_Line).
abs_expr(*,not_null,not_null,not_null,_Line).
abs_expr(*,not_null,null,null,_Line).
abs_expr(*,not_null,top,top,_Line).


abs_expr(/,pos,pos,pos,_Line).
abs_expr(/,pos,neg,neg,_Line).
abs_expr(/,pos,not_null,not_null,_Line).
abs_expr(/,pos,null,bot,Line) :- !, log("Divided by zero",error,domain,Line).
abs_expr(/,pos,top,top,Line) :- !, log("Possible divided by zero",warning,domain,Line).

abs_expr(/,neg,pos,neg,_Line).
abs_expr(/,neg,neg,pos,_Line).
abs_expr(/,neg,not_null,not_null,_Line).
abs_expr(/,neg,null,bot,Line) :- !, log("Divided by zero",error,domain,Line).
abs_expr(/,neg,top,top,Line) :- !, log("Possible divided by zero",warning,domain,Line).

abs_expr(/,not_null,pos,not_null,_Line).
abs_expr(/,not_null,neg,not_null,_Line).
abs_expr(/,not_null,not_null,not_null,_Line).
abs_expr(/,not_null,null,bot,Line) :- !, log("Divided by zero",error,domain,Line).
abs_expr(/,not_null,top,top,Line) :- !, log("Possible divided by zero",warning,domain,Line).

abs_expr(/,null,pos,null,_Line).
abs_expr(/,null,neg,null,_Line).
abs_expr(/,null,not_null,null,_Line).
abs_expr(/,null,null,null,Line) :- !, log("Divided by zero",error,domain,Line).
abs_expr(/,null,top,null,_Line).

abs_expr(/,top,pos,top,_Line).
abs_expr(/,top,neg,top,_Line).
abs_expr(/,top,null,bot,Line) :- !, log("Divided by zero",error,domain,Line).
abs_expr(/,top,not_null,top,_Line).
abs_expr(/,top,top,top,Line) :- !, log("Possible divided by zero",warning,domain,Line).


abs_expr(<<,pos,pos,pos,_Line).
abs_expr(<<,neg,pos,neg,_Line).
abs_expr(<<,not_null,pos,not_null,_Line).
abs_expr(<<,null,pos,null,_Line).
abs_expr(<<,top,pos,top,_Line).

abs_expr(<<,neg,neg,neg,_Line).
abs_expr(<<,null,neg,null,_Line).
abs_expr(<<,pos,neg,top,_Line).
abs_expr(<<,not_null,neg,top,_Line).
abs_expr(<<,top,neg,top,_Line).

abs_expr(<<,X,not_null,top,_Line) :- abs_int(X).
abs_expr(<<,X,top,top,_Line) :- abs_int(X).
abs_expr(<<,X,null,X,_Line) :- abs_int(X).

abs_expr(>>,pos,pos,top,_Line).
abs_expr(>>,neg,pos,neg,_Line).
abs_expr(>>,not_null,pos,top,_Line).
abs_expr(>>,null,pos,null,_Line).
abs_expr(>>,top,pos,top,_Line).

abs_expr(>>,pos,neg,pos,_Line).
abs_expr(>>,neg,neg,neg,_Line).
abs_expr(>>,not_null,neg,not_null,_Line).
abs_expr(>>,null,neg,null,_Line).
abs_expr(>>,top,neg,top,_Line).

abs_expr(>>,X,not_null,top,_Line) :- abs_int(X).
abs_expr(>>,X,top,top,_Line) :- abs_int(X).
abs_expr(>>,X,null,X,_Line) :- abs_int(X).


abs_expr(mod,X,null,bot,Line) :-  abs_int(X),!, log("Divided by zero",error,domain,Line).
abs_expr(mod,X,top,top,Line) :- abs_int(X),!,log("Possible divided by zero",warning,domain,Line).
abs_expr(mod,null,X,null,_Line) :- abs_int(X).

abs_expr(mod,X,Y,null,_Line) :- abs_int(X), X \= null, abs_int(Y).


abs_expr(**,X,null,pos,_Line) :- abs_int(X).

abs_expr(**,pos,X,pos,_Line) :- abs_int(X), X\=null.

abs_expr(**,neg,X,not_null,_Line) :- abs_int(X), X\=null.

abs_expr(**,not_null,X,not_null,_Line) :- abs_int(X), X\=null.

abs_expr(**,top,X,top,_Line) :- abs_int(X), X\=null.

abs_expr(**,null,pos,null,_Line).
abs_expr(**,null,neg,bot,Line) :- log("Divided by zero",error,domain,Line).
abs_expr(**,null,not_null,null,Line) :- !,log("Possible divided by zero",warning,domain,Line).
abs_expr(**,null,top,null,Line) :- !,log("Possible divided by zero",warning,domain,Line).



abs_neg(pos,neg).
abs_neg(neg,pos).
abs_neg(null,null).
abs_neg(top,top).
abs_neg(not_null,not_null).


% Abstrakte Prädikate
% abs_expr(Op,ValA,ValB,Val,NewValA,NewValB)
% ValA Op ValB = Val

%% <
abs_pred(<,top,top,true,top,top).
abs_pred(<,top,pos,true,top,pos).
abs_pred(<,top,neg,true,neg,neg).
abs_pred(<,top,null,true,neg,null).
abs_pred(<,top,not_null,true,top,not_null).

abs_pred(<,top,top,false,top,top).
abs_pred(<,top,pos,false,pos,pos).
abs_pred(<,top,neg,false,top,neg).
abs_pred(<,top,null,false,top,null).
abs_pred(<,top,not_null,false,top,not_null).

abs_pred(<,pos,top,true,pos,pos).
abs_pred(<,pos,pos,true,pos,pos).
abs_pred(<,pos,not_null,true,pos,pos).

abs_pred(<,pos,top,false,pos,top).
abs_pred(<,pos,pos,false,pos,pos).
abs_pred(<,pos,neg,false,pos,neg).
abs_pred(<,pos,null,false,pos,null).
abs_pred(<,pos,not_null,false,pos,not_null).

abs_pred(<,neg,neg,true,neg,neg).
abs_pred(<,neg,pos,true,neg,pos).
abs_pred(<,neg,null,true,neg,null).
abs_pred(<,neg,not_null,true,neg,not_null).
abs_pred(<,neg,top,true,neg,top).

abs_pred(<,neg,neg,false,neg,neg).
abs_pred(<,neg,not_null,false,neg,not_null).
abs_pred(<,neg,top,false,neg,top).

abs_pred(<,not_null,pos,true,not_null,pos).
abs_pred(<,not_null,neg,true,neg,neg).
abs_pred(<,not_null,top,true,not_null,top).
abs_pred(<,not_null,null,true,neg,null).
abs_pred(<,not_null,not_null,true,not_null,not_null).

abs_pred(<,not_null,pos,false,pos,pos).
abs_pred(<,not_null,neg,false,not_null,neg).
abs_pred(<,not_null,null,false,pos,null).
abs_pred(<,not_null,not_null,false,not_null,not_null).
abs_pred(<,not_null,top,false,not_null,top).

abs_pred(<,null,pos,true,null,pos).
abs_pred(<,null,not_null,true,null,pos).
abs_pred(<,null,top,true,null,pos).

abs_pred(<,null,neg,false,null,neg).
abs_pred(<,null,not_null,false,null,neg).
abs_pred(<,null,null,false,null,null).
abs_pred(<,null,top,false,null,top).

% >
abs_pred(>,top,top,true,top,top).
abs_pred(>,top,pos,true,pos,pos).
abs_pred(>,top,neg,true,top,neg).
abs_pred(>,top,null,true,pos,null).
abs_pred(>,top,not_null,true,top,not_null).

abs_pred(>,top,top,false,top,top).
abs_pred(>,top,pos,false,top,pos).
abs_pred(>,top,neg,false,neg,neg).
abs_pred(>,top,null,false,top,null).
abs_pred(>,top,not_null,false,top,not_null).

abs_pred(>,pos,top,true,pos,top).
abs_pred(>,pos,pos,true,pos,pos).
abs_pred(>,pos,not_null,true,pos,not_null).
abs_pred(>,pos,null,true,pos,null).
abs_pred(>,pos,top,true,pos,top).

abs_pred(>,pos,top,false,pos,pos).
abs_pred(>,pos,pos,false,pos,pos).
abs_pred(>,pos,not_null,false,pos,pos).

abs_pred(>,neg,neg,true,neg,neg).
abs_pred(>,neg,not_null,true,neg,neg).
abs_pred(>,neg,top,true,neg,neg).

abs_pred(>,neg,neg,false,neg,neg).
abs_pred(>,neg,not_null,false,neg,not_null).
abs_pred(>,neg,top,false,neg,top).
abs_pred(>,neg,null,false,neg,null).
abs_pred(>,neg,pos,false,neg,pos).

abs_pred(>,not_null,pos,true,pos,pos).
abs_pred(>,not_null,neg,true,not_null,neg).
abs_pred(>,not_null,top,true,not_null,top).
abs_pred(>,not_null,null,true,top,null).
abs_pred(>,not_null,not_null,true,not_null,not_null).

abs_pred(>,not_null,pos,false,not_null,pos).
abs_pred(>,not_null,neg,false,neg,neg).
abs_pred(>,not_null,null,false,neg,null).
abs_pred(>,not_null,not_null,false,not_null,not_null).
abs_pred(>,not_null,top,false,not_null,top).

abs_pred(>,null,neg,true,null,neg).
abs_pred(>,null,not_null,true,null,neg).
abs_pred(>,null,top,true,null,neg).

abs_pred(>,null,pos,false,null,pos).
abs_pred(>,null,not_null,false,null,pos).
abs_pred(>,null,null,false,null,null).
abs_pred(>,null,top,false,null,top).

% =\=

abs_pred(=\=,pos,null,true,pos,null).
abs_pred(=\=,pos,neg,true,pos,neg).
abs_pred(=\=,pos,pos,true,pos,pos).
abs_pred(=\=,pos,not_null,true,pos,not_null).
abs_pred(=\=,pos,top,true,pos,top).

abs_pred(=\=,neg,null,true,neg,null).
abs_pred(=\=,neg,neg,true,neg,neg).
abs_pred(=\=,neg,pos,true,neg,pos).
abs_pred(=\=,neg,not_null,true,neg,not_null).
abs_pred(=\=,neg,top,true,neg,top).

abs_pred(=\=,top,null,true,not_null,null).
abs_pred(=\=,top,neg,true,top,neg).
abs_pred(=\=,top,pos,true,top,pos).
abs_pred(=\=,top,not_null,true,top,not_null).
abs_pred(=\=,top,top,true,top,top).

abs_pred(=\=,not_null,null,true,not_null,null).
abs_pred(=\=,not_null,neg,true,not_null,neg).
abs_pred(=\=,not_null,pos,true,not_null,pos).
abs_pred(=\=,not_null,not_null,true,not_null,not_null).
abs_pred(=\=,not_null,top,true,not_null,top).

abs_pred(=\=,X,Y,false,A,B) :-
    abs_pred(==,X,Y,true,A,B).

abs_pred(==,X,Y,false,A,B) :-
    abs_pred(=\=,X,Y,true,A,B).
    
    
abs_pred(==,pos,pos,true,pos,pos).
abs_pred(==,pos,top,true,pos,pos).
abs_pred(==,pos,not_null,true,pos,pos).

abs_pred(==,top,null,true,null,null).
abs_pred(==,top,not_null,true,not_null,not_null).
abs_pred(==,top,pos,true,pos,pos).
abs_pred(==,top,neg,true,neg,neg).

abs_pred(==,neg,not_null,true,neg,neg).
abs_pred(==,neg,top,true,neg,neg).
abs_pred(==,neg,neg,true,neg,neg).

abs_pred(==,null,top,true,null,null).
abs_pred(==,null,null,true,null,null).

abs_pred(==,not_null,top,true,not_null,not_null).
abs_pred(==,not_null,pos,true,pos,pos).
abs_pred(==,not_null,neg,true,neg,neg).


% Abstrakte Negation
abs_not(true,false).
abs_not(false,true).

% Least upper Bound: Vereinigung von Werten
lub(top,_,top).
lub(_,top,top).
lub(X,bot,X).
lub(bot,X,X).
lub(X,X,X).
lub(pos,neg,not_null).
lub(neg,pos,not_null).
lub(not_null,neg,not_null).
lub(not_null,pos,not_null).
lub(neg,not_null,not_null).
lub(pos,not_null,not_null).
lub(null,pos,top).
lub(pos,null,top).
lub(null,neg,top).
lub(neg,null,top).

find_missing_pred(Op,A,B) :-
    L = [pos,neg,null,not_null,top],
    Ops = [/,*,+,-,mod,<<,>>],
    member(A,L),
    member(B,L),
    member(Op,Ops),
    not(abs_expr(Op,A,B,_,-1)).

:- begin_tests(null_pos_neg).

test(missing_preds) :-
    not(find_missing_pred(_,_,_)).



:- end_tests(null_pos_neg).
