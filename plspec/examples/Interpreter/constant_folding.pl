:- module(constant_folding,[folding/3]).
:- use_module(logger,[log/4, log/5]).
:- use_module(library(plunit)).

folding(A,B,Options) :-
  (option(fp(X),Options) -> assert(fp(X));assert(fp(false))), % Falten in Print-Ausdrücken
  empty_assoc(State), % Führe einen State mit, der die aktuellen Werte der Variablen enthält
  put_assoc(marked,State,[],StateT), % Markierte Variable werden nicht zum Falten verwendet
  folding(A,StateT,_,B,false),
  retractall(fp(_)).

% Durch den AST durchgehen und alle vorhandenen Expressions falten
folding([],A,A,[],_) :- !.
folding([F|Old_Ast],StateIn,StateOut,[H|New_Ast],InLoop) :-
  folding(F,StateIn,StateA,H,InLoop),
  folding(Old_Ast,StateA,StateOut,New_Ast,InLoop).

% Falten rechte Seite Definition
folding(def(Line,id(X),Expr),StateIn,StateOut,def(Line,id(X),Folded_Expr),true) :- 
  expr_contains_var(Expr,id(X)),!, % Enthält Definition die Variable selber?
  get_assoc(marked,StateIn,Marked),
  (member(X,Marked) 
  -> StateT = StateIn; 
  put_assoc(marked,StateIn,[X|Marked],StateT)), % falls X noch nicht markiert ist, markiere es
  fold_expr(Expr,StateT,Folded_Expr,Line),
  put_assoc(X,StateT,Folded_Expr,StateOut).
  
folding(def(Line,id(X),Expr),StateIn,StateOut,def(Line,id(X),Folded_Expr),_) :- 
  get_assoc(marked,StateIn,Marked),
  not(member(X,Marked)),!,
  fold_expr(Expr,StateIn,Folded_Expr,Line),
  put_assoc(X,StateIn,Folded_Expr,StateOut).

folding(def(Line,id(X),Expr),StateIn,StateOut,def(Line,id(X),Folded_Expr),false) :- 
  get_assoc(marked,StateIn,Marked),
  select(X,Marked,NewMarked), % Variable ist markiert
  not(expr_contains_var(Expr,id(X))), %Variable kommt nicht mehr auf der rechten Seite vor, und darf daher wieder zum Falten benutzt werden
  put_assoc(marked,StateIn,NewMarked,StateT),
  fold_expr(Expr,StateT,Folded_Expr,Line),
  put_assoc(X,StateT,Folded_Expr,StateOut).

  
% Konstantenfaltung im If-Pred, im Then- und im Else-Block
folding(if(Line,Pred,Then,skip(A)),StateIn,StateIn,if(Line,FPred,FThen,skip(A)),InLoop) :- !,
  fold_pred(Pred,StateIn,FPred,Line),
  folding(Then,StateIn,_StateThen,FThen,InLoop).
folding(if(Line,Pred,Then,Else),StateIn,StateOut,if(Line,FPred,FThen,FElse),InLoop) :-
  fold_pred(Pred,StateIn,FPred,Line),
  folding(Then,StateIn,StateThen,FThen,InLoop),
  folding(Else,StateIn,StateElse,FElse,InLoop),
  merge_states(StateThen,StateElse,StateOut).

folding(skip(A),_,_,skip(A),_).
% In einer Schleife wollen wir "From" und "To" und alle Ausdrücke im Block falten.
% Die Zählvariable verändert sich jedoch ständig und daher darf der aktuelle Wert
% nicht zum Falten benutzt werden.
folding(for(Line,id(X),From,To,Block),StateIn,StateOut,for(Line,id(X),FFrom,FTo,FBlock),_) :-
  get_assoc(marked,StateIn,Marked),
  % falls X noch nicht markiert ist, markiere es
  (member(X,Marked) -> StateT = StateIn; put_assoc(marked,StateIn,[X|Marked],StateT)), 
  fold_expr(From,StateT,FFrom,Line),
  fold_expr(To,StateT,FTo,Line),
  folding(Block,StateT,StateOut,FBlock,true).
  
folding(for(Line,def(Line,id(X),Expr), End, def(Line,id(X),Change),Block),StateIn,StateOut,Res,_) :-
  get_assoc(marked,StateIn,Marked),
  (member(X,Marked) -> StateT = StateIn; put_assoc(marked,StateIn,[X|Marked],StateT)),
  fold_expr(Expr,StateT,FExpr,Line),
  fold_pred(End,StateT,FEnd,Line),
  fold_expr(Change,StateT,FChange,Line),
  folding(Block,StateT,StateOut,FBlock,true),
  Res = for(Line,def(Line,id(X),FExpr), FEnd, def(Line,id(X),FChange),FBlock).

  
folding(print(Line,Expr),StateIn,StateIn,print(Line,Res),_) :-
  (fp(true) -> % Falte hier nur, wenn fp auf true gesetzt ist
	fold_expr(Expr,StateIn,Res,Line),
	(Expr = Res -> 
	  true;
	  log("Folded Constants in print(%t) to print(%t).",[Expr,Res],info,constant_folding,Line)
	);
	Res = Expr
  ).


% Auch hier Zählvariable nicht zum Falten verwenden
folding(while(Line,pred(Op,id(X),Exp2),Block),StateIn,StateOut,Res,_) :-
  get_assoc(marked,StateIn,Marked),
  (member(X,Marked) -> StateT = StateIn; put_assoc(marked,StateIn,[X|Marked],StateT)),
  fold_expr(id(X),StateT,FExp1,Line),
  fold_expr(Exp2,StateT,FExp2,Line),
  folding(Block,StateT,StateOut,FBlock,true),
  Res = while(Line,pred(Op,FExp1,FExp2),FBlock).
  
expr_contains_var(id(X),id(X)).
expr_contains_var(neg(E),id(X)) :-
  expr_contains_var(E,id(X)).
expr_contains_var(expr(_,Expr1,Expr2),id(X)) :-
  expr_contains_var(Expr1,id(X));
  expr_contains_var(Expr2,id(X)).
  
% Falte einen Ausdruck, der nur aus Konstanten entsteht.
fold_expr(expr(Op,cst(A),cst(B)),_State,cst(C),Line) :- !,
  E = expr(Op,cst(A),cst(B)),
  Term =.. [Op,A,B],
  C is Term,
  log("%t folded to %t.",[E,cst(C)],info,constant_folding,Line).

% Falte Ausdrücke mit neg
% neg vor einer Konstanten kann als - in die Konstante reingezogen werden
fold_expr(neg(cst(X)),_State,cst(Y),Line) :- !,
  Y is -X,
  log("%t folded to %t.",[neg(cst(X)),cst(Y)],info,constant_folding,Line).

% ein doppeltes neg fällt weg 
fold_expr(neg(neg(Expr)),StateIn,Folded_Expr,Line) :- !,
  fold_expr(Expr,StateIn,Folded_Expr,Line).
  

% Steht neg vor einem anderen, bisher nicht behandeltem Ausdruck,
% falte diesen und wrappe ihn dann wieder in neg
fold_expr(neg(Expr),StateIn,Res,Line) :- 
  fold_expr(Expr,StateIn,Folded_Expr,Line),
  Expr \= Folded_Expr,!,
  fold_expr(neg(Folded_Expr),StateIn,Res,Line).

% Falte Variablen
fold_expr(id(X),StateIn,id(X),Line) :-
  get_assoc(X,StateIn,unknown), !, % Der Wert dieser Variable ist unbekannt, da sie in
					 % verschiedenen Branches unterschiedlich definiert wurde
  log("%t unknown value!",[X],info,constant_folding,Line).
fold_expr(id(X),StateIn,id(X),Line) :-
  get_assoc(X,StateIn,_), 
  get_assoc(marked,StateIn,Marked),
  member(X,Marked),!, % X ist eine Loop-Variable -> nicht falten
  log("%t is a loop variable!",[X],info,constant_folding,Line).
fold_expr(id(X),StateIn,Expr,Line) :-
  get_assoc(X,StateIn,Expr),!, %Ein Wert für X konnte gefunden werden
  log("for variable %t set in %t",[X,Expr],info,constant_folding,Line).

fold_expr(id(X),StateIn,id(X),Line) :-
  not(get_assoc(X,StateIn,_)), % Variable konnte nicht gefunden werden
  get_assoc(marked,StateIn,Marked), % ist aber markiert -> ist eine Schleifenkopf/Zählvariable
  member(X,Marked), !,
  log("%t is a loop variable!",[X],info,constant_folding,Line).
  

fold_expr(id(X),_StateIn,id(X),Line) :- !, %Variable konnte nicht gefunden werden -> Fehler
  log("Right-Hand Variable %t not yet defined",[X],error,constant_folding,Line).
  

  
% Keiner der oben behandelten Spezialfälle trifft zu
% bei expr(Op,A,B) falte also A zu FA und B zu FB
% Falls es bei einem Argument eine Veränderung gab,
% falte expr(Op,FA,FB).
fold_expr(expr(Op,A,B),State,Res,Line) :-
  fold_expr(A,State,FA,Line),
  fold_expr(B,State,FB,Line),
  (A \= FA; B \= FB),!,
  fold_expr(expr(Op,FA,FB),State,Res,Line).
  
% Es kann sein, dass das Falten von expr(Op,A,B) keine neuen Erkenntnise gebracht hat,
% weil zum Beispiel A eine unbekannte Variable ist, 
% Wenn es kein Ergebnis gab, wende Rechenregeln wie --(X)=X und A*B = B*A an:

% Ein neg bei * oder / kann nach vorne rausgezogen werden
fold_expr(expr(Op,A,neg(B)),State,Res,Line) :- 
  (Op = *; Op = /),!,
  fold_expr(neg(expr(Op,A,B)),State,Res,Line).

fold_expr(expr(Op,neg(A),B),State,Res,Line) :- 
  (Op = *; Op = /),!,
  fold_expr(neg(expr(Op,A,B)),State,Res,Line).
  
% -A+B = B-A
fold_expr(expr(+,neg(A),B),State,Res,Line) :- !,
  fold_expr(expr(-,B,A),State,Res,Line).  
  
% A+(-B) = A-B
fold_expr(expr(+,A,neg(B)),State,Res,Line) :- !,
  fold_expr(expr(-,A,B),State,Res,Line).

%-A-B = -(A+B)
fold_expr(expr(-,neg(A),B),State,Res,Line) :- !,
  fold_expr(neg(expr(+,A,B)),State,Res,Line).  
  
%A-(-B) = A+B
fold_expr(expr(-,A,neg(B)),State,Res,Line) :- !,
  fold_expr(expr(+,A,B),State,Res,Line).  


% Wenn in expr(Op,X,Y) das Falten von X und von Y keine Veränderung gebracht hat,
% (Bspl: expr(+,cst(5),expr(+,cst(5),id(y))), y unbekannt
% werden folgende Spezialfälle untersucht

% Das Falten der genauer spezifizierten Komponente hat also kein Ergebnis gebracht

% A+(B-C) = (A+B)-C = (A-C)+B
fold_expr(expr(+,A,expr(-,B,C)),State,Res,Line) :-
  AB = expr(+,A,B),
  fold_expr(AB,State,FAB,Line),
  fold_expr(C,State,FC,Line),
  (AB \= FAB ; C \= FC),!,
  fold_expr(expr(-,FAB,FC),State,Res,Line).
  
fold_expr(expr(+,A,expr(-,B,C)),State,Res,Line) :-
  AC = expr(-,A,C),
  fold_expr(AC,State,FAC,Line),
  fold_expr(B,State,FB,Line),
  (AC \= FAC; B \= FB),!,
  fold_expr(expr(+,FAC,FB),State,Res,Line).

% Andersherum
fold_expr(expr(+,expr(-,B,C),A),State,Res,Line) :- !,
  AC = expr(-,A,C),
  fold_expr(AC,State,FAC,Line), % Stelle die Bedingung von oben her
  fold_expr(expr(+,B,FAC),State,Res,Line).
  
% A - (B+C) = (A-B)-C = (A-C)-B
fold_expr(expr(-,A,expr(+,B,C)),State,Res,Line) :-
  AB = expr(-,A,B),
  fold_expr(AB,State,FAB,Line),
  fold_expr(C,State,FC,Line),
  (AB \= FAB ; C \= FC),!,
  fold_expr(expr(-,FAB,FC),State,Res,Line).
  
fold_expr(expr(-,A,expr(+,B,C)),State,Res,Line) :-
  AC = expr(-,A,C),
  fold_expr(AC,State,FAC,Line),
  fold_expr(B,State,FB,Line),
  (AC \= FAC; B \= FB),!,
  fold_expr(expr(-,FAC,FB),State,Res,Line).
  
% Andersherum
fold_expr(expr(-,expr(+,B,C),A),State,Res,Line) :- !,
  BA = expr(-,B,A),
  fold_expr(BA,State,FBA,Line),
  fold_expr(expr(+,C,FBA),State,Res,Line).
  
% A - (B-C) = (A-B)+C = (A+C)-B
fold_expr(expr(-,A,expr(-,B,C)),State,Res,Line) :-
  AB = expr(-,A,B),
  fold_expr(AB,State,FAB,Line),
  fold_expr(C,State,FC,Line),
	(AB \= FAB ; C \= FC),!,
  fold_expr(expr(+,FAB,FC),State,Res,Line).
  
fold_expr(expr(-,A,expr(-,B,C)),State,Res,Line) :-
  AC = expr(+,A,C),
  fold_expr(AC,State,FAC,Line),
  fold_expr(B,State,FB,Line),
  (AC \= FAC; B \= FB),!,
  fold_expr(expr(-,FAC,FB),State,Res,Line).	 
  
% Andersherum 
fold_expr(expr(-,expr(-,B,C),A),State,Res,Line) :- !,
  AC = expr(+,A,C),
  fold_expr(AC,State,FAC,Line),
  fold_expr(expr(-,B,FAC),State,Res,Line).
  
% Dasselbe gilt auch für * anstatt + und / anstatt -
% A*(B/C) = (A*B)/C = (A/C)*B
fold_expr(expr(*,A,expr(/,B,C)),State,Res,Line) :-
  AB = expr(*,A,B),
  fold_expr(AB,State,FAB,Line),
  fold_expr(C,State,FC,Line),
  (AB \= FAB ; C \= FC),!,
  fold_expr(expr(/,FAB,FC),State,Res,Line).
  
fold_expr(expr(*,A,expr(/,B,C)),State,Res,Line) :-
  AC = expr(/,A,C),
  fold_expr(AC,State,FAC,Line),
  fold_expr(B,State,FB,Line),
  (AC \= FAC; B \= FB),!,
  fold_expr(expr(*,FAC,FB),State,Res,Line).

fold_expr(expr(*,expr(/,B,C),A),State,Res,Line) :- !,
  AC = expr(/,A,C),
  fold_expr(AC,State,FAC,Line),
  fold_expr(expr(*,B,FAC),State,Res,Line).
  
% A / (B*C) = (A/B)/C = (A/C)/B
fold_expr(expr(/,A,expr(*,B,C)),State,Res,Line) :-
  AB = expr(/,A,B),
  fold_expr(AB,State,FAB,Line),
  fold_expr(C,State,FC,Line),
  (AB \= FAB ; C \= FC),!,
  fold_expr(expr(/,FAB,FC),State,Res,Line).
  
fold_expr(expr(/,A,expr(*,B,C)),State,Res,Line) :-
  AC = expr(/,A,C),
  fold_expr(AC,State,FAC,Line),
  fold_expr(B,State,FB,Line),
  (AC \= FAC; B \= FB),!,
  fold_expr(expr(/,FAC,FB),State,Res,Line).
  
fold_expr(expr(/,expr(*,B,C),A),State,Res,Line) :- !,
  AB = (expr(/,B,A),
  fold_expr(AB,State,FAB,Line),
  fold_expr(expr(*,C,FAB)),State,Res,Line).
  
% A / (B/C) = (A/B)*C = (A*C)/B
fold_expr(expr(/,A,expr(/,B,C)),State,Res,Line) :-
  AB = expr(/,A,B),
  fold_expr(AB,State,FAB,Line),
  fold_expr(C,State,FC,Line),
  (AB \= FAB ; C \= FC),!,
  fold_expr(expr(*,FAB,FC),State,Res,Line).
  
fold_expr(expr(/,A,expr(/,B,C)),State,Res,Line) :-
  AC = expr(*,A,C),
  fold_expr(AC,State,FAC,Line),
  fold_expr(B,State,FB,Line),
  (AC \= FAC; B\=FB),!,
  fold_expr(expr(/,FAC,FB),State,Res,Line).	 
  
fold_expr(expr(/,expr(/,B,C),A),State,Res,Line) :- !,
  AC = expr(*,A,C),
  fold_expr(AC,State,FAC,Line),
  fold_expr(expr(/,B,FAC),State,Res,Line).

% SHIFT 
fold_expr(expr(<<,A,neg(B)),State,Res,Line) :- !,
  fold_expr(expr(>>,A,B),State,Res,Line).
fold_expr(expr(>>,A,neg(B)),State,Res,Line) :- !,
  fold_expr(expr(<<,A,B),State,Res,Line).

fold_expr(expr(<<,A,cst(B)),State,Res,Line) :- 
  B < 0,
  C is -B,!,
  fold_expr(expr(>>,A,cst(C)),State,Res,Line).
fold_expr(expr(>>,A,cst(B)),State,Res,Line) :-	
  B < 0,
  C is -B,!,
  fold_expr(expr(<<,A,cst(C)),State,Res,Line).
  
fold_expr(expr(Op,expr(Op,A,cst(X)),cst(Y)),State,Res,Line) :-
  (Op = <<; Op = >>),
  (X >= 0, Y >= 0; X =< 0, Y =<0),!,
  Z is X+Y,
  fold_expr(expr(Op,A,cst(Z)),State,Res,Line).
  
fold_expr(expr(*,cst(A),expr(<<,B,cst(C))),State,Res,Line) :-
  C >= 0,
  Z= expr(<<,cst(A),cst(C)),
  fold_expr(Z,State,FZ,Line),
  fold_expr(B,State,FB,Line),
  (B \= FB; Z \= FZ),!,
  fold_expr(expr(*,FB,FZ),State,Res,Line).


% Keine weiteren Veränderungen bei Shift, da die Umformungen von den
% Vorzeichen abhängen
  
  
% Das Falten der inneren Ausdrücke hat nichts verändert

% Falls * oder +, können wir Assoziativität (+ Kommutativität) an

% Anstatt (A*B)*C, versuche (A*C)*B
fold_expr(expr(Op,expr(Op,A,B),C),State,Res,Line) :-
  (Op = *; Op = +),
  AC = expr(Op,A,C),
  fold_expr(AC,State,FAC,Line),
  fold_expr(B,State,FB,Line),
  (AC \= FAC; B \= FB),!,
  fold_expr(expr(Op,FAC,FB),State,Res,Line).
  
%Dann (B*C)*A  
fold_expr(expr(Op,expr(Op,A,B),C),State,Res,Line) :-
  (Op = *; Op = +),
  BC = expr(Op,B,C),
  fold_expr(A,State,FA,Line),
  fold_expr(BC,State,FBC,Line),
  (A \= FA; BC \= FBC),!,
  fold_expr(expr(Op,FA,FBC),State,Res,Line).
  
% Falls der Ausdruck die Form C*(A*B) hat -> tausche Argumente
fold_expr(expr(Op,C,expr(Op,A,B)),State,Res,Line) :-
  (Op = *; Op = +),!,
  fold_expr(expr(Op,expr(Op,A,B),C),State,Res,Line).
  
  
% Kein Spezialfall passte -> liefere den Ausdruck zurück
fold_expr(A,_,A,_Line).





% Falte ein logisches Prädikat, indem die Ausdrücke auf der rechten
% und linken Seite gefaltet werden
fold_pred(pred(Op,A,B),State,Res,Line) :-
  fold_expr(A,State,FA,Line),
  fold_expr(B,State,FB,Line),
  Res = pred(Op,FA,FB).

merge_states(State1,State2,StateOut) :-
  assoc_to_keys(State1,Keys),
  empty_assoc(CurrentState),
  merge_keys(Keys,State1,State2,CurrentState,StateOut).
  
merge_keys([],_,_,S,S) :- !.
merge_keys([Key|Keys],State1,State2,Current,Out) :-
  get_assoc(Key,State1,Val),
  get_assoc(Key,State2,Val),!,
  put_assoc(Key,Current,Val,NewState),
  merge_keys(Keys,State1,State2,NewState,Out).
merge_keys([Key|Keys],State1,State2,Current,Out) :-
  get_assoc(Key,State1,Val1),
  get_assoc(Key,State2,Val2),
  Val1 \= Val2,!,
  put_assoc(Key,Current,unknown,NewState),
  merge_keys(Keys,State1,State2,NewState,Out).
merge_keys([_|Keys],State1,State2,Current,Out) :-
  merge_keys(Keys,State1,State2,Current,Out).
  

:- begin_tests(constant_folding).

% Erzeuge einen Teststate, um dann das Falten zu testen
testState(TestState) :-
  empty_assoc(State),
  put_assoc(x,State,cst(6),State1), %x ist eine normale, zum Falten benutzbare Variable
  put_assoc(y,State1,unknown,State2), %y hat in if-branches unterschiedliche Werte bekommen
  put_assoc(marked,State2,[i,a],State3), %i ist eine Schleifenvariable
  put_assoc(a,State3,expr(+,id(a),cst(12)),State4), %a ist eine Variable, die in einer Schleife erhöht wird
  TestState = State4.

test(fold_expr_id, [condition(testState(TestState))]) :-
  fold_expr(id(x),TestState,cst(6),_),
  fold_expr(id(y),TestState,id(y),_),
  fold_expr(id(a),TestState,expr(+,id(a),cst(12)),_),
  fold_expr(id(i),TestState,id(i),_).
  
test(fold_expr_neg, [condition(testState(TestState))]) :-
  Expr = neg(neg(expr(*,neg(expr(+,id(x),cst(6))),expr(*,id(y),cst(5))))),	% -(-((-(x+6))*(y*5)))
  Expectation1 = expr(*,cst(-60),id(y)),% -(x+6)*(y*5) = (-12)*5*y = -60 *y
  Expectation2 = expr(*,id(y),cst(-60)),
  fold_expr(Expr,TestState,Res,_),
  (Res = Expectation1;Res = Expectation2).
  
test(fold_expr_commutativ1,[condition(testState(TestState))]) :-
  fold_expr(expr(*,cst(5),expr(*,id(y),cst(6))),TestState,Res,_),
  (Res = expr(*,cst(30),id(y)); Res = expr(*,id(y),cst(30))).
  
test(fold_expr_commutativ2,[condition(testState(TestState))]) :-
  fold_expr(expr(*,expr(*,id(y),cst(6)),cst(5)),TestState,Res,_),
  (Res = expr(*,cst(30),id(y)); Res = expr(*,id(y),cst(30))).	
  
test(fold_expr_commutativ3,[condition(testState(TestState))]) :-
  fold_expr(expr(*,expr(*,id(y),cst(6)),expr(*,id(y),cst(5))),TestState,expr(*,A,B),_), % (y*6)*(y*5) = 30 *y^2
  (A = cst(30),B = expr(*,id(y),id(y)), !;
  B = cst(30), A = expr(*,id(y),id(y)), !;
  A = id(y), B = expr(*,id(y),cst(30)), !;
  B = id(y), A = expr(*,id(y),cst(30)), !;
  A = id(y), B = expr(*,cst(30),id(y)), !;
  B = id(y), A = expr(*,cst(30),id(y)), !).

test(fold_expr_neg2,[condition(testState(TestState))]) :-
  fold_expr(expr(+,cst(5),neg(id(y))),TestState,expr(-,cst(5),id(y)),_).
  
test(fold_expr_verschachtelt, [condition(testState(TestState))]) :-
  Expr = expr(*,cst(1),expr(*,cst(2),expr(*,cst(3),cst(4)))),
  fold_expr(Expr,TestState,cst(24),_).
 
test(fold_expr_verschachtelt2, [condition(testState(TestState))]) :-
  Expr = expr(*,cst(2),expr(*,id(y),expr(*,cst(3),cst(4)))),
  fold_expr(Expr,TestState,Res,_),
  Expectation1 = expr(*,id(y),cst(24)),
  Expectation2 = expr(*,cst(24),id(y)),
  (Res = Expectation1, !; Res = Expectation2).
  
test(fold_plus_minus, [condition(testState(TestState))]) :-
  Expr = expr(-,cst(2),expr(+,id(y),cst(12))),
  fold_expr(Expr,TestState,expr(-,cst(-10),id(y)),_).
  
test(fold_plus_minus2, [condition(testState(TestState))]) :-
  Left = expr(-,cst(5),id(y)),
  Right = expr(-,cst(2),id(x)),
  Expr = expr(+,Left,Right),
  fold_expr(Expr,TestState,expr(-,cst(1),id(y)),_).

test(fold_mal_geteilt, [condition(testState(TestState))]) :-
  Expr = expr(/,cst(2),expr(*,id(y),cst(4))),
  fold_expr(Expr,TestState,expr(/,cst(0.5),id(y)),_).
  
test(fold_mal_geteilt2, [condition(testState(TestState))]) :-
  Left = expr(/,cst(8),id(y)),
  Right = expr(/,cst(3),id(x)),
  Expr = expr(*,Left,Right),
  fold_expr(Expr,TestState,expr(/,cst(4.0),id(y)),_).
  
test(fold_shift1, [condition(testState(TestState))]) :-
  Expr = expr(<<,expr(<<,id(x),cst(4)),cst(3)),
  fold_expr(Expr,TestState,cst(768),_).
  
test(fold_shift2, [condition(testState(TestState))]) :-
  Expr = expr(<<,expr(<<,id(y),cst(2)),cst(4)),
  fold_expr(Expr,TestState,R,_),
  R = expr(<<,id(y),cst(6)).
  
:- end_tests(constant_folding).
