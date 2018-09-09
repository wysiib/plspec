:- module(imp_int,[impl_int/1,impl_int/2]).
:- use_module(fileProcessor,[process_file/4,extract_line_from_Statement/2]).
:- use_module(logger).

int_expr(cst(Val),_,Val).
int_expr(id(N),State,Val) :-
  get_assoc(N,State,Val).
int_expr(neg(X),State,Val) :-
	int_expr(X,State,ValX),
	Val is -ValX.
int_expr(expr(Op,A,B),State,Val) :-
  int_expr(A,State,ValA),
  int_expr(B,State,ValB),
  Term =.. [Op,ValA,ValB],
  Val is Term.

int_pred(pred(Op,A,B),State,Val) :-
  int_expr(A,State,ValA),
  int_expr(B,State,ValB),
  (call(Op,ValA,ValB) -> Val = true ; Val = false).
int_pred(not(P),State,Val) :-
  int_expr(P,State,PVal),
  (PVal = true -> Val = false ; Val = true).

start_int(Code,Path,Options) :-
  process_file(Code,Path,Options,AST),
  empty_assoc(State),
  int(AST,State,_).
 
int([],State,State).
int([H|T],State,StateOut) :-
  int(H,State,StateT),
  int(T,StateT,StateOut).
int(skip(_),State,State).
int(if(_Line,Pred,If,Else),StateIn,StateOut) :-
  int_pred(Pred,StateIn,Val),
  (Val = true  -> int(If,StateIn,StateOut) ;
   Val = false -> int(Else,StateIn,StateOut)).
int(while(Line,Pred,Block),StateIn,StateOut) :-
  int(if(Line,Pred,[Block,while(Line,Pred,Block)],skip(Line)),StateIn,StateOut).
int(for(_Line,id(X),From,To,Statements),StateIn,StateOut) :-
  int_expr(From,StateIn,FromVal),
  int_expr(To,StateIn,ToVal),
  put_assoc(X,StateIn,FromVal,StateT),
  int_for(X,FromVal,ToVal,Statements,StateT,StateOut).
int(for(Line,def(Line,id(VName),Start),End,Change,Statements),StateIn,StateOut) :-
  int(def(Line,id(VName),Start),StateIn,StateT1),
  int_for2(VName,Change,End,Statements,StateT1,StateOut).
int(def(_Line,id(VName),Expr),State,StateOut) :-
  int_expr(Expr,State,Val),
  put_assoc(VName,State,Val,StateOut).
int(print(_Line,Expr),State,State) :-
  int_expr(Expr,State,Val),
  log(Val).
  
int(Statement,_,_) :- !, %Interpretieren dieses Statements ist fehlgeschlagen
  extract_line_from_Statement(Statement,Line),
  log("Could not interpret",error,imp_int,Line).


int_for(X,FromVal,ToVal,Statements,StateIn,StateOut) :-
  get_assoc(X,StateIn,Val),
  (Val < ToVal  -> int(Statements,StateIn,StateT),
                   NX is Val+1, put_assoc(X,StateT,NX,StateTT),
                   int_for(X,FromVal,ToVal,Statements,StateTT,StateOut) ;
   Val >= ToVal -> StateIn = StateOut).
   
int_for2(X,Change,EndCondition,Statements,StateIn,StateOut) :-
  int_pred(EndCondition,StateIn,Body),
  (Body = true -> int(Statements,StateIn,StateT),
                  int(Change,StateT,StateT2),
                  int_for2(X,Change,EndCondition,Statements,StateT2,StateOut) ;
   Body = false -> StateIn = StateOut).

impl_int(F,Options) :-
  read_file_to_codes(F, Code, []),
  start_int(Code,F,Options), !.
  
impl_int(F) :-
  read_file_to_codes(F, Code, []),
  start_int(Code,F,[]), !.
