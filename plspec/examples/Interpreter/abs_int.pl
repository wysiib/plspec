:- module(abs_int,[abs_int/3, abs_int/2]).
:- use_module(fileProcessor,[process_file/4,extract_line_from_Statement/2]).
:- use_module(logger).
:- use_module(null_pos_neg).
:- use_module(library(plunit)).
:- use_module(plspec/plspec/plspec_core,[defspec/2,defspec_pred/2,spec_pre/2,spec_post/3,enable_all_spec_checks/0,log/3]).

:- enable_all_spec_checks.
:- plspec_core:set_loglevel(debug).
:- defspec(skip,compound(skip(int))).
:- defspec(if,compound(if(int,pred,block,one_of([block,skip])))).
:- defspec(while,compound(while(int,pred,block))).
:- defspec(for,one_of([compound(for(int,def,pred,def,block)),compound(for(int,id,expr,expr,block))])).
:- defspec(def,compound(def(int,id,expr))).
:- defspec(print, compound(print(int,expr))).
:- defspec(block,list(statement)).
:- defspec(statement, one_of([skip,if,while,for,def,print])).
:- defspec(cst,compound(cst(int))).
:- defspec(expr, one_of([cst, compound(expr(op,expr,expr)), compound(neg(expr)), id])).
:- defspec(id, compound(id(atom))).
:- defspec(op, one_of([atom(+), atom(-), atom(*), atom(/), atom(**), atom(^), atom(>>), atom(<<)])).
:- defspec(pred,one_of([compound(pred(pred_op,expr,expr)),compound(not(pred))])).
:- defspec(pred_op,one_of([atom(<), atom(>), atom(=<), atom(>=), atom(==), atom(=\=)])).
:- defspec(state_list,list(state_list_element)).
:- defspec(state,one_of([atom(t),compound(t(atom,atom,atom,state,state))])).

state_list_element(A-B) :-
    atom(A), atom(B).

:- defspec_pred(state_list_element,state_list_element).


:- spec_pre(int_expr/4,[one_of([cst,expr,compound(neg(expr)),id]),state,var,int]).
:- spec_post(int_expr/4,[one_of([cst,expr,compound(neg(expr)),id]),state,var,int],[ground,state,atom,int]).
int_expr(cst(Val),_,AbsVal,Line) :- !,
  alpha(Val,AbsVal),
  log("%t is abstracted to %t.",[Val,AbsVal],info,abs_int,Line).
int_expr(expr(Op,A,B),State,Val,Line) :- !,
  int_expr(A,State,ValA,Line),
  int_expr(B,State,ValB,Line),
  abs_expr(Op,ValA,ValB,Val,Line).
int_expr(neg(A),State,Val,Line) :- !,
    int_expr(A,State,ValA,Line),
    abs_neg(ValA,Val),
    log("%t is abstracted to %t.",[neg(A),Val],info,abs_int,Line).
int_expr(id(N),State,Val,Line) :- 
  get_assoc(N,State,Val),!,
  log("%t is abstracted to %t.",[id(N),Val],info,abs_int,Line).
int_expr(id(A),_,X,Line) :-
    undef(X),
    log("%t is undefined",[id(A)],error,abs_int,Line).
  

:- spec_pre(int_pred/5,[pred,state,var,one_of([var,atom]),int]).
:- spec_post(int_pred/5,[pred,state,var,var,int],[pred,state,state,atom,int]).
int_pred(pred(Op,A,B),State,StateOut,ValOut,Line) :-
  int_expr(A,State,ValA,Line),
  int_expr(B,State,ValB,Line),
  abs_pred(Op,ValA,ValB,ValOut,NValA,NValB),
  (A = id(NameA) -> put_assoc(NameA,State,NValA,StateT) ; StateT = State),
  (B = id(NameB) -> put_assoc(NameB,StateT,NValB,StateOut) ; StateOut = StateT).
int_pred(not(P),State,State,Val,Line) :-
  int_expr(P,State,PVal,Line),
  abs_not(PVal,Val).

:- spec_pre(start_int/4,[list(int),any,list(atom),var]).
:- spec_post(start_int/4,[list(int),any,list(atom),var],[list(int),any,list(atom),state]).
start_int(Code,Path,Options,A) :-
  process_file(Code,Path,Options,AST),
  log(AST),
  empty_assoc(State),
  int(AST,State,StateOut),
  assoc_to_list(StateOut,A).

:- spec_pre(int/3,[any,state,var]).
:- spec_pre(int/3,[any,state,var]).
:- spec_post(int/3,[block,state,var],[block,state,state]).
:- spec_post(int/3,[statement,state,var],[statement,state,state]).
int([],State,State).
int([H|T],State,StateOut) :-
  int(H,State,StateT),
  int(T,StateT,StateOut).
int(Statement,State,StateOut) :-
  extract_line_from_Statement(Statement,Line),
  int2(Statement,State,StateOut),
  assoc_to_list(StateOut,StateList),
  log('after %w: %w',[Statement,StateList],info,abs_int,Line).


int(Statement,A,A) :- % int ist gefailt
    extract_line_from_Statement(Statement,Line),!,
    log("Could not process",error,abs_int,Line).
int(_,A,A) :- !,% int ist gefailt
    log("Could not process",error,abs_int,0).

:- spec_pre(int2/3,[statement,state,var]).
:- spec_pre(int2/3,[block,state,var]).
:- spec_post(int2/3,[statement,state,var],[statement,state,state]).
int2(skip(_),State,State).

% Es gibt keinen State, der den If- *oder* den Else-Block wahr machen würde -> Fehler
int2(if(Line,Pred,_,_),StateIn,StateIn) :-
  findall((true,BetterStateIn),int_pred(Pred,StateIn,BetterStateIn,true,Line),[]),
  findall((false,BetterStateIn),int_pred(Pred,StateIn,BetterStateIn,false,Line),[]),!,
  log("No branch of if-Statement is reachable",error,abs_int,Line).

% Der Then-Block ist nicht erreichbar, da es keinen Zustand gibt, der die Bedingung wahr macht
int2(if(Line,Pred,If,Else),StateIn,StateOut) :-
  findall((true,BetterStateIn),int_pred(Pred,StateIn,BetterStateIn,true,Line),[]),!,
  log("Then-Block is unreachable",warning,abs_int,Line),
  findall((false,BetterStateIn),int_pred(Pred,StateIn,BetterStateIn,false,Line),Solutions),
  maplist(int_if(If,Else),Solutions,PossibleStates),
  merge_list_of_states(PossibleStates,StateOut).
 
% Der Else-Block ist nicht erreichbar da es keinen Zustand gibt, der die Bedingung falsch macht
int2(if(Line,Pred,If,Else),StateIn,StateOut) :-
  findall((false,BetterStateIn),int_pred(Pred,StateIn,BetterStateIn,false,Line),[]),!,
  findall((true,BetterStateIn),int_pred(Pred,StateIn,BetterStateIn,true,Line),Solutions),
  log("Else-Block is unreachable",warning,abs_int,Line),
  maplist(int_if(If,Else),Solutions,PossibleStates),
  merge_list_of_states(PossibleStates,StateOut). 
  
% Beide Blöcke sind erreichbar
int2(if(Line,Pred,If,Else),StateIn,StateOut) :-
  findall((Val,BetterStateIn),int_pred(Pred,StateIn,BetterStateIn,Val,Line),Solutions),
  maplist(int_if(If,Else),Solutions,PossibleStates),
  merge_list_of_states(PossibleStates,StateOut).
  
int2(while(Line,Pred,Block),StateIn,StateOut) :-
  int_while(Line,Pred,Block,StateIn,StateOut).
  
int2(for(Line,id(X),From,To,Statements),StateIn,StateOut) :-
  append(Statements,[def(Line,id(X),expr(+,id(X),cst(1)))],WhileBody),
  int([def(Line,id(X),From),while(Line,pred(<,id(X),To),WhileBody)],StateIn,StateOut).
  
int2(for(Line,def(Line,id(X),Start),EndPred,Change,Statements),StateIn,StateOut) :-
    append(Statements,[Change],WhileBody),
    int([def(Line,id(X),Start),while(Line,EndPred,WhileBody)],StateIn,StateOut).
    
int2(def(Line,id(VName),Expr),State,StateOut) :-
  int_expr(Expr,State,Val,Line),
  put_assoc(VName,State,Val,StateOut). 
  
int2(print(Line,Expr),State,State) :-
  int_expr(Expr,State,Val,Line),
  log(Val).


:- spec_pre(int_if/4,[block,one_of([block,skip]),ground,var]).
:- spec_post(int_if/4,[block,one_of([block,skip]),ground,var],[block,one_of([block,skilp]),ground,state]).
int_if(If,_,(true,StateIn),StateOut) :-
  int(If,StateIn,StateOut).
int_if(_,Else,(false,StateIn),StateOut) :-
  int(Else,StateIn,StateOut).

:- spec_pre(int_while/5,[int,pred,block,state,var]).
:- spec_post(int_while/5,[int,pred,block,state,var],[int,pred,block,state,state]).
int_while(Line,Pred,Block,StateIn,StateOut) :-
  fixpoint_loop_body(Line,Pred,Block,StateIn,LoopState),
  findall(StateOut,int_pred(Pred,LoopState,StateOut,false,Line),StatesWherePredIsFalse),
  (StatesWherePredIsFalse = [] 
    -> log("found endless loop",error,abs_int,Line),StateOut=StateIn;
   merge_list_of_states(StatesWherePredIsFalse,StateOut)).

:-spec_pre(fixpoint_loop_body/5,[int,pred,any,state,var]).
fixpoint_loop_body(Line,Pred,_Block,StateIn,StateIn) :-
  % Es gibt keinen State, der die Eintrittsbedingung wahr macht
  findall(StateOut,int_pred(Pred,StateIn,StateOut,true,Line),[]),!,
  log("found unreachable code",warning,abs_int,Line).
fixpoint_loop_body(Line,Pred,Block,StateIn,ResultState) :-
  % Eine Runde durch die Schleife:
  % 1. Alle Möglichkeiten, die Schleife zu betreten
  findall(StateOut,int_pred(Pred,StateIn,StateOut,true,Line),StatesWherePredIsTrue),
  % 2. Merge: Was haben alle gemeinsam
  merge_list_of_states(StatesWherePredIsTrue,LoopEnterState),
  int(Block,LoopEnterState,StateAfterLoop),
  % Wenn sich der State verändert hat: Nochmal!
  % Wenn sich nichts verändert hat: Fertig!
  (StateAfterLoop = StateIn -> ResultState = StateAfterLoop
                            ;  fixpoint_loop_body(Line,Pred,Block,StateAfterLoop,ResultState)).

:- spec_pre(merge_list_of_states/2,[list(state),var]).
:- spec_post(merge_list_of_states/2,[list(state),var],[list(state),state]).
merge_list_of_states([H],H).
merge_list_of_states([H|T],S) :-
  merge_list_of_states(T,ST),
  merge_states(H,ST,S).
merge_states(State1,State2,StateOut) :-
  assoc_to_keys(State1,Keys),
  empty_assoc(CurrentState),
  merge_keys(Keys,State1,State2,CurrentState,StateOut).
merge_keys([],_,_,S,S).
merge_keys([Key|Keys],State1,State2,Current,Out) :-
  (get_assoc(Key,State1,Val1) -> true ; undef(Val1)),
  (get_assoc(Key,State2,Val2) -> true ; undef(Val2)),
  lub(Val1,Val2,Val),
  put_assoc(Key,Current,Val,NewState),
  merge_keys(Keys,State1,State2,NewState,Out).

:- spec_pre(abs_int/3,[any,var,list(atom)]).
:- spec_post(abs_int/3,[any,var,list(atom)],[any,list(state),list(atom)]).
abs_int(F,StateList,Options) :-
  read_file_to_codes(F, Code, []),
  start_int(Code,F,Options,StateList),!.

:- spec_pre(abs_int/2,[any,var]).
:- spec_post(abs_int/2,[any,var],[any,state_list]).
abs_int(F,StateList) :-
  read_file_to_codes(F, Code, []),
  start_int(Code,F,[],StateList),!.
