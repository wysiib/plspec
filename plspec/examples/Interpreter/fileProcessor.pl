:- module(fileProcessor,[process_file/4, getOptions/1,extract_line_from_Statement/2,set_loglevel/1,loglevel/1]).
:- use_module(parser,[parse/2]).
:- use_module(constant_folding,[folding/3]).
:- use_module(strength_reduction,[reduction/2]).
:- use_module(library(option)).
:- meta_predicate loglevel(0, ?).
:- retractall(loglevel(_)),asserta(loglevel(error)).

% Dieses Modul fungiert als eine Art wrapper für den Parser.
% process_file parst die Datei, verbessert anschließend den
% AST und schreibt die verbesserte Version in eine Datei
% Die Interpreter kennen den Parser nicht, sondern nur dieses Modul


% Setzt das Loglevel
% nothing -> nichts wird geprinted
% info -> info, warning und error
% warning -> warning and error
% error -> error
set_loglevel(nothing) :-
    retractall(loglevel(_)).
    
set_loglevel(info) :-
    retractall(loglevel(_)),
    asserta(loglevel(info)),
    asserta(loglevel(warning)), 
    asserta(loglevel(error)).

set_loglevel(warning) :-
    retractall(loglevel(_)),
    asserta(loglevel(warning)),
    asserta(loglevel(error)).
    
set_loglevel(error) :-
    retractall(loglevel(_)),
    asserta(loglevel(error)).
    
    
    
process_file(Code,Path,AST) :-
    process_file(Code,Path,[sr(false),cf(false)],AST).
process_file(Code,Path,Options,Folded_AST) :-
    get_bapl_and_ast_name(Path,"apl",Path_bapl,_Path_AST),
    parse(Code,AST),
    (option(sr(SR),Options) -> SR = SR; SR = false), % Führe Strength Reduction durch
    (option(cf(CF),Options) -> CF = CF; CF = false), % Führe Constant Folding durch
    (SR -> reduction(AST,Reduced_AST);AST = Reduced_AST),
    (CF -> folding(Reduced_AST,Folded_AST,Options);Reduced_AST = Folded_AST),
    ((SR;CF) -> write_programm_from_AST(Folded_AST,Path_bapl);true). 

    
process_file(Code,Path,_,AST) :-
    get_bapl_and_ast_name(Path,"bapl",_,_),
    parse(Code,AST).
    
get_bapl_and_ast_name(Path,Old_Ending,Path_bapl,Path_AST) :-
    split_string(Path,".","",[FileName,Old_Ending]),
    string_concat(FileName,".bapl",Path_bapl), % Better APL -> durch ggf SR und CF verbesserte Version
    string_concat(FileName,".ast",Path_AST). % mit der Endung .ast könnte man den AST abspeichern -> nicht implementiert
  
% Hilfsmethode, um aus den modifizierten Statements die Zeile zu bekommen  
extract_line_from_Statement(if(Line,_,_,_),Line) :- !.
extract_line_from_Statement(while(Line,_,_),Line) :- !.
extract_line_from_Statement(for(Line,_,_,_,_),Line) :- !.
extract_line_from_Statement(def(Line,_,_),Line) :- !.
extract_line_from_Statement(print(Line,_),Line) :- !.   
extract_line_from_Statement(skip(Line),Line) :- !. 
  
getOptions([sr(boolean),cf(boolean),fp(boolean)]) :-
    write("Option | Long Name          | default | Meaning"),nl,
    write("----------------------------------------------------------------------------------------------"),nl,
    write("sr     | Strength Reduction | false   | when true, strength reduction is execute after parsing"),nl,
    write("cf     | Constant Folding   | false   | when true, constant folding is executed after parsing"),nl,
    write("fp     | Folding Print      | true    | when true, the expressions after print are folded."),nl.
    
predicates :-
    write("abs_int(+Path,-StateList)"),nl,
    write("abs_int(+Path,-StateList,+Options)"),nl,
    write("impl_int(+Path)"),nl,
    write("impl_int(+Path,+Options)"),nl,
    write("parse(+Codes,-ParsedAST)"),nl,
    write("process_file(+Code,+Path,-AST)"),nl,
    write("process_file(+Code,+Path,+Options,-AST)"),nl.
     
write_programm_from_AST(AST,FileName) :-
    open(FileName,write,Stream),
    write_programm(AST,Stream),
    close(Stream).
    
write_programm([],_) :- !.
write_programm([F|AST],Stream) :-
    write_programm(F,Stream),
    write_programm(AST,Stream).
    
write_programm(def(_,id(X),Expr),Stream) :-
    writeq(Stream,X),
    write(Stream," := "),
    write_expr(Expr,Stream),nl(Stream).
   
write_programm(print(_,Expr),Stream) :-
    write(Stream,"print "),
    write_expr(Expr,Stream),nl(Stream).
    
write_programm(if(_,Pred,Then,skip(_)),Stream) :- !,
    write(Stream,"if "),
    write_pred(Pred,Stream),
    write(Stream," do\n"),
    write_programm(Then,Stream),
    write(Stream,"done\n").
    
    
write_programm(if(_,Pred,Then,Else),Stream) :-
    write(Stream,"if "),
    write_pred(Pred,Stream),
    write(Stream," do\n"),
    write_programm(Then,Stream),
    write(Stream,"else\n"),
    write_programm(Else,Stream),
    write(Stream,"done\n").
    
write_programm(while(_,Pred,Block),Stream) :-
    write(Stream,"while "),
    write_pred(Pred,Stream),
    write(Stream," do\n"),
    write_programm(Block,Stream),
    write(Stream,"done\n").
    
write_programm(for(_,id(X),From,To,Block),Stream) :-
    write(Stream,"for "),
    write_expr(id(X),Stream),
    write(Stream," in "),
    write_expr(From,Stream),
    write(Stream,".."),
    write_expr(To,Stream),
    write(Stream," do\n"),
    write_programm(Block,Stream),
    write(Stream,"done\n").

write_programm(for(_,def(_,id(Var),Expr), Ende, def(_,id(Var),Change),Block),Stream) :-
    write(Stream,"for "),
    writeq(Stream,Var),
    write(Stream," := "),
    write_expr(Expr,Stream),
    write(Stream,"; "),
    write_pred(Ende,Stream),
    write(Stream,"; "),
    writeq(Stream,Var),
    write(Stream," := "),
    write_expr(Change,Stream),
    write(Stream," do\n"),
    write_programm(Block,Stream),
    write(Stream,"done\n").
    
write_pred(pred(Op,A,B),Stream) :-
    write_expr(A,Stream),
    writeq(Stream,Op),
    write_expr(B,Stream).
    
    
write_expr(expr(Op1,X,Y),Stream) :-
    op_class(Op1,1),!,
    (X = cst(N), N < 0 -> write(Stream,"("), write_expr(X,Stream),write(Stream,")"); write_expr(X,Stream)),
    writeq(Stream,Op1),
    (Y = cst(M), M < 0 -> write(Stream,"("), write_expr(Y,Stream),write(Stream,")"); write_expr(Y,Stream)).
write_expr(expr(Op2,X,Y),Stream) :-
    op_class(Op2,2),!,
    (X = expr(OpA,_,_), op_class(OpA,1) -> write(Stream,"("),write_expr(X,Stream),write(Stream,")");write_expr(X,Stream)),
    writeq(Stream,Op2),
    (Y = expr(OpB,_,_), op_class(OpB,1) -> write(Stream,"("),write_expr(Y,Stream),write(Stream,")");write_expr(Y,Stream)).
write_expr(expr(Op3,X,Y),Stream) :-
    op_class(Op3,3),!,
    (X = expr(OpA,_,_), op_class(OpA,CA), CA < 3 -> write(Stream,"("),write_expr(X,Stream),write(Stream,")");write_expr(X,Stream)),
    writeq(Stream,Op3),
    (Y = expr(OpB,_,_), op_class(OpB,CB), CB < 3 -> write(Stream,"("),write_expr(Y,Stream),write(Stream,")");write_expr(Y,Stream)).

write_expr(id(X),Stream) :-
    writeq(Stream,X).
write_expr(cst(X),Stream) :-
    write(Stream,X).


write_expr(neg(X),Stream) :-
    write(Stream,'-('),
    write_expr(X,Stream),
    write(Stream,')').

  
% Priorität der Operatoren
% Für die Klammersetzung  
op_class(+,1).
op_class(-,1).
op_class(*,2).
op_class(/,2).
op_class(>>,2).
op_class(<<,2).
op_class(**,3).
op_class(mod,3).