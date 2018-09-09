:- module(parser, [parse/2]).


% arithmetic expressions
float(F) --> digit(D0), digits(D), `.`, digit(E0), digits(E), {append([D0|D],[E0|E],Codes), number_codes(F,Codes)}.
integer(I) --> natural_number(I).
integer(I) --> `-`,natural_number(J),{I is -J}.
natural_number(I) --> digit(D0), digits(D), {number_codes(I, [D0|D])}.
digits([D|T]) --> digit(D), !, digits(T).
digits([]) --> [].
digit(D) --> [D], {code_type(D, digit)}.

ws --> [D], {code_type(D, white), !}, ws.
ws --> ``.

identifier(id(I)) --> char(D0), chars(D), {atom_codes(I, [D0|D])}.
chars([D|T]) --> char(D), !, chars(T).
chars([]) --> [].
char(D) --> [D], {code_type(D, alpha)}.

constant(cst(X)) --> integer(X).
constant(cst(F)) --> float(F).

predicate(pred(<,X,Y)) -->
  expression(X), ws, `<`, ws, expression(Y).
predicate(pred(=<,X,Y)) -->
  expression(X), ws, `=<`, ws, expression(Y).
predicate(pred(>,X,Y)) -->
  expression(X), ws, `>`, ws, expression(Y).
predicate(pred(>=,X,Y)) -->
  expression(X), ws, `>=`, ws, expression(Y).
predicate(pred(==,X,Y)) -->
  expression(X), ws, `=`, ws, expression(Y).
predicate(pred(=\=,X,Y)) -->
  expression(X), ws, `!=`, ws, expression(Y).
predicate(not(X)) -->
  `!`, ws, predicate(X).


expression(expr(+,X,Y)) --> expression2(X), ws, `+`, ws, expression(Y).
expression(expr(-,X,Y)) --> expression2(X), ws, `-`, ws, expression(Y).
expression(X) --> expression2(X).

expression2(expr(*,X,Y)) --> expression3(X), ws, `*`, ws, expression2(Y).
expression2(expr(/,X,Y)) --> expression3(X), ws, `/`, ws, expression2(Y).
expression2(expr(<<,X,Y)) --> expression3(X), ws, `<<`, ws, expression2(Y).
expression2(expr(>>,X,Y)) --> expression3(X), ws, `>>`, ws, expression2(Y).
expression2(X) --> expression3(X).

expression3(expr(**,X,Y)) --> expression4(X), ws, `^`, ws, expression3(Y).
expression3(expr(**,X,Y)) --> expression4(X), ws, `**`, ws, expression3(Y).
expression3(expr(mod,X,Y)) --> expression4(X), ws, `%`, ws, expression3(Y).
expression3(X) --> expression4(X).

expression4(X) --> `(`, ws, expression(X), ws, `)`.
expression4(X) --> constant(X).
expression4(X) --> identifier(X).
expression4(neg(X)) --> `-`, expression(X).

% Erstes Argument der Elemente im AST ist die Zeile

parse_else(In,Out,Statements) -->
  `else`, ws, new_line(In,Next), ws,statements(Next,Out,Statements).
parse_else(In,In,skip(In)) --> ``.

statement(A,A,def(A,Var,Expr)) -->
  identifier(Var), ws, `:=`, ws, expression(Expr).
statement(A,A,print(A,Expr)) -->
  `print `, ws, expression(Expr).
statement(In,Out,if(In,Expr,Then,Else)) -->
  `if `, ws,
  predicate(Expr), ws,
  `do`, ws, new_line(In,Next),
  statements(Next,AfterThen,Then),
  parse_else(AfterThen,Out,Else),
  ws, `done`.
statement(In,Out,while(In,Pred,Block)) -->
  `while `, ws,
  predicate(Pred), ws,
  `do`, ws, new_line(In,AfterHead),
  statements(AfterHead,Out,Block),
  ws, `done`.
statement(In,Out,for(In,Expr,From,To,Block)) -->
  `for `, ws,
  identifier(Expr), ws,
  `in`, ws, expression(From),
  ws, `..`, expression(To), ws,
  `do`, ws, new_line(In,AfterHead),
  statements(AfterHead,Out,Block),
  ws, `done`.
statement(In,Out,for(In,def(In,Var,Expr), Ende, def(In,Var,Change),Block)) -->
  `for `, ws,
  statement(In,In,def(In,Var,Expr)), `;`,ws,
  predicate(Ende), `;`,ws,
  statement(In,In,def(In,Var,Change)), ws,
  `do`, ws, new_line(In,AfterHead),
  statements(AfterHead,Out,Block),
  ws, `done`.


statements(In,Out,[D|T]) -->
  ws, statement(In,AfterFirstStatement,D), ws, new_line(AfterFirstStatement,Next),
  !, statements(Next,Out,T).
statements(In,In,[]) --> [].

one_new_line(In,Out) --> [D], {code_type(D, end_of_line), !, Out is In+1}.

new_line(In,Out) --> [A,B], {code_type(A,end_of_line), code_type(B,end_of_line),!,Next is In+1},{!},new_line(Next,Out).
new_line(In,Out) --> [D], {code_type(D, newline), !, Next is In+1},{!}, new_line(Next,Out).
new_line(In,In) --> ``.
 

parse(Codes,ParsedAST) :-
    new_line(1,Out,Codes,Rest),statements(Out,_,ParsedAST,Rest,[]).
    

    
