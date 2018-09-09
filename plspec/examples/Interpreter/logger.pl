:- module(logger,[log/4, log/5, log/1]).
:- use_module(fileProcessor,[loglevel/1]).
  

log(FormatString,Values,Type,Source,Line) :-
    (loglevel(Type) -> header(Type,Source,Line),writef(FormatString,Values),nl;true).
    
log(String,Type,Source,Line) :-
    (loglevel(Type) -> header(Type,Source,Line),  write(String),nl;true).

log(X) :-
    (loglevel(_) -> print(X),nl;true).
    
header(Type,Source,Line) :-
    writef("%t $ %t in Line %t: ",[Type,Source,Line]).
    
header(Type,Source) :-
    writef("%t $ %t: ",[Type,Source]).
    