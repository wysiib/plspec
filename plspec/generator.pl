:- use_module(plspec_core).
:- use_module(validator).
:- use_module(library(random)).

generate(Spec,Value) :-
  spec_predicate(Spec,Predicate),
  generate_spec_predicate(Spec,Predicate,Value).

generate_spec_predicate(integer, Predicate, Value) :-
  N = 1000,
  AbsValue is random(N),
  (maybe
  -> Value = AbsValue
  ; Value is (-1)*AbsValue),
  call(Predicate,Value).

generate_spec_predicate(float, Predicate, Value) :-
  generate_spec_predicate(integer,integer,Integer),
  Float is random_float,
  Value is Integer + Float,
  call(Predicate, Value).

generate_spec_predicate(number, Predicate, Value) :-
  generate_spec_predicate(integer,integer,Integer),
  generate_spec_predicate(float,float,Float),
  (maybe -> Value = Integer; Value = Float),
  call(Value, Predicate).

list_string_concat([],"") :- !.
list_string_concat([X],X) :- !.
list_string_concat([X,Y|T],Res) :-
  string_concat(X,Y,Z),
  list_string_concat([Z|T],Res).


random_atom(Atom) :-
  L is random(20),
  random_string(String, L),
  atom_string(Atom,String).

random_string(S, Length) :-
  random_letters(Letters,Length),
  list_string_concat(Letters,S).

random_letters(List,Length) :-
  length(List,Length),
  maplist(random_letter,List).

random_letter(L) :-
  random_member(L,["a","b","c","d","e","f","g","h","i","j"]).

%words taken from here: https://github.com/dwyl/english-words/blob/master/words_alpha.txt
