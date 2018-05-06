:- module(validator, [spec_predicate/2, spec_predicate_recursive/4, spec_indirection/2, spec_connective/4, spec_exists/1,
                      true/1, atom/2,
                      valid/2,
                      evaluate_spec_match/3, evaluate_spec_match_aux/3,
                      list/4, compound/4, tuple/4,
                      spec_and/4, and/3, or/3
                     ]).

:- use_module(library(terms), [variant/2]).
:- dynamic spec_indirection/2, spec_predicate/2, spec_predicate_recursive/4, spec_connective/4.
:- multifile spec_indirection/2, spec_predicate/2, spec_predicate_recursive/4, spec_connective/4.



% Definition of spec predicates
spec_predicate(atomic, atomic).
spec_predicate(atom, atom).
spec_predicate(atom(X), atom(X)). %TODO: why is this needed?
spec_predicate(integer, integer).
spec_predicate(number, number).
spec_predicate(float, float).
spec_predicate(var, var).
spec_predicate(ground, ground).
spec_predicate(nonvar, nonvar).
spec_predicate(any, true).

spec_predicate_recursive(compound(X), compound(X), and, and_invariant).
spec_predicate_recursive(list(X), list(X), and, and_invariant).
spec_predicate_recursive(tuple(X), tuple(X), and, and_invariant).

spec_indirection(int, integer).
spec_indirection([X], list(X)).

spec_connective(and([H|T]), spec_and([H|T]), and, and_invariant).
spec_connective(one_of(X), spec_and(X), or, or_invariant).

%When does a predicate exists:
spec_exists(X) :- spec_predicate(X, _).
spec_exists(X) :- spec_predicate_recursive(X, _, _, _).
spec_exists(X) :- spec_indirection(X, _).
spec_exists(X) :- spec_connective(X, _, _, _).

:- public true/1.
true(_).
:- public atom/2.
atom(X, Y) :- atom(Y), X = Y.

valid(Spec, Val) :-
    evaluate_spec_match(Spec, Val, Success),
    Success == true.

% evaluate_spec_match
%% checks, if the spec exists.If no, fail, if yes, call evaluate_spec_match_aux
evaluate_spec_match(Spec, _, fail(spec_not_found(spec(Spec)))) :-
    nonvar(Spec),
\+ spec_exists(Spec), !,
format('plspec: spec ~w not found~n', [Spec]).
evaluate_spec_match(Spec, Val, Res) :-
    %spec_exists(Spec),
    evaluate_spec_match_aux(Spec, Val, Res).

%evaluate_spec_match_aux matches the value Val against the existing spec Spec.
% There are different kinds of spec predicates:

% a normal spec predicate
evaluate_spec_match_aux(Spec, Val, Res) :-
    spec_predicate(Spec, Predicate),
    %% HACK: copy_term does weird things to co-routines
    copy_term(Val, Vali),
    (call(Predicate, Val)
     -> Res = true
     ; Res = fail(spec_not_matched(spec(Spec), value(Val)))),
    (copy_term(Val, Valii), variant(Valii, Vali) -> true ; format('plspec: implementation of spec ~w binds variables but should not~n', [Predicate])).

% a recursive spec
evaluate_spec_match_aux(Spec, Val, Res) :-
    spec_predicate_recursive(Spec, Predicate, MergePred, _MergePredInvariant),
    copy_term(Val, Vali),
    (call(Predicate, Val, NewSpecs, NewVals)
     -> call(MergePred, NewSpecs, NewVals, Res)
     ; Res = fail(spec_not_matched(spec(Spec), value(Val)))),
    (copy_term(Val, Valii), variant(Valii, Vali) -> true ; format('plspec: implementation of spec ~w binds variables but should not~n', [Predicate])).

% a connective spec
evaluate_spec_match_aux(Spec, Val, Res) :-
    nonvar(Spec),
    spec_connective(Spec, Predicate, MergePred, _MergePredInvariant),
    copy_term(Val, Vali),
    (call(Predicate, Val, NewSpecs, NewVals)
     -> call(MergePred, NewSpecs, NewVals, Res)
     ; Res = fail(spec_not_matched(spec(Spec), value(Val)))),
    (copy_term(Val, Valii), variant(Valii, Vali) -> true ; format('plspec: implementation of spec ~w binds variables but should not~n', [Predicate])).

%spec was an alias for another spec
evaluate_spec_match_aux(Spec, Val, Res) :-
    spec_indirection(Spec, NewSpec),
    evaluate_spec_match(NewSpec, Val, Res).

% built-in recursive specs
list(Spec, Val, NewSpecs, NewVals) :-
    nonvar(Val), list1(Val, Spec, NewSpecs, NewVals).
%% list1 only ensures that the value is a list.
%% The type of its members is checked later on in a seperate step.
%% list1 will return a spec for each member.
%% If a tail is a variable, the bound value should be
%% of the same type as the list itself.
list1(L, Spec, [Spec|ST], [H|VT]) :-
    nonvar(L), L = [H|T], !,
    list1(T, Spec, ST, VT).
list1(L, _, [], []) :-
    nonvar(L), L = [], !.
list1(Var, Spec, [list(Spec)], [Var]) :- var(Var).


:- public compound/4.
compound(Spec, Val, NewSpecs, NewVars) :-
    compound(Val),
    Val =.. [Functor|NewVars],
    Functor \= '[|]',
    length(NewVars, Len),
    length(NewSpecs, Len),
    Spec =.. [Functor|NewSpecs].

:- public tuple/4.
tuple(SpecList, VarList, SpecList, VarList) :-
    is_list(VarList).

spec_and(SpecList, Var, SpecList, VarRepeated) :-
    SpecList \= [],
    %% this is actually repeat
    length(SpecList,L),
    length(VarRepeated,L),
    maplist(=(Var), VarRepeated).

:- public and/3.
and([], [], true).
and([S|Specs], [V|Vals], Res) :-
    evaluate_spec_match(S, V, X),
    (X == true
     -> and(Specs, Vals, Res)
     ; Res = fail(spec_not_matched(spec(S), value(V)))).

:- public or/3.
or(Specs, Vals, true) :-
    or2(Specs, Vals), !.
or(Specs, Vals, fail(spec_not_matched_merge(specs(or(Specs)), values(Vals)))).

or2([HSpec|TSpec], [HVal|TVal]) :-
    (evaluate_spec_match(HSpec, HVal, true)
     -> true
     ;  or2(TSpec, TVal)).
