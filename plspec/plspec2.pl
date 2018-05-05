:- use_module(library(lists), [maplist/2, maplist/3, maplist/4, is_list/1]).
:- use_module(library(terms), [variant/2]).


% Definition of spec predicates
spec_predicate(atomic, atomic).
spec_predicate(atom, atom).
spec_predicate(atom(X), atom(X)).
spec_predicate(integer, integer).
spec_predicate(number, number).
spec_predicate(float, float).
spec_predicate(var, var).
spec_predicate(ground, ground).
spec_predicate(nonvar, nonvar).
spec_predicate(any, true).

%When does a predicate exists:
spec_exists(X) :- spec_predicate(X, _).

%TODO: why is this needed
:- public true/1.
true(_).
:- public atom/2.
atom(X, Y) :- atom(Y), X = Y.

validate(Spec, Val) :-
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
