:- use_module("../plspec/plspec_core").
:- enable_all_spec_checks.
:- set_loglevel(debug).

%:- plspec:set_error_handler(print).

backtracking(X) :-
    member(X,[a,1]),
    only_int(X).

:- spec_pre(only_int/1,[integer]).
only_int(X) :-
    integer(X).


?-backtracking(X).
%@ fail(prespec_violated(specs([[integer],[integer],[integer],[integer],[integer],[integer],[integer]]),values([a]),location(only_int/1)))plspec debugThese pre-post specs matched: []
%@ plspec debug........Unified the arguments with [a]
%@ plspec debug........Pre-Spec [integer] matched!
%@ plspec debug........These pre-post specs matched: []
%@ plspec debug........Unified the arguments with [1]
%@ X = 1.

 
