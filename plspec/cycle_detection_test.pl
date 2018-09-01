:- use_module(library(plunit)).
:- use_module(plspec_core).

:- enable_all_spec_checks.
:- set_loglevel(debug).

:- begin_tests(mark_recursive1, [setup(plspec:set_error_handler(throw)), cleanup(plspec:set_error_handler(plspec_default_error_handler))]).

test(test1,[]) :-
    defspec(a,one_of(b,c)),
    not(plspec:is_recursive(a)),
    defspec(b,a),
    plspec:is_recursive(a),
    plspec:is_recursive(b),
    not(plspec:is_recursive(c)),
    defspec(d,a),
    plspec:is_recursive(d).

:- end_tests(mark_recursive1).
