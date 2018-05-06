:- module(prettyprinter, [pretty_print_error/1]).

pretty_print_error(fail(postcondition_violated(matched_pre(Pre), violated_post(Post), value(Val)))) :-
    format('~n! plspec: a postcondition was violated!~n', []),
    format('! plspec: the matched precondition was "~w"~n', [Pre]),
    format('! plspec: however, the postcondition "~w" does not hold~n', [Post]),
    format('! plspec: the offending value was: ~w~n', [Val]).
pretty_print_error(fail(prespec_violated(specs(PreSpecs), values(Vals), location(Functor)))) :-
    format('~n! plspec: no precondition was matched in ~w~n', [Functor]),
    format('! plspec: specified preconditions were: ~w~n', [PreSpecs]),
    format('! plspec: however, none of these is matched by: ~w~n', [Vals]).
pretty_print_error(fail(spec_violated(spec(T), value(V), location(Location)))) :-
    format('~n! plspec: an invariant was violated in ~w~n', [Location]),
    format('! plspec: the spec was: ~w~n', [T]),
    format('! plspec: however, the value was bound to: ~w~n', [V]).
pretty_print_error(fail(spec_not_found(spec(Spec)))) :-
    %% TODO: not all failures include a location
    format('~n! plspec: spec "~w" was not found~n', [Spec]).
pretty_print_error(fail(spec_not_found(spec(Spec), location(Location)))) :-
    format('~n! plspec: a spec for ~w was not found~n', [Location]),
    format('! plspec: spec "~w" was not found~n', [Spec]).
pretty_print_error(X) :-
    format('~n! plspec: plspec raised an error that is unhandled.~n', []),
    format('! plspec: ~w.~n', [X]).

pretty_print_error(fail(postcondition_violated(matched_pre(Pre), violated_post(Post), value(Val)))) :-
    format('~n! plspec: a postcondition was violated!~n', []),
    format('! plspec: the matched precondition was "~w"~n', [Pre]),
    format('! plspec: however, the postcondition "~w" does not hold~n', [Post]),
    format('! plspec: the offending value was: ~w~n', [Val]).
pretty_print_error(fail(prespec_violated(specs(PreSpecs), values(Vals), location(Functor)))) :-
    format('~n! plspec: no precondition was matched in ~w~n', [Functor]),
    format('! plspec: specified preconditions were: ~w~n', [PreSpecs]),
    format('! plspec: however, none of these is matched by: ~w~n', [Vals]).
pretty_print_error(fail(spec_violated(spec(T), value(V), location(Location)))) :-
    format('~n! plspec: an invariant was violated in ~w~n', [Location]),
    format('! plspec: the spec was: ~w~n', [T]),
    format('! plspec: however, the value was bound to: ~w~n', [V]).
pretty_print_error(fail(spec_not_found(spec(Spec)))) :-
    %% TODO: not all failures include a location
    format('~n! plspec: spec "~w" was not found~n', [Spec]).
pretty_print_error(fail(spec_not_found(spec(Spec), location(Location)))) :-
    format('~n! plspec: a spec for ~w was not found~n', [Location]),
    format('! plspec: spec "~w" was not found~n', [Spec]).
pretty_print_error(X) :-
    format('~n! plspec: plspec raised an error that is unhandled.~n', []),
    format('! plspec: ~w.~n', [X]).

pretty_print_error(fail(postcondition_violated(matched_pre(Pre), violated_post(Post), value(Val)))) :-
    format('~n! plspec: a postcondition was violated!~n', []),
    format('! plspec: the matched precondition was "~w"~n', [Pre]),
    format('! plspec: however, the postcondition "~w" does not hold~n', [Post]),
    format('! plspec: the offending value was: ~w~n', [Val]).
pretty_print_error(fail(prespec_violated(specs(PreSpecs), values(Vals), location(Functor)))) :-
    format('~n! plspec: no precondition was matched in ~w~n', [Functor]),
    format('! plspec: specified preconditions were: ~w~n', [PreSpecs]),
    format('! plspec: however, none of these is matched by: ~w~n', [Vals]).
pretty_print_error(fail(spec_violated(spec(T), value(V), location(Location)))) :-
    format('~n! plspec: an invariant was violated in ~w~n', [Location]),
    format('! plspec: the spec was: ~w~n', [T]),
    format('! plspec: however, the value was bound to: ~w~n', [V]).
pretty_print_error(fail(spec_not_found(spec(Spec)))) :-
    %% TODO: not all failures include a location
    format('~n! plspec: spec "~w" was not found~n', [Spec]).
pretty_print_error(fail(spec_not_found(spec(Spec), location(Location)))) :-
    format('~n! plspec: a spec for ~w was not found~n', [Location]),
    format('! plspec: spec "~w" was not found~n', [Spec]).
pretty_print_error(X) :-
    format('~n! plspec: plspec raised an error that is unhandled.~n', []),
    format('! plspec: ~w.~n', [X]).
