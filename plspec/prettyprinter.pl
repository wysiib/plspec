:- module(prettyprinter, [pretty_print_error/1]).
:- use_module(logger).

pretty_print_error(fail(postcondition_violated(matched_pre(Pre),
                                               violated_post(Post),
                                               value(Val)))) :-
    log(error, 'A postcondition was violated!'),
    log(error, 'The matched precondition was "~w".',[Pre]),
    log(error, 'However, the postcondition "~w" does not hold',[Post]),
    log(error, 'The offending value was: ~w',[Val]).
pretty_print_error(fail(prespec_violated(specs(PreSpecs),
                                         values(Vals),
                                         location(Functor)))) :-
    log(error, 'No precondition was matched in ~w',[Functor]),
    log(error, 'Specified preconditions ware: ~w', [PreSpecs]),
    log(error, 'However, none of these matched by: ~w', [Vals]).
pretty_print_error(fail(spec_violated(spec(T),
                                      value(V),
                                      location(Location)))) :-
    log(error, 'An invariant was violated in ~w.', [Location]),
    log(error, 'The spec was: ~w.', [T]),
    log(error'However, the value was bound to: ~w.', [V]).
pretty_print_error(fail(spec_not_found(spec(Spec)))) :-
    %% TODO: not all failures include a location
    log(error, 'Spec "~w" was not found!', [Spec]).
pretty_print_error(fail(spec_not_found(spec(Spec), location(Location)))) :-
    log(error, 'A spec for ~w was not found.', [Location]),
    log(error, 'Spec "~w" was not found.', [Spec]).
pretty_print_error(X) :-
    log(error, 'plspec raised an error that is unhandled'),
    log(error, '~w.', [X]).

pretty_print_error(fail(postcondition_violated(matched_pre(Pre),
                                              violated_post(Post),
                                              value(Val)))) :-
    log(error, 'A postcondition was violated!'),
    log(error, 'The matched precondition was "~w".', [Pre]),
    log(error, 'However, the postcondition "~w" does not hold.', [Post]),
    log(error, 'The offending value was: ~w.', [Val]).
pretty_print_error(fail(prespec_violated(specs(PreSpecs), values(Vals),
                                         location(Functor)))) :-
    log(error, 'No precondition was matched in ~w.', [Functor]),
    log(error, 'Specified preconditions were: ~w.', [PreSpecs]),
    log(error, 'However, none of these is matched by: ~w.', [Vals]).
pretty_print_error(fail(spec_violated(spec(T), value(V), location(Location)))) :-
    log(error, 'An invariant was violated in ~w.', [Location]),
    log(error, 'The spec was: ~w.', [T]),
    log(error, 'However, the value was bound to: ~w.', [V]).
pretty_print_error(fail(spec_not_found(spec(Spec)))) :-
    %% TODO: not all failures include a location
    log(error, 'Spec "~w" was not found', [Spec]).
pretty_print_error(fail(spec_not_found(spec(Spec), location(Location)))) :-
    log(error, 'A spec for ~w was not found', [Location]),
    log(error, 'Spec "~w" was not found', [Spec]).
pretty_print_error(X) :-
    log(error, 'plspec raised an error that is unhandled.', []),
    log(error, '~w.', [X]).

pretty_print_error(fail(postcondition_violated(matched_pre(Pre),
                                               violated_post(Post),
                                               value(Val)))) :-
    log(' a postcondition was violated!', []),
    log(' the matched precondition was "~w"', [Pre]),
    log(' however, the postcondition "~w" does not hold', [Post]),
    log(' the offending value was: ~w', [Val]).
pretty_print_error(fail(prespec_violated(specs(PreSpecs), values(Vals),
                                         location(Functor)))) :-
    log(' no precondition was matched in ~w', [Functor]),
    log(' specified preconditions were: ~w', [PreSpecs]),
    log(' however, none of these is matched by: ~w', [Vals]).
pretty_print_error(fail(spec_violated(spec(T), value(V), location(Location)))) :-
    log(' an invariant was violated in ~w', [Location]),
    log(' the spec was: ~w', [T]),
    log(' however, the value was bound to: ~w', [V]).
pretty_print_error(fail(spec_not_found(spec(Spec)))) :-
    %% TODO: not all failures include a location
    log(' spec "~w" was not found', [Spec]).
pretty_print_error(fail(spec_not_found(spec(Spec), location(Location)))) :-
    log(' a spec for ~w was not found', [Location]),
    log(' spec "~w" was not found', [Spec]).
pretty_print_error(X) :-
    log(' plspec raised an error that is unhandled.', []),
    log(' ~w.', [X]).
