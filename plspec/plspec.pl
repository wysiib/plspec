:- module(plspec,[spec_pre/2,spec_post/3,spec_invariant/2,
                  defspec/2, defspec_pred/2, defspec_pred_recursive/4, defspec_connective/4,
                  setup_uber_check/3,which_posts/5,check_posts/3,
                  plspec_some/2, error_not_matching_any_pre/3,
                  enable_spec_check/1, enable_all_spec_checks/0,
                  spec_set_debug_mode_on/0, spec_set_debug_mode_off/0,
                  debug_format/2,
                  set_error_handler/1,
                  spec_and/4,
                  list/4,
                  valid/2,
                  asserted_spec_pre/2, asserted_spec_invariant/2, asserted_spec_post/3, check_predicate/1 % called by term expander
               ]).

:- use_module(validator).
:- use_module(prettyprinter).

:- use_module(library(terms), [variant/2]).

:- dynamic asserted_spec_pre/2, asserted_spec_invariant/2, asserted_spec_invariant/3, asserted_spec_post/3.

%% set up facts

named_spec(Name:Spec, Name, Spec).

asserted_spec_invariant(Pred, Spec) :-
    asserted_spec_invariant(Pred, _, Spec).

spec_pre(Pred,PreSpec) :-
    (ground(PreSpec)
        -> true
        ; format('plspec: a pre spec should be ground, got ~w in ~w~n', [PreSpec, Pred]), fail),
    (Pred = _:_/Arity),
    (length(PreSpec, Arity)
        -> true
        ; format('plspec: a pre spec of ~w does not match in length~n', [Pred])),
    assert(asserted_spec_pre(Pred,PreSpec)).
spec_invariant(Pred, InvariantSpec) :-
    (ground(InvariantSpec)
        -> true
        ; format('plspec: an invariant spec should be ground, got ~w in ~w~n', [InvariantSpec, Pred]), fail),
    Pred = _:_/Arity,
    (length(InvariantSpec, Arity)
        -> true
        ; format('plspec: invariant spec of ~w does not match in length~n', [Pred])),
    (maplist(named_spec, InvariantSpec, Names, Specs)
        -> assert(asserted_spec_invariant(Pred, Names, Specs))
        ; assert(asserted_spec_invariant(Pred, InvariantSpec))).
spec_post(Pred,PreSpec,PostSpec) :-
    (ground(PreSpec)
        -> true
        ; format('plspec: an post spec should be ground, got ~w in ~w~n', [PreSpec, Pred]), fail),
    (ground(PostSpec)
        -> true
        ; format('plspec: an post spec should be ground, got ~w in ~w~n', [PostSpec, Pred]), fail),
    Pred = _:_/Arity,
    (length(PreSpec, Arity)
        -> true
        ; format('plspec: a post spec (precondition) of ~w does not match in length~n', [Pred])),
    (length(PostSpec, Arity)
        -> true
        ; format('plspec: a post spec (postcondition) of ~w does not match in length~n', [Pred])),
    assert(asserted_spec_post(Pred,PreSpec,PostSpec)).

:- dynamic spec_debug/0.
debug_format(Format, Args) :-
    (spec_debug -> format(Format, Args),nl ; true).

spec_set_debug_mode_on :-
    assert(spec_debug).
spec_set_debug_mode_off :-
    retractall(spec_debug).

defspec(SpecId, OtherSpec) :-
    (spec_exists(SpecId, Existing)
        %% we use variant in order to determine whether it is actually the same spec;
        % for example, consider defspec(foo(X,Y), bar(X,Y)), defspec(foo(X,Y), bar(Y,X)).
        % we do not want to unify X = Y but also notice these are not the same specs.
        -> (variant(spec(SpecId, Existing), spec(SpecId, indirection(OtherSpec)))
            -> debug_format('spec is overwritten with itself, proceeding~n', [SpecId])
            ; format('plspec: spec ~w already exists, will not be redefined~n', [SpecId]))
        ; assert(spec_indirection(SpecId, OtherSpec))).
:- meta_predicate defspec_pred(+, 1).
defspec_pred(SpecId, Predicate) :-
    (spec_exists(SpecId, Existing)
        -> (variant(spec(SpecId, Existing), spec(SpecId, predicate(Predicate)))
            -> debug_format('spec is overwritten with itself, proceeding~n', [SpecId])
            ; format('plspec: spec ~w already exists, will not be redefined~n', [SpecId]))
        ; assert(spec_predicate(SpecId, Predicate))).
:- meta_predicate defspec_pred_recursive(+, 3,3,4).
defspec_pred_recursive(SpecId, Predicate, MergePred, MergePredInvariant) :-
    (spec_exists(SpecId, Existing)
        -> (variant(spec(SpecId, Existing), spec(SpecId, predicate_recursive(Predicate, MergePred, MergePredInvariant)))
            -> debug_format('spec is overwritten with itself, proceeding~n', [SpecId])
            ; format('plspec: spec ~w already exists, will not be redefined~n', [SpecId]))
        ; assert(spec_predicate_recursive(SpecId, Predicate, MergePred, MergePredInvariant))).
:- meta_predicate defspec_connective(+, 3,3,4).
defspec_connective(SpecId, Predicate, MergePred, MergePredInvariant) :-
    (spec_exists(SpecId, Existing)
        -> (variant(spec(SpecId, Existing), spec(SpecId, connective(Predicate, MergePred, MergePredInvariant)))
            -> debug_format('spec is overwritten with itself, proceeding~n', [SpecId]))
            ; format('plspec: spec ~w already exists, will not be redefined~n', [SpecId])
        ; assert(spec_connective(SpecId, Predicate, MergePred, MergePredInvariant))).


:- dynamic check_predicate/1.
enable_spec_check([H|T]) :- !,
    maplist(enable_spec_check, [H|T]).
enable_spec_check(X) :-
    assert(check_predicate(X)).
enable_all_spec_checks :-
    assert(check_predicate(_)).


:- dynamic error_handler/1.
error_handler(plspec_default_error_handler).

:- public plspec_default_error_handler/1.
plspec_default_error_handler(X) :-
    pretty_print_error(X),
    throw(plspec_error).

:- meta_predicate set_error_handler(1).
set_error_handler(Pred) :-
    retractall(error_handler(_)),
    assert(error_handler(Pred)).

%% check coroutine magic
setup_uber_check(Location,Spec,Val) :-
    setup_check(Location,Res,Spec,Val),
    freeze(Res, ((Res == true) -> true ; error_handler(X), call(X, Res))).

setup_check(Location,Res,Spec,Val) :-
    setup_check_aux(Spec,Location,Val,Res).

setup_check_aux(Spec, Location, Val, Res) :-
    spec_predicate(Spec, Pred), !,
    freeze(Val, (call(Pred, Val) -> true ; reason(Spec, Location, Val, Res))).
setup_check_aux(Spec, Location, Val, Res) :-
    spec_indirection(Spec, OtherSpec), !,
    setup_check_aux(OtherSpec, Location, Val, Res).
setup_check_aux(Spec, Location, Val, Res) :-
    spec_predicate_recursive(Spec, Pred, _MergePred, MergePredInvariant), !,
    freeze(Val, (call(Pred, Val, NewSpecs, NewVals)
                    -> call(MergePredInvariant, NewSpecs, NewVals, Location, Res)
                    ;  reason(Spec, Location, Val, Res))).
setup_check_aux(Spec, Location, Val, Res) :-
    spec_connective(Spec, Pred, _MergePred, MergePredInvariant), !,
    freeze(Val, (call(Pred, Val, NewSpecs, NewVals)
                    -> call(MergePredInvariant, NewSpecs, NewVals, Location, Res)
                    ;  reason(Spec, Location, Val, Res))).
setup_check_aux(Spec, Location, _, fail(spec_not_found(spec(Spec), location(Location)))).



reason(T, Location, V, Reason) :-
    copy_term(Location, LocationWithoutAttributes, _Goals),
    Reason = fail(spec_violated(spec(T), value(V), location(LocationWithoutAttributes))).


%% non-coroutine non-magic
which_posts([],[],_,[],[]).
which_posts([Pre|Pres],[Post|Posts],Args,[Pre|PreT],[Post|T]) :-
    maplist(valid,Pre,Args), !,
    which_posts(Pres,Posts,Args,PreT, T).
which_posts([_|Pres],[_|Posts],Args,PreT,T) :-
    which_posts(Pres,Posts,Args,PreT,T).

check_posts([], [], []).
check_posts([Arg|ArgT], [Pre|PreT], [Post|PostT]) :-
    evaluate_spec_match(Post, Arg, Res),
    (Res == true
        -> check_posts(ArgT, PreT, PostT)
         ; error_handler(X),
        call(X, fail(postcondition_violated(matched_pre(Pre), violated_post(Post), value(Arg))))).

%% term expansion
:- meta_predicate plspec_some(1, +).
plspec_some(Goal, List) :-
    plspec_some1(List, Goal).
plspec_some1([], _) :- fail.
plspec_some1([H|_], Goal) :-
    call(Goal,H), !.
plspec_some1([_|T], Goal) :-
    plspec_some1(T, Goal).

:- public spec_matches/3. %THIS SEEMS NOT USED - TO DO: investigate
spec_matches([], true, []).
spec_matches([Arg|ArgsT], Res, [Spec|SpecT]) :-
    evaluate_spec_match(Spec, Arg, R),
    (R == true
    -> spec_matches(ArgsT, Res, SpecT)
    ;  Res = spec_not_matched(Spec, Arg, in(R))).



error_not_matching_any_pre(Functor, Args, PreSpecs) :-
    error_handler(X),
    call(X, fail(prespec_violated(specs(PreSpecs), values(Args), location(Functor)))).

invariand([], [], _, true).
invariand([HSpec|TSpec], [HVal|TVal], Location, R) :-
    setup_check(Location, ResElement,HSpec, HVal),
    freeze(TVal, invariand(TSpec, TVal, Location, ResTail)), % TODO: do we need this freeze?
    both_eventually_true(ResElement, ResTail, R).

:- public and_invariant/4.
and_invariant(Specs, Vals, Location, R) :-
    invariand(Specs, Vals, Location, R).


or_invariant([], [], Acc, OrigVals, OrigPattern, Location, UberVar) :-
    freeze(Acc, (Acc == fail -> (reason(OrigPattern, Location, OrigVals, Reason), UberVar = Reason) ; true)).
or_invariant([H|T], [V|VT], Prior, OrigVals, OrigPattern, Location, UberVar) :-
    setup_check(Location, ResOption, H, V),
    freeze(ResOption, (ResOption == true -> (UberVar = true, Current = true) ; freeze(Prior, (Prior == true -> true; Current = fail)))),
    or_invariant(T, VT, Current, OrigVals, OrigPattern, Location, UberVar).

:- public or_invariant/4.
or_invariant(NewSpecs, NewVals, Location, FutureRes) :-
    or_invariant(NewSpecs, NewVals, [], NewVals, or(NewSpecs), Location, FutureRes).

%% merge recursive specs
both_eventually_true(V1, V2, Res) :-
    when((nonvar(V1); nonvar(V2)),
         (V1 == true
            -> freeze(V2, Res = V2) %% look at the other co-routined variable
            ; nonvar(V1)
                -> Res = V1 %% since it is not true
                ; V2 == true
                    -> freeze(V1, Res = V1)
                    ; nonvar(V2) -> Res = V2)).
