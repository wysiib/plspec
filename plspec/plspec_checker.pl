:- module(plspec_checker, []).
:- use_module(plspec).

expansion(Head,Goal,PreSpecs,InvariantSpecOrEmpty,PrePostSpecs,PostSpecs,NewHead,NewBody) :-
    Head =.. [Functor|Args],
    length(Args, Lenny),
    %% newargs: only relevant if head implements pattern matching:
    % consider foo(foo). then the call 'foo(bar)' would not violate the spec but only fail
    % thus, we insert a fresh variable and check the unification with the argument term later on
    length(NewArgs, Lenny),
    NewHead =.. [Functor|NewArgs],
    NewBody = (% determine if at least one precondition is fulfilled
               (PreSpecs = [] -> true ; (plspec:plspec_some(spec_matches(NewArgs, true), PreSpecs) -> true ; plspec:error_not_matching_any_pre(Functor, NewArgs, PreSpecs))),
               (InvariantSpecOrEmpty = [InvariantSpec] -> lists:maplist(plspec:setup_uber_check(pred_specs_args(Head, InvariantSpec, Args)),InvariantSpec,Args) ; true), 
               % unify with pattern matching of head
               NewArgs = Args,
               % gather all matching postconditions
               plspec:which_posts(PrePostSpecs,PostSpecs,Args,ValidPrePostSpecs,PostsToCheck),
               Goal,
               lists:maplist(plspec:check_posts(Args),ValidPrePostSpecs,PostsToCheck)).

should_expand(A, F, Arity) :-
    functor(A,F,Arity),
    %trace,
    (plspec:le_spec_pre(F/Arity, _) ; plspec:le_spec_invariant(F/Arity, _) ; plspec:le_spec_post(F/Arity, _, _)), !,
    plspec:check_predicate(F/Arity).

expandeur(':-'(A, B), ':-'(NA, NB)) :-
    should_expand(A, F, Arity), !,
    findall(PreSpec, plspec:le_spec_pre(F/Arity,PreSpec), PreSpecs),
    findall(InvSpec, plspec:le_spec_invariant(F/Arity,InvSpec),InvariantSpecOrEmpty),
    findall(PreSpec2,plspec:le_spec_post(F/Arity,PreSpec2,_),PrePostSpecs),
    findall(PostSpec,plspec:le_spec_post(F/Arity,_,PostSpec),PostSpecs),
    expansion(A,B,PreSpecs,InvariantSpecOrEmpty,PrePostSpecs,PostSpecs,NA,NB).

do_expand(':-'(A, B), ':-'(NA, NB)) :-
    expandeur(':-'(A, B), ':-'(NA, NB)).
do_expand(A, ':-'(NA, NB)) :-
    expandeur(':-'(A, true), ':-'(NA, NB)).
do_expand(A,A).

:- multifile term_expansion/2.
user:term_expansion(A, B) :-
    do_expand(A,B).

:- multifile user:term_expansion/6.
user:term_expansion(Term1, Layout1, Ids, Term2, Layout1, [plspec_token|Ids]) :-
    nonmember(plspec_token, Ids),
    do_expand(Term1, Term2).
