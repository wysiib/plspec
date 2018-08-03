:- module(plspec_checker,
            %plspec predicates
           [enable_all_spec_checks/0,
            spec_pre/2, spec_post/3, spec_invariant/2,
            defspec/2, defspec_pred/2,
            defspec_pred_recursive/4, defspec_connective/4,
            %validator predicates:
            valid/2,
            %logger
            set_loglevel/1, log/3,
            %multifile:
            asserted_spec_pre/3, asserted_spec_invariant/3,
            asserted_spec_invariant/4, asserted_spec_post/5,
            check_predicate/1
            ]).
:- use_module(plspec).
:- use_module(validator).
:- use_module(logger).

expansion(Head,Goal,PreSpecs,InvariantSpecOrEmpty,PrePostSpecs,PostSpecs,NewHead,NewBody) :-
  Head =.. [Functor|Args],
  length(Args, Lenny),
  %% newargs: only relevant if head implements pattern matching:
  % consider foo(foo). then the call 'foo(bar)' would not violate the spec but only fail
  % thus, we insert a fresh variable and check the unification with the argument term later on
  length(NewArgs, Lenny),
  NewHead =.. [Functor|NewArgs],
  NewBody = (% determine if at least one precondition is fulfilled
              (PreSpecs = []
                  -> true
                  ;  (plspec:plspec_some(spec_matches(NewArgs, true), PreSpecs)
                      -> true
                      ; plspec:error_not_matching_any_pre(Functor/Lenny, NewArgs, PreSpecs))),
              (InvariantSpecOrEmpty = [InvariantSpec]
                  -> lists:maplist(plspec:setup_uber_check(Functor/Lenny),InvariantSpec,NewArgs)
                  ; true),
               % unify with pattern matching of head
              NewArgs = Args,
              % gather all matching postconditions
              plspec:which_posts(PrePostSpecs,PostSpecs,Args,ValidPrePostSpecs,PostsToCheck),
              Goal,
              lists:maplist(plspec:check_posts(Args),ValidPrePostSpecs,PostsToCheck)).

should_expand(A, F, Module, Arity) :-
  functor(A,F,Arity),
  %trace,
  (plspec:asserted_spec_pre(Module:F/Arity, _, _) ;
   plspec:asserted_spec_invariant(Module:F/Arity, _, _) ;
   plspec:asserted_spec_post(Module:F/Arity, _, _, _, _)
  ), !,
  plspec:check_predicate(F/Arity).

expandeur(':-'(A, B), Module, ':-'(NA, NB)) :-
  should_expand(A, F, Module, Arity), !,
  findall(PreSpec, plspec:asserted_spec_pre(Module:F/Arity,PreSpec, _TypePre), PreSpecs),
  findall(InvSpec, plspec:asserted_spec_invariant(Module:F/Arity,InvSpec, _TypeInv),InvariantSpecOrEmpty),
  findall(PreSpec2,plspec:asserted_spec_post(Module:F/Arity,PreSpec2,_,_TypePre2,_),PrePostSpecs),
  findall(PostSpec,plspec:asserted_spec_post(Module:F/Arity,_,PostSpec,_,_TypePost),PostSpecs),
  expansion(A,B,PreSpecs,InvariantSpecOrEmpty,PrePostSpecs,PostSpecs,NA,NB).

do_expand(':-'(spec_pre(Predicate/Arity, Spec)),
          Module,
          ':-'(spec_pre(Module:Predicate/Arity, Spec))).

do_expand(':-'(spec_invariant(Predicate/Arity, Spec)),
          Module,
          ':-'(spec_invariant(Module:Predicate/Arity, Spec))).

do_expand(':-'(spec_post(Predicate/Arity, SpecPre, SpecPost)),
          Module,
          ':-'(spec_post(Module:Predicate/Arity, SpecPre, SpecPost))).

do_expand(':-'(plspec:spec_pre(Predicate/Arity, Spec)),
          Module,
          ':-'(plspec:spec_pre(Module:Predicate/Arity, Spec))).

do_expand(':-'(plspec:spec_invariant(Predicate/Arity, Spec)),
          Module,
          ':-'(plspec:spec_invariant(Module:Predicate/Arity, Spec))).

do_expand(':-'(plspec:spec_post(Predicate/Arity, SpecPre, SpecPost)),
          Module,
          ':-'(plspec:spec_post(Module:Predicate/Arity, SpecPre, SpecPost))).

do_expand(':-'(A, B), Module, ':-'(NA, NB)) :-
  log(debug,'do_expand of ~w',[':-'(A, B)]),
  expandeur(':-'(A, B), Module, ':-'(NA, NB)).
do_expand(A, Module, ':-'(NA, NB)) :-
  log(debug,'do_expand of ~w',[A]),
  expandeur(':-'(A, true), Module, ':-'(NA, NB)).
do_expand(A, _Module, A).

:- multifile term_expansion/2.
user:term_expansion(A, B) :-
  log(debug,'term-expansion SWI of ~w', [A]),
  prolog_load_context(module, Module),
  do_expand(A, Module, B).

:- multifile user:term_expansion/6.
user:term_expansion(Term1, Layout1, Ids, Term2, Layout1, [plspec_token|Ids]) :-
  log(debug,'term-expansion SICTUS of ~w', [Term1]),
  nonmember(plspec_token, Ids),
  prolog_load_context(module, Module),
  do_expand(Term1, Module, Term2).
