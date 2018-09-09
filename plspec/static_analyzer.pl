:-module(static_analyzer,[analyze_source/1]).
:- use_module(library(pprint)).

analyze_source(Src,LobbyOut) :-
    process_source(Src,process_directs),
    empty_assoc(LobbyIn),
    process_source(Src,abs_int(LobbyIn,LobbyOut)).

process_source(Src,Goal) :-
    prolog_canonical_source(Src,CanSrc),
    prolog_open_source(CanSrc,In),
    Goal =.. [Name|Args],
    ProcessAsList = [Name,In|Args],
    Process =.. ProcessAsList,
    call_cleanup(Process,prolog_close_source(In)).


process_directs(Stream) :-
    prolog_read_source_term(Stream,Term,Expanded,[]),!,
    (Term = end_of_file
     ->
         true
     ;
         execute_directs(Expanded),!,
         process_directs(Stream)).

execute_directs(':-'(A)) :-
    !,call(A).
execute_directs(_) :- !.

abs_int(Stream,LobbyIn,LobbyOut) :-
    prolog_read_source_term(Stream,Term,Expanded,[]),!,
    (Term = end_of_file
     ->
         LobbyIn = LobbyOut
     ;
         empty_assoc(EnvIn),
         analyze_term(Expanded,EnvIn,EnvOut),!,
         put_assoc(Expanded,LobbyIn,EnvOut,LobbyBetween),
         abs_int(Stream,LobbyBetween,LobbyOut)).

find_specs_to_goal(Goal,Specs) :-
    name_with_module(Goal,FullName),
    findall(Spec,asserted_spec_pre(FullName,Spec,_),Specs).

write_condition(Goal,EnvIn,EnvOut) :-
    Goal =.. [_|Args],
    create_empty_value_if_not_exists(Args,EnvIn,EnvWorking),
    find_specs_to_goal(Goal,Specs),
    get_assoc(Args,EnvWorking,L,Env2,[one_of(Specs)|L]),
    assoc_single_values(Args,Specs,Env2,EnvOut).


create_empty_value_if_not_exists(Key,Assoc,Assoc) :-
    get_assoc(Key,Assoc,_), !.
create_empty_value_if_not_exists(Key,Assoc,NewAssoc) :-
    put_assoc(Key,Assoc,[],NewAssoc).

assoc_single_values([],_,Env,Env) :- !.
assoc_single_values([H|Args],Specs,EnvIn,EnvOut) :-
    maplist(nth0(0),Specs,SpecsForH),
    create_empty_value_if_not_exists(H,EnvIn,EnvWorking),
    get_assoc(H,EnvWorking,L,EnvWorking2,[one_of(SpecsForH)|L]),
    assoc_single_values(Args,Specs,EnvWorking2,EnvOut).


analyze_term(':-'(_),StateIn,StateIn) :- !.
analyze_term(':-'(A,B),StateIn,StateOut) :-
    write_condition(A,StateIn,State2),
    analyze_body(B,State2,StateOut),
    assoc_to_list(StateOut,Res),
    write(A), write(": "), write(Res), nl, nl.

analyze_body((B,C),In,Out) :- !,
    write_condition(B,In,Between),
    analyze_body(C,Between,Out).
analyze_body((C),In,Out) :-
    write_condition(C,In,Out).


name_with_module(Compound,FullName) :-
    Compound =.. [Name|Args],
    length(Args,Arity),
    prolog_load_context(module,Module),
    FullName = Module:Name/Arity.

do_expand(
        ':-'(spec_pre(Predicate/Arity, Spec)),
        Module,
        ':-'(spec_pre(Module:Predicate/Arity, Spec))).
do_expand(
        ':-'(spec_invariant(Predicate/Arity, Spec)),
        Module,
        ':-'(spec_invariant(Module:Predicate/Arity, Spec))).
do_expand(
        ':-'(spec_post(Predicate/Arity, SpecPre, SpecPost)),
        Module,
        ':-'(spec_post(Module:Predicate/Arity, SpecPre, SpecPost))).
do_expand(
        ':-'(plspec:spec_pre(Predicate/Arity, Spec)),
        Module,
        ':-'(plspec:spec_pre(Module:Predicate/Arity, Spec))).
do_expand(
        ':-'(plspec:spec_invariant(Predicate/Arity, Spec)),
        Module,
        ':-'(plspec:spec_invariant(Module:Predicate/Arity, Spec))).
do_expand(
        ':-'(plspec:spec_post(Predicate/Arity, SpecPre, SpecPost)),
        Module,
        ':-'(plspec:spec_post(Module:Predicate/Arity, SpecPre, SpecPost))).
do_expand(A,_,A) :- !.
 
:- multifile term_expansion/2.
user:term_expansion(A, B) :-
    prolog_load_context(module, Module),
    do_expand(A, Module, B).

what_is_B((B,C)) :- !,
    write("Y: "),write(B),nl,
    what_is_B(C).
what_is_B((B)) :-
   write("B: "), write(B),nl.
