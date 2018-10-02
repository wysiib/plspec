:-module(static_analyzer,[analyze_source/2]).
:- use_module(library(pprint)).

analyze_source(Src,LobbyOut) :-
    empty_assoc(LobbyIn),
    prolog_canonical_source(Src,CanSrc),
    prolog_open_source(CanSrc,Stream),
    process_source(Stream,LobbyIn,LobbyBetween),
    lobby_to_list(LobbyBetween, LobbyList),
    simplify_lobby_list(LobbyList,LobbyOut).

process_source(Stream,LobbyIn,LobbyOut) :-
    prolog_read_source_term(Stream, Term, Expanded, []), !,
    (Term = end_of_file
     ->
         LobbyIn = LobbyOut
     ;
         process_term(Expanded,LobbyIn,LobbyBetween),
         process_source(Stream,LobbyBetween,LobbyOut)
    ).

process_term(':-'(A),Lobby,Lobby) :-
    !, call(A).
process_term(Expanded,LobbyIn,LobbyOut) :-
    empty_assoc(EnvIn),
    analyze_term(Expanded,EnvIn,EnvOut),!,
    put_assoc(Expanded,LobbyIn,EnvOut,LobbyOut).

analyze_term(':-'(A,B),StateIn,StateOut) :-
    write_condition(A,StateIn,State2),
    analyze_body(B,State2,StateOut).

analyze_body((B,C),In,Out) :-
    !,
    write_condition(B,In,Between),
    analyze_body(C,Between,Out).
analyze_body((C),In,Out) :-

    write_condition(C,In,Out).

write_condition(Goal,EnvIn,EnvOut) :-
    Goal =.. [_|Args],
    create_empty_value_if_not_exists(Args,EnvIn,EnvWorking),
    find_specs_to_goal(Goal,Specs),
    get_assoc(Args,EnvWorking,L,Env2,[one_of(Specs)|L]),
    assoc_single_values(Args,Specs,Env2,EnvOut).


find_specs_to_goal(Goal,Specs) :-
    name_with_module(Goal,FullName),!,
    findall(Spec,asserted_spec_pre(FullName,Spec,_),Specs).


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


name_with_module(Compound,FullName) :-
    Compound =.. [Name|Args],
    length(Args,Arity),
    prolog_load_context(module,Module),
    FullName = Module:Name/Arity.

lobby_to_list(Lobby,List) :-
    assoc_to_list(Lobby,LobbyAsList),
    env_to_list(LobbyAsList,List).

env_to_list([],[]) :- !.
env_to_list([K-V|T],[K-W|S]) :-
    assoc_to_list(V,W),
    env_to_list(T,S).

simplify_lobby_list([],[]) :- !.
simplify_lobby_list([K-Env|T],[K-EnvNew|TT]) :-
    simplify_env(Env,EnvNew),
    simplify_lobby_list(T,TT).

simplify_env([],[]) :- !.
simplify_env([K-V|EnvIn],[K-NewV|EnvOut]) :-
    simplify_list(V,NewV),
    simplify_env(EnvIn,EnvOut).

simplify_list([],[]) :- !.
simplify_list([one_of([])|T],Res) :-
    !,
    simplify_list(T,Res).
simplify_list([one_of(L)|T],[one_of(S)|Res]) :-
    list_to_set(L,S),
    simplify_list(T,Res).


pretty_print_lobby([]) :- !.
pretty_print_lobby([Term-Env|T]) :-
    write("... "), write(Term), write(""), nl,
    pretty_print_env(Env),
    pretty_print_lobby(T).

pretty_print_env([]) :- !.
pretty_print_env([K-V|T]) :-
    write("         "), write(K), write(" :    "), write(V),nl,
    pretty_print_env(T).
 
% expand needed to write module name in front of predicate
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

