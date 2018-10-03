:-module(static_analyzer,[analyze_source/2]).
:- use_module(library(pprint)).

analyze_source(Src,Res) :-
    empty_assoc(LobbyIn),
    prolog_canonical_source(Src,CanSrc),
    prolog_open_source(CanSrc,Stream),
    preprocess_source(Stream,Terms),
    process_source(Terms,LobbyIn,LobbyBetween),
    lobby_to_list(LobbyBetween, LobbyList),
    simplify_lobby_list(LobbyList,LobbyOut),
    analyze_domains(LobbyOut,Res).

preprocess_source(Stream, Out) :-
    prolog_read_source_term(Stream, Term, Expanded, []),
    (Term = end_of_file -> Out = []
     ; (Expanded = ':-'(A) -> call(A), Out = Next ; Out = [Expanded|Next]), preprocess_source(Stream,Next)).

process_source([],Lobby,Lobby) :- !.
process_source([Expanded|Terms],LobbyIn,LobbyOut) :-
      process_term(Expanded,LobbyIn,LobbyBetween),
      process_source(Terms,LobbyBetween,LobbyOut).

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
    length(Args,Size),
    find_specs_to_goal(Goal,Specs,Size),
    create_empty_value_if_not_exists(Args,EnvIn,EnvWorking),
    get_assoc(Args,EnvWorking,L,Env2,[one_of(Specs)|L]),
    assoc_single_values(Args,Specs,Env2,EnvOut).
     

create_list_of(_,0,[]) :- !.
create_list_of(A,Size,[A|L]) :-
    N is Size-1,
    create_list_of(A,N,L).

find_specs_to_goal(Goal,Specs,_) :-
    name_with_module(Goal,user:(is)/2),!,
    Specs = [[number,number]].
find_specs_to_goal(Goal,Specs,Size) :-
    name_with_module(Goal,FullName),!,
    (setof(Spec,asserted_spec_pre(FullName,Spec,_),Specs)
     -> true
     ;  create_list_of(any,Size,L),
        Specs = [L]).

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

list_to_lobby(List,Lobby) :-
    list_to_lobby_inner(List,Step1),
    list_to_assoc(Step1,Lobby).

list_to_lobby_inner([],[]) :-!.
list_to_lobby_inner([K-V|T],[K-Assoc|Res]) :-
    list_to_assoc(V,Assoc),
    list_to_lobby_inner(T,Res).

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
    check_if_key_is_var(K),!,
    simplify_list(V,NewV),
    simplify_env(EnvIn,EnvOut).
simplify_env([_-_|EnvIn],EnvOut) :-
    simplify_env(EnvIn,EnvOut).

check_if_key_is_var(K) :-
    is_list(K),!,
    foreach(member(X,K),var(X)).
check_if_key_is_var(K) :-
    var(K).

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

% analyze and calculate the domains of the predicates
analyze_domains(LobbyAsList,Res) :-
    Res = LobbyAsList.


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

