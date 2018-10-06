:-module(static_analyzer,[analyze_source/2]).
:- use_module(library(pprint)).
:- use_module(plspec_logger,[log/3,log/2,set_loglevel/1]).
:- use_module(spec_domains,[simplify_and/2, type_of/2]).

:- set_loglevel(error).
analyze_source(Src,Res) :-
    prolog_canonical_source(Src,CanSrc),
    prolog_open_source(CanSrc,Stream),
    preprocess_source(Stream,Terms),
    create_lobby(LobbyIn),
    process_source(Terms,LobbyIn,LobbyBetween),
    lobby_to_list(LobbyBetween, LobbyList),
    simplify_lobby_list(LobbyList,LobbyOut),
    analyze_domains(LobbyOut,Res),
    clean_up.

clean_up :-
    retractall(asserted_spec_pre(_,_,_)).

create_lobby(Lobby) :-
    empty_assoc(Lobby), !.
    %empty_assoc(Lobby1),
    %empty_assoc(Pre),
    %empty_assoc(Post),
    %empty_assoc(Inv),
    %put_assoc(pre,Lobby1,Pre,Lobby2),
    %put_assoc(post,Lobby2,Post,Lobby3),
    %put_assoc(inv,Lobby3,Inv,Lobby).

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
    collect_pre_specs(A,StateIn,State2), % initial pre specs
    % gehe durch den Body und checke, ob die Pre Specs ok sind
    body_to_list(B,Body),
    analyze_body(Body,State2,StateOut).

analyze_body([],State,State) :- !.
analyze_body([H|T],StateIn,StateOut) :-
    % Berechne State mit Pre Bedingung
    collect_pre_specs(H,StateIn,State2),
    % Überprüfe, ob der StateIn eine Pre Bedingung erfüllt.
    valid_state(State2),
    % Berechne den State nach dem Call
    interfere_domain_after_call(H,State2,State3),
    % Mache weiter mit dem Rest
    valid_state(State3),
    analyze_body(T,State3,StateOut).


valid_state(_State) :-
    true.

body_to_list((B,C),[B|T]) :- !,
    body_to_list(C,T).
body_to_list((C),[C]) :- !.


interfere_domain_after_call(Goal,EnvIn,EnvOut) :-
    Goal =.. [_|Args],
    length(Args,Size),
    find_specs_to_goal(Goal,SpecsFound,Size),
    maplist(replace_var_through_any,SpecsFound,Specs),
    create_empty_value_if_not_exists(Args,EnvIn,EnvWorking),
    get_assoc(Args,EnvWorking,OldDomain,Env2,NewDomain),
    simplify_and([one_of(Specs)|OldDomain],NewDomain),
    assoc_single_values(Args,Specs,Env2,EnvOut).

collect_pre_specs(Goal,EnvIn,EnvOut) :-
    Goal =.. [_|Args],
    length(Args,Size),
    find_specs_to_goal(Goal,Specs,Size),
    create_empty_value_if_not_exists(Args,EnvIn,EnvWorking),
    get_assoc(Args,EnvWorking,OldDomain,Env2,NewDomain),
    simplify_and([one_of(Specs)|OldDomain],NewDomain),
    assoc_single_values(Args,Specs,Env2,EnvOut).

create_list_of(_,0,[]) :- !.
create_list_of(A,Size,[A|L]) :-
    N is Size-1,
    create_list_of(A,N,L).

find_specs_to_goal(Goal,Specs) :-
    Goal =.. [_|Args],
    length(Args,Size),
    find_specs_to_goal(Goal,Specs,Size).

find_specs_to_goal(Goal,Specs,_) :-
    name_with_module(Goal,user:(is)/2),!,
    Specs = [[number,number],[var,number]].
find_specs_to_goal(Goal,Specs,Size) :-
    name_with_module(Goal,FullName),!,
    (setof(Spec,asserted_spec_pre(FullName,Spec,_),Specs)
     -> true
     ;  create_list_of(any,Size,L),
        Specs = [L]).

find_spec_and_transform(FullName,Spec) :-
    asserted_spec_pre(FullName,SpecFound,_),
    replace_var_through_any(SpecFound,Spec).

replace_var_through_any([],[]) :- !.
replace_var_through_any([var|T],[any|R]) :-
    !, replace_var_through_any(T,R).
replace_var_through_any([H|T],[H|R]) :-
    replace_var_through_any(T,R).


create_empty_value_if_not_exists(Key,Assoc,Assoc) :-
    get_assoc(Key,Assoc,_), !.
create_empty_value_if_not_exists(Key,Assoc,NewAssoc) :-
    put_assoc(Key,Assoc,[],NewAssoc).

assoc_single_values([],_,Env,Env) :- !.
assoc_single_values([H|Args],Specs,EnvIn,EnvOut) :-
    maplist(nth0(0),Specs,SpecsForH,RestSpecs),
    create_empty_value_if_not_exists(H,EnvIn,EnvWorking),
    get_assoc(H,EnvWorking,OldDomain,EnvWorking2,NewDomain),
    simplify_and([one_of(SpecsForH)|OldDomain],NewDomain),
    assoc_single_values(Args,RestSpecs,EnvWorking2,EnvOut).


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
    simplify_list(V,NewV1),
    simplify_and(NewV1,NewV),
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

