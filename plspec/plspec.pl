:- module(plspec,[spec_pre/2,spec_post/3,
                  setup_check/3,which_pres/4,check_posts/2]).

:- dynamic le_spec_pre/2, le_spec_post/3.

spec_pre(Pred,PreSpec) :-
    assert(le_spec_pre(Pred,PreSpec)).
spec_post(Pred,PreSpec,PostSpec) :-
    assert(le_spec_post(Pred,PreSpec,PostSpec)).

setup_check(Location,A,B) :-
    setup_check_aux(A,Location,B).

setup_check_aux(any,_,_) :- !.
setup_check_aux(Spec,Location,Var) :-
    when(nonvar(Var),check(Spec,Location,Var)).

check([_],_,[]) :- !.
check([X],Location,[H|T]) :- !,
    maplist(setup_check(Location,X),[H|T]).
check(T,Location,V) :-
    throw(['radong','expected',T,'but got',V,'in',Location]).

which_pres([],[],_,[]).
which_pres([Pre|Pres],[Post|Posts],Args,[Post|T]) :-
    maplist(cond_is_true,Pre,Args), !,
    which_pres(Pres,Posts,Args,T).
which_pres([_|Pres],[_|Posts],Args,T) :-
    which_pres(Pres,Posts,Args,T).

check_posts(Args,Posts) :-
    maplist(cond_is_true,Posts,Args), !.
check_posts(_,_) :-
    throw(['radong','postcondition violated']).

cond_is_true(any,_) :- !.
cond_is_true([X],A) :- !,
    nonvar(A),
    maplist(cond_is_true(X),A).
cond_is_true(ground,A) :- !,
    ground(A).
cond_is_true(var,A) :- !,
    var(A).

:- begin_tests(cond_is_true).

test(any) :-
    cond_is_true(any, _),
    cond_is_true(any, 1),
    cond_is_true(any, []),
    cond_is_true(any, foo(_, _)),
    cond_is_true(any, foo).

test(ground) :-
    \+ cond_is_true(ground, _),
    cond_is_true(ground, 1),
    cond_is_true(ground, []),
    \+ cond_is_true(ground, foo(_, _)),
    cond_is_true(ground, foo(1, 2)),
    cond_is_true(ground, foo).

test(list) :-
    \+ cond_is_true([any], _),
    cond_is_true([any], []),
    cond_is_true([any], [a]),
    cond_is_true([any], [1]),
    cond_is_true([any], [_]),
    cond_is_true([any], [[]]),
    cond_is_true([any], [any]).

test(list_of_list) :-
    \+ cond_is_true([[any]], _),
    \+ cond_is_true([[any]], [a]),
    \+ cond_is_true([[any]], [_]),
    cond_is_true([[any]], []),
    cond_is_true([[any]], [[1]]),
    cond_is_true([[any]], [[a]]),
    cond_is_true([[any]], [[]]).

test(compounds) :-
    cond_is_true(foo(any), foo(_)),
    cond_is_true(foo(any), foo(a)),
    \+ cond_is_true(foo(any), bar(a)),
    \+ cond_is_true(foo(any, any), foo(a)),
    cond_is_true(foo(any, any), foo(a, a)),
    \+ cond_is_true(foo(any, var), foo(a, a)).

:- end_tests(cond_is_true).



do_expand((A:-B),(A:-NB)) :-
    expand_body(B,NB).

body_expansion(Body,PreSpec,PreSpecs,PostSpecs,NewBody) :-
    Body =.. [_|Args],
    NewBody = (maplist(plspec:setup_check(Body),PreSpec,Args),
               plspec:which_pres(PreSpecs,PostSpecs,Args,PostsToCheck),
               Body,
               maplist(plspec:check_posts(Args),PostsToCheck)).

expand_body((A,B),(NA,NB)) :- !,
  expand_body(A,NA), expand_body(B,NB).
expand_body({A},{NA}) :- !,
  expand_body(A,NA).
expand_body(A,NA) :-
    functor(A,F,Arity),
    le_spec_pre(F/Arity,PreSpec), !,
    findall(PreSpec,le_spec_post(A,PreSpec,_),PreSpecs),
    findall(PostSpec,le_spec_post(A,_,PostSpec),PostSpecs),
    body_expansion(A,PreSpec,PreSpecs,PostSpecs,NA).
expand_body(A,A).

:- multifile term_expansion/2.
user:term_expansion(A, B) :-
    do_expand(A,B).
