process_source(Src) :-
    prolog_canonical_source(Src,CanSrc),
    prolog_open_source(CanSrc,In),
    call_cleanup(process(In), prolog_close_source(In)).



process(Stream) :-
    prolog_read_source_term(Stream,Term,Expanded,[]),!,
    (Term = end_of_file
     ->
         true
     ;
         interpret(Expanded),
         process(Stream)).

interpret(':-'(A)) :-
    write(A),nl,
    call(A), !.
interpret(':-'(A,B)) :-
    write(A),write(" :- "),nl, !,
    what_is_B(B),nl.

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
