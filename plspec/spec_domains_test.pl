:- module(spec_domains_test,[]).
:- use_module(spec_domains).
:- use_module(plspec).
:- use_module(library(plunit)).

:- assert(spec_domains:child_parent(b,a)).
:- assert(spec_domains:child_parent(c,a)).
:- assert(spec_domains:child_parent(d,b)).
:- assert(spec_domains:child_parent(e,b)).
:- assert(spec_domains:child_parent(f,c)).
:- assert(spec_domains:child_parent(g,c)).
:- assert(spec_domains:child_parent(h,d)).
:- assert(spec_domains:child_parent(i,d)).
:- assert(spec_domains:child_parent(j,e)).
:- assert(spec_domains:child_parent(k,e)).
:- assert(spec_domains:child_parent(l,f)).
:- assert(spec_domains:child_parent(m,f)).


:- begin_tests(ancestor).

test(ancestor) :-
    spec_domains:ancestor(a,b),
    spec_domains:ancestor(a,c),
    spec_domains:ancestor(a,d),
    spec_domains:ancestor(a,e),
    spec_domains:ancestor(a,f),
    spec_domains:ancestor(a,g),
    spec_domains:ancestor(a,h),
    spec_domains:ancestor(a,i),
    spec_domains:ancestor(a,j),
    spec_domains:ancestor(a,k),
    spec_domains:ancestor(a,l),
    spec_domains:ancestor(a,m).

test(descendant) :-
    spec_domains:descendant(b,a),
    spec_domains:descendant(c,a),
    spec_domains:descendant(d,a),
    spec_domains:descendant(e,a),
    spec_domains:descendant(f,a),
    spec_domains:descendant(g,a),
    spec_domains:descendant(h,a),
    spec_domains:descendant(i,a),
    spec_domains:descendant(j,a),
    spec_domains:descendant(k,a),
    spec_domains:descendant(l,a),
    spec_domains:descendant(m,a).

:- end_tests(ancestor).

:- begin_tests(set_operations).

test(union) :-
    union(g,a,a),
    union(h,b,b),
    union(j,l,one_of([j,l])),
    union(b,c,one_of([b,c])),
    union(a,empty,a),
    union(empty,empty,empty),
    union(f,f,f).

test(intersect) :-
    intersect(f,a,f),
    intersect(a,f,f),
    intersect(b,h,h),
    intersect(b,f,empty),
    intersect(a,empty,empty),
    intersect(a,a,a),
    intersect(empty,a,empty).

:- end_tests(set_operations).

:- begin_tests(simplify_single_domain).

test(simplify_and1) :-
    spec_domains:simplify_and([one_of([b,b,c]), one_of([e])], [one_of([e])]).

test(simplify_and2) :-
    spec_domains:simplify_and([one_of([d,e,f,g]), one_of([h,i])], [one_of(L)]),
    sort(L,[h,i]).

test(simplify_everything_away) :-
    spec_domains:simplify_and([one_of([l,m]), one_of([d,e]), one_of([c])], []).

:- end_tests(simplify_single_domain).
