:- use_module(plspec).
:- use_module(library(lists), [exclude/3]).

% TODO: possible specs of [] are list(_)
possible_specs(Data, ListOfSpecs) :-
    findall(Spec, valid(Spec, Data), ListOfSpecs).


find_smallest_spec_subset(ListOfSpecLists, SmallSpecList) :-
    find_smallest_spec_subset_aux(ListOfSpecLists, 1, SmallSpecList).

% this is stupid and probably very slow but might work
% thus, it is not stupid but still very slow
% :-(
find_smallest_spec_subset_aux(ListOfSpecLists, N, SmallSpecList) :-
    length(SmallSpecList, N),
    iterate_specs(ListOfSpecLists, SmallSpecList).
find_smallest_spec_subset_aux(ListOfSpecLists, N, SmallSpecList) :-
    %% if N specs are not enough, try N + 1 specs
    N1 is N + 1,
    length(ListOfSpecLists, M),
    %  but only if we have at most N + 1 items
    M >= N1,
    find_smallest_spec_subset_aux(ListOfSpecLists, N1, SmallSpecList).


iterate_specs([], []).
iterate_specs([HSpecList|TSpecLists], [HResSpec|TResSpecs]) :-
    % find a spec that matches the first element
    member(HResSpec, HSpecList),
    % remove all elements that match the same spec
    exclude(member(HResSpec), TSpecLists, RestSpecLists),
    % repeat with all element that are not matched yet
    iterate_specs(RestSpecLists, TResSpecs).

% TODO: implement this
merge_specs(_AllPossibleSpecs, InferredSpec) :-
    InferredSpec = any.


merge_spec_list([H|T], InferredSpec) :-
    merge_spec_list(T, H, InferredSpec).
merge_spec_list([], Acc, Acc).
merge_spec_list([H|T], Acc, Res) :-
    merge_two_specs(Acc, H, NewAcc),
    merge_spec_list(T, NewAcc, Res).

:- use_module(library(ordsets)).

    % TODO:
    % one_of([list(one_of([list(any), integer])),
    %         integer])
    % as accumulator
    % and list(integer) as value
contains_spec(X, X).
contains_spec(one_of(Set), Spec) :-
    spec_exists(Spec, predicate(_)), !,
    member(Spec, Set).
contains_spec(one_of(SpecSet),Spec) :-
    get_spec_with_variables(Spec, SpecWithVariables),
    copy_term(SpecWithVariables, SpecWithVariables2),
    term_variables(SpecWithVariables, Vars1),
    term_variables(SpecWithVariables2, Vars2),
    member(SpecWithVariables, SpecSet),
    SpecWithVariables2 = Spec,
    maplist(contains_spec, Vars1, Vars2).
contains_spec(Spec1, Spec2) :-
    trace,
    get_spec_with_variables(Spec2, SpecWithVariables2),
    copy_term(SpecWithVariables2, SpecWithVariables1),
    term_variables(SpecWithVariables1, Vars1),
    term_variables(SpecWithVariables2, Vars2),
    SpecWithVariables2 = Spec2,
    SpecWithVariables1 = Spec1,
    maplist(contains_spec, Vars1, Vars2).

:- begin_tests(contains_spec).

test(simple_contained) :-
    contains_spec(integer, integer).

test(contained1) :-
    contains_spec(one_of([atom, integer]), integer).

test(contained2) :-
    contains_spec(one_of([atom, integer]), atom).

test(not_contained) :-
    \+ contains_spec(one_of([atom, integer]), atomic).

test(hard_contained) :-
    trace,
    contains_spec(one_of([list(one_of([integer, atom]))]), list(integer)).

%% TODO: tests with more than one variable
% e.g. compound, tuple, ...


:- end_tests(contains_spec).

merge_two_specs(X, X, X).
merge_two_specs(one_of(SpecSet), Spec, one_of(SpecSet)) :-
    contains_spec(SpecSet, Spec).
merge_two_specs(one_of(Set), Spec, one_of(NewSet)) :-
    % merge in the correct position
    fail.


:- begin_tests(merge_specs).

test(same_spec) :-
    merge_two_specs(integer, integer, X), !,
    X == integer.

test(incompatible_simple) :-
    merge_two_specs(integer, atom, X), !,
    list_to_ord_set([integer, atom], SpecSet),
    X == one_of(SpecSet).

test(incompatible_simple2) :-
    Specs = [integer, compound(foo(integer))],
    merge_two_specs(integer, compound(foo(integer)), X), !,
    list_to_ord_set(Specs, SpecSet),
    X == one_of(SpecSet).

test(somewhat_compatible) :-
    Specs = [compound(foo(integer)), compound(foo(atom))],
    merge_two_specs(compound(foo(integer)), compound(foo(atom)), X), !,
    list_to_ord_set(Specs, SpecSet),
    X == compound(foo(one_of(SpecSet))).

:- end_tests(merge_specs).


infer_spec(DataList, PossibleSpec) :-
    maplist(possible_specs, DataList, AllPossibleSpecs),
    find_smallest_spec_subset(AllPossibleSpecs, SpecList),
    merge_specs(SpecList, PossibleSpec).

