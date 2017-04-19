:- use_module(plspec, [valid/2]).
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

infer_spec(DataList, PossibleSpec) :-
    maplist(possible_specs, DataList, AllPossibleSpecs),
    find_smallest_spec_subset(AllPossibleSpecs, SpecList),
    merge_specs(SpecList, PossibleSpec).

