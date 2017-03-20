# plspec

Inspired by [clojure.spec](https://clojure.org/about/spec), *plspec* aims to provide similar support for describing valid data.

## Get started

Specs always have to be written somewhere above the predicate (because of term expansion magic).
You can annotate your predicate like this:

```
:- spec_pre(member/2,[any,any]). % mandatory
:- spec_invariant(member/2,[any,list(any)]).
:- spec_post(member/2,[any,var],[any,list(any)]).
member(E,[E|_]).
member(E,[_|T]) :-
    member(E,T).
```
    
But what does all of that mean? Let's look at the semantics in more detail:


### spec_pre/2

At least one `spec_pre/2` is mandatory right now.
In order to define a valid call to your predicate, the arguments have to match at least one of the specifiations in `spec_pre/2`.

In the example above, we have `spec_pre(member/2,[any,any]).`
This means that we annotate a predicate named `member` of arity 2.
Both arguments are specified to be of `any` type, i.e. every single call is a valid call.

If a call is not valid, you'll get an exception. Basically, this describes a precondition.


### spec_invariant/2

You may optionally call `spec_invariant/2`.
`spec_invariant/2` checks *your* code.
If variables are bound to values, they still have to be able to unify with a value of the given type.

In our example, we call `spec_invariant(member/2,[any,list(any)]).`
We do not care about the first argument and specify `any` for it.
For the second argument, however, we say that *if* the value is bound, it has to become a list (of any type).
Let's consider some values:

* `_`, the anonymous variable, is always a valid value.
* `[_|_]` is a valid value for any list of any type.
* `[1|_]` is okay for a list of any type or a list of integers. If we specified a list of atoms, we would throw an exception.
* `[_|a]` is not okay for a list. An exception will be thrown.
* `[]`, the empty list, always is a valid list of any type.

If you choose not to bind the variable in your predicate, an exception will be thrown even when the caller decides to bind the variable to a disallowed type later on. Neat, huh?


### spec_post/3

Let's take a look at `spec_post/3`.
You can have as many as you want of these.
Aside from the predicate it references, this one actually takes two specs.
The first spec acts somewhat as a guard.
If the first spec was true when the predicate was called, the second spec has to hold when the predicate succeeds (*if* it succeeds, that is).

In the example, we can see `spec_post(member/2,[any,var],[any,list(any)]).`.
The promise you make here is that if the second argument was a variable and `member/2` succeeds, the second variable will become a list. Otherwise, you guessed it, you get an exception.


### built-ins specs

We have implemented a couple of specs:

* `any` allows any value
* `integer` (or `int` for short) allows integer values
* `number` allows any kind of numbers
* `var` allows variables
* `ground` allows ground values (be careful if you use it in an invariant! There, it is equivalent to `any`.)
* `nonvar` allows values which are nonvar (be careful if you use it in an invariant! There, it is equivalent to `any`.)

There are building blocks to construct more complicated specs:

* `compound(X)` allows terms with a given functor and arity, as well as given specs for its arguments. For example, `compound(int_wrapper(int))` will allow `int_wrapper(2)`, but not `int_wrapper(pi)` or `foo(2)`.
* `list(X)` or `[X]` allows homogeneous lists whose members are of type `X`, e.g. `list(int)` only allows integers as members.
* `tuple(X)` allows heterogeneous lists of a fixed length. An example is `tuple([int, atom])` which will accept `[2, foo]`, but neither `[foo, 2]` or `[2, foo, bar]`.
* `and(X)` takes a list `X` of other specs. Valid values have to conform to each of the specs. For example, `and([ground, list(any)])` only allows lists that are ground. 
* `one_of(X)` also takes a list `X` of other specs. Valid values have to conform to at least one of the specs. For example, `one_of([int, atom])` will accept `3` and `foo`, but will not allow `[]`.
