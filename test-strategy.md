<!-- SPDX-FileCopyrightText: Copyright (c) 2022 NVIDIA CORPORATION & AFFILIATES. All rights reserved. -->

# Test Strategy

In order to systematically validate the tool, the following strategy is used:

1. Constrain TLA+ subset, necessary to support intended use cases. Besides that the subset is defined to avoid potentially dangerous, excessive, rarely used syntactic forms
2. Identify required language features and assign identifiers to them
3. Create test cases using pairwise feature combinations. TLA+ language specification [?] has little restrictions on how different features can be combined. However, it seems reasonable to assume that pairwise feature combinations are able to exercise all relevant paths in the tool in a systematic way

The idea is to systematically exercise all language features and their combinations.



## Feature

Feature is an operator, constant, variable or other TLA+ language construct, which is required by the use cases.

Every feature has a type and a kind. This information is needed to create meaningful test cases. Type information is also necessary to create equivalent Apalache test cases, which require type annotations.

### Feature types

The information in this section is not strictly necessary. However, it can help to understand how features combine and specifically why some features cannot be combined.

Types may be either atomic or recursive.

There are three atomic types:
- BoolT
- IntT
- StrT

Recursive types are parameterized with other types (atomic and recursive):
- Def1T - type of definitions of 1-order operators, i.e. operators with at least one argument
- FunT - type of TLA+ functions
- RecordT - type of TLA+ records/structures
- TupleT - type of tuples, i.e. TLA+ sequences, where elements can have different types
- SeqT - type of sequences, i.e. TLA+ sequences, where elements can have different types
- SetT - type of sets
- InDefT - this pseudo type to support different ways, how elements can be picked from a set. InDef is used for functions, sets, CHOOSE and quantifiers. Features of this type has two forms:
    - `x, y \in S` - "choose all possible pairs of values from set S"
    - `<<x, y>> \S` - "S is a set of pairs, choose all such pairs and assign the first element to x and the second to y"

### Feature kinds

TLA+ expressions differ in the context they may appear. This is captured by feature kind:

- Const: constant expressions; they may not reference variables and temporal operators
- State: state expressions; they can reference variables, but cannot reference temporal operators
- Action: action expressions; they can reference variables and can use prime operations, but cannot use any other temporal operators besides prime
- Temporal: temporal expressions; they can reference variables and can use temporal operator ALWAYS `[]`
- Boxed: "boxed" temporal operator with action expression inside
- Nice: conjunction of state, temporal or boxed expressions

For instance, two features Prime and Temporal cannot be combined in a reasonable way.

## Feature pairing

Main principle of test case building is considering all possible pairs of features and:
* creating a test case for every pair, OR
* explain why test case can not be created out of the pair

So feature pair is two features, where their order is important:
* first feature in the pair is called `case`
* second feature is called `plug`

Note that `case` and `plug` are roles, which are determined by order. Let's consider feature `And` and feature `Or`, which represents Boolean operations in TLA+. Four pairs can be build from this two features:
- And + And
- And + Or
- Or + And
- Or + Or

In every such pair, the first feature is `case` and the second is `plug`.

## Generation of test cases

Test cases are created by test generator. Test generator enumerates all possible feature pairs and tries to create test case.

Test case generator normally uses `case` feature to create test case template: a TLA+ specification with slot reserved. This slot is used to insert TLA+ code, produced from `plug` feature.

Some feature pairs may not be used to create test cases. Below exhaustive list of reasons:
- TypeMismatch: types of features do not allow to combine them. E.g. a set can not be combined with function application
- KindMismatch: features have incompatible kinds
- CanNotBeCase: first feature in the pair cannot be used as a `case`
- CanNotBePlug: second feature in the pair cannot be use as a `plug`
- ModelValueCanNotBeUsed: second feature in the pair is model value and it cannot be used in the context of the first feature in the pair

If features in the feature pair are compatible, test case generator produces a test case. Test case consists of:

- TLC model: TLA+ specification and configuration
- Apalache model: TLA+ specification and configuration

Apalache model checker is new symbolic model checker for TLA+. It is used to independently verify TLC results (see test case results interpretation)

## Command options

TLC is expected to run on multiple cores. It has command line option `-worker` to control this behavior.
For every identified test case, there are created three:

* With `-worker 1` - base (original) variant
* With `-worker 2`
* With `-worker auto`

These additional test cases must yield the exactly same results as original TLC model with `worker 1`.

## Test case results

Running test case consists of following steps:

- Run TLC model: TBD
- Run Apalache model: TBD
- Compare results: TBD

There are four kinds of result:

- Success: all properties are proved
    - TBD: document error codes
- Violation: some property is violated
    - TBD: document error codes
- Crash: any other result

## Test case analysis

A test case, where TLC results and Apalache results diverge OR both are Crash, has to be manually analyzed in Divergence report. There must be no unexplained deviations.

## Docs

Feature list and description
Test specifications: feature matrix with reasons to skip
Test case results: all deviations explained
Coverage report

## Anomalous Conditions

* Resources:
    - RAM: container
    - Disk: container
    - Handles: container
    - Parallel execution? --> prohibit in safety manual?