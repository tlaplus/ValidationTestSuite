SPDX-FileCopyrightText: Copyright (c) 2022 NVIDIA CORPORATION & AFFILIATES. All rights reserved.

---- MODULE SymmetrySpec ----

EXTENDS TLC, Naturals, FiniteSets

CONSTANT
    M0,
    M1,
    M2,
    M3,
    Iterations

VARIABLE
    left,
    right,
    iteration,
    count

Messages == { M0, M1, M2, M3 }

vars == <<left, right, iteration, count>>

Init ==
    /\ left = Messages
    /\ right = {}
    /\ count = 0
    /\ iteration = 0

Send == \E message \in left :
    /\ left' = left \ { message }
    /\ right' = right \union { message }
    /\ count' = count + 1
    /\ UNCHANGED iteration

Iteration ==
    /\ iteration < Iterations
    /\ left = {}
    /\ iteration' = iteration + 1
    /\ left' = right
    /\ right' = {}
    /\ UNCHANGED count

Next == Send \/ Iteration

Spec == Init /\ [][Next]_vars

----

Inv == (left \union right) = Messages
Prop == [] Inv

MessagesSymm == Permutations(Messages)
IterationsDef == 2
ViewDef == <<left, right, iteration>>

====
