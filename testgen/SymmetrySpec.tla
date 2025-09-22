SPDX-FileCopyrightText: Copyright (c) 2022 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
SPDX-License-Identifier: MIT

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the "Software"),
to deal in the Software without restriction, including without limitation
the rights to use, copy, modify, merge, publish, distribute, sublicense,
and/or sell copies of the Software, and to permit persons to whom the
Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
DEALINGS IN THE SOFTWARE.

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
