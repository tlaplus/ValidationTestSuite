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

\* Designed to test TLC under anomalous conditions. It must be complex enough to:
\*  - consume significant amount of RAM
\*  - consume significant amount of disk space
\*  - consume significant amount of system handles

---- MODULE AnomalousSpec ----

EXTENDS Naturals, Sequences

VARIABLE queue

\* Such size and message set will result in ~10M states
Size == 10
Messages == 1..5

Init == queue = <<>>

Send == \E message \in Messages :
    /\ Len(queue) < Size
    /\ queue' = Append(queue, message)

Receive ==
    /\ queue /= <<>>
    /\ queue' = Tail(queue)

Next == Send \/ Receive

Spec == Init /\ [][Next]_queue

----

Inv == { queue[ix] : ix \in DOMAIN queue } \subseteq Messages
Prop == [] Inv

====
