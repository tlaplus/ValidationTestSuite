SPDX-FileCopyrightText: Copyright (c) 2022 NVIDIA CORPORATION & AFFILIATES. All rights reserved.

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
