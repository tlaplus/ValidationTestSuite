SPDX-FileCopyrightText: Copyright (c) 2022 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
SPDX-License-Identifier: Apache-2.0

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

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
