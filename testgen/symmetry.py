# SPDX-FileCopyrightText: Copyright (c) 2022-2026 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
# SPDX-License-Identifier: Apache-2.0
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

from .ast import *
from .testcase import *

def etalon_cfg(deadlock, invariant, property, view):
    return fR"""
\* CONFIG

CONSTANT
    M0 = M0
    M1 = M1
    M2 = M2
    M3 = M3

    Iterations <- IterationsDef

SPECIFICATION
    Spec

{deadlock}
{view or ''}
{invariant or ''}
{property or ''}
"""

def symmetry_cases():
    name = 'SymmetrySpec'
    symmetries = [
        ("Permutations(U)", "SYMMETRY MessagesSymm1"),
        (R"Permutations(U) \union Permutations(V)", "SYMMETRY MessagesSymm2"),
    ]
    invariants = [
        ("Positive", "INVARIANT InvPos"),
        ("Negative", "INVARIANT InvNeg"),
        ("Absent", None),
    ]
    properties = [
        ("Positive", "PROPERTY PropPos"),
        ("Negative", "PROPERTY PropNeg"),
        ("Absent", None),
    ]
    views = [
        (True, "VIEW ViewDef"),
        (False, None),
    ]
    deadlocks = [
        (True, "CHECK_DEADLOCK TRUE"),
        (False, "CHECK_DEADLOCK FALSE"),
    ]
    cases = []

    for symmetry in symmetries:
        for invariant in invariants:
            for property in properties:
                for view in views:
                    for deadlock in deadlocks:
                        ref = etalon_cfg(
                            deadlock = deadlock[1],
                            invariant = invariant[1],
                            property = property[1],
                            view = view[1],
                        )
                        ref_model = PlainFileModel(name, cfg_content = ref)
                        tlc = '\n'.join([ref, symmetry[1]])
                        tlc_model = PlainFileModel(name, cfg_content = tlc)

                        desc = {
                            'check_deadlock' : deadlock[0],
                            'invariant' : invariant[0],
                            'property' : property[0],
                            'view' : view[0],
                            'symmetry' : symmetry[0],
                            'reduction_strategy': {
                                'configuration': 'Do not use SYMMETRY optimization'
                            },
                        }

                        case = TlcSymmetryCase(tlc_model, ref_model, desc)
                        cases.append(case)
    return cases
