# SPDX-FileCopyrightText: Copyright (c) 2022 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
# SPDX-License-Identifier: MIT
#
# Permission is hereby granted, free of charge, to any person obtaining a
# copy of this software and associated documentation files (the "Software"),
# to deal in the Software without restriction, including without limitation
# the rights to use, copy, modify, merge, publish, distribute, sublicense,
# and/or sell copies of the Software, and to permit persons to whom the
# Software is furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
# THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
# FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
# DEALINGS IN THE SOFTWARE.

from .ast import *
from .testcase import *

def etalon_cfg(deadlock, invariant = False, property = False):
    inv = "INVARIANT Inv" if invariant else ""
    prop = "PROPERTY Prop" if property else ""

    return f"""
\* CONFIG

CONSTANT
    M0 = M0
    M1 = M1
    M2 = M2
    M3 = M3

    Iterations <- IterationsDef

SPECIFICATION
    Spec

CHECK_DEADLOCK {'TRUE' if deadlock else 'FALSE'}

{inv}
{prop}
"""

def symmetry_cases():
    name = 'SymmetrySpec'
    view_line = "VIEW ViewDef"
    symmetry = "SYMMETRY MessagesSymm"

    cases = []

    for deadlock in [True, False]:
        for inv in [True, False]:
            for property in [True, False]:
                ref = etalon_cfg(deadlock = deadlock, invariant = inv, property = property)
                ref_model = PlainFileModel(name, cfg_content = ref)
                for view in [True, False]:
                    parts = [ref, symmetry]
                    if view:
                        parts.append(view_line)
                    tlc = '\n'.join(parts)
                    tlc_model = PlainFileModel(name, cfg_content = tlc)

                    desc = {
                        'check_deadlock' : deadlock,
                        'invariant' : inv,
                        'property' : property,
                        'view' : view,
                        'reduction_strategy': {
                            'configuration': 'Do not use SYMMETRY optimization'
                        }
                    }

                    case = TlcSymmetryCase(tlc_model, ref_model, desc)
                    cases.append(case)
    return cases
