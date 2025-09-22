# SPDX-FileCopyrightText: Copyright (c) 2022 NVIDIA CORPORATION & AFFILIATES. All rights reserved.

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
