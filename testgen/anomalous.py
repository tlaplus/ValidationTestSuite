# SPDX-FileCopyrightText: Copyright (c) 2023 NVIDIA CORPORATION & AFFILIATES. All rights reserved.

from .testcase import *

def cfg_content():
    return """
\* CONFIG

SPECIFICATION
    Spec

CHECK_DEADLOCK TRUE

INVARIANT Inv
PROPERTY Prop
"""

def make_case(condition):
    name = 'AnomalousSpec'
    model = PlainFileModel(name, cfg_content = cfg_content(), cmd_options = ['-workers', '2'])
    case = AnomalousConditionCase(model, condition)
    return case

# Create test cases for anomalous conditions
def anomalous_cases():
    return [make_case(condition) for condition in AnomalousCondition]
