# SPDX-FileCopyrightText: Copyright (c) 2023 NVIDIA CORPORATION & AFFILIATES. All rights reserved.

from enum import Enum, unique

# Test case types

# Reference model is reduced TLC model
TestCaseType_RefTlc = 'ref-tlc'

# Reference model is Apalache model
TestCaseType_RefApalache = 'ref-apalache'

# Special test cae to be run under anomalous operating conditions
TestCaseType_RefAnomalous = 'ref-anomalous'

@unique
class AnomalousCondition(Enum):
    OutOfMemory = 'OutOfMemory'
    OutOfSpace = 'OutOfSpace'
    OutOfHandles = 'OutOfHandles'

    def describe(self):
        if self == AnomalousCondition.OutOfMemory:
            desc = {
                'desc' : 'Out of memory',
                'memory' : 5000000
            }
        elif self == AnomalousCondition.OutOfSpace:
            desc = {
                'desc' : 'out of space',
                'max-file-size' : 1000
            }
        elif self == AnomalousCondition.OutOfHandles:
            desc = {
                'desc' : 'Out of handles',
                'max-handles' : 20
            }
        else:
            assert False, f'Unknown anomalous condition {self}'

        desc['tag'] = self.value
        return desc
