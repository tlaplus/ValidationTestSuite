# SPDX-FileCopyrightText: Copyright (c) 2023 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
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
