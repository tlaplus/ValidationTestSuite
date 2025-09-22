# SPDX-FileCopyrightText: Copyright (c) 2023 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
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
