# SPDX-FileCopyrightText: Copyright (c) 2022 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
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

from enum import Enum, auto, unique

@unique
class Kind(Enum):
    Const = 0
    State = 1
    Action = 2
    Temporal = 3
    Boxed = 4
    Nice = 5

    def generalize(self, other) -> bool:
        # Reflective
        if self == other:
            return True

        if self == Kind.Nice:
            return True

        if self == Kind.Temporal and other in [Kind.State, Kind.Const]:
            return True
        
        if self == Kind.Boxed and other in [Kind.Action, Kind.State, Kind.Const]:
            return True

        if self == Kind.Action and other in [Kind.State, Kind.Const]:
            return True

        if self == Kind.State and other in [Kind.Const]:
            return True

        return False

    """
    def __lt__(self, other) -> bool:
        if self.__class__ is other.__class__:
            return self.value < other.value
        return NotImplemented
    """
    def __eq__(self, other) -> bool:
        if self.__class__ is other.__class__:
            return self.value == other.value
        return NotImplemented

def most_generic(*kinds):
    r = None
    for u in kinds:
        if all(u.generalize(v) for v in kinds):
            return u
    raise f'Inconsistent set of kinds: {kinds}'