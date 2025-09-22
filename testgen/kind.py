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