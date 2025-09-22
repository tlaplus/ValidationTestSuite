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

# Global per model unique id
id = 0

# Reset name id
def reset_name():
    global id
    id = 0

# Make unique name
def mk_name():
    global id
    name = f'x{id}'
    id += 1
    return name

# String formatting helpers

linesep = '\n'

def intersperse(sep, xs):
    it = iter(xs)
    if not xs:
        return
    yield next(it)
    for x in it:
        yield sep
        yield x

default_ident = '    '

def indent_one(shift, v):
    return shift + v if v != '' else ''

def commas(vs : list[str]) -> str:
    return ', '.join(vs)

def unlines(vs : list[str]) -> str:
    return linesep.join(vs)

# Unlines with black line in between
def unlines1(vs : list[str]) -> str:
    return unlines(intersperse('', vs))

def indent_multiline(shift, v : str) -> str:
    return unlines([indent_one(shift, x) for x in v.splitlines()])

def indent_multiline_but_first(shift, v : str) -> str:
    lines = v.splitlines()
    if not lines:
        return ''
    x0 = lines[0]
    xs = [indent_one(shift, x) for x in lines[1:]]
    return unlines([x0] + xs)

def indent(*vs : str) -> str:
    return unlines([indent_multiline(default_ident, x) for x in vs])

def indent_but_first_with(shift, *vs : str) -> str:
    if not vs:
        return ''
    x0 = indent_multiline_but_first(shift, vs[0])
    xs = [indent_multiline(shift, x) for x in vs[1:]]
    return unlines([x0] + xs)

def indent_but_first(*vs : str) -> str:
    return indent_but_first_with(default_ident, *vs)

def indent_with(shift, *vs : str) -> str:
    return unlines([indent_multiline(shift, x) for x in vs])
