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
