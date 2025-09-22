<!--
SPDX-FileCopyrightText: Copyright (c) 2022 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
SPDX-License-Identifier: MIT

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the "Software"),
to deal in the Software without restriction, including without limitation
the rights to use, copy, modify, merge, publish, distribute, sublicense,
and/or sell copies of the Software, and to permit persons to whom the
Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
DEALINGS IN THE SOFTWARE.
-->

# `SYMMETRY` Optimization Testing Strategy

Test generator based on pairwise feature combinations is not suitable to test `SYMMETRY` configuration setting,
because this setting is only applied in very specific cases: it requires sets of model values.

Due to this, combination of `SYMMETRY` with other optimization setting `VIEW` is also not tested.

Another problem with the test generator is that it generates very simple specifications. Whereas `SYMMETRY` requires
more sophisticated specification to be meaningfully tested.

CFG Test Generator is a test generator specifically aimed at testing `SYMMETRY` optimization setting in combinations
with other CFG settings.

The basis for the test cases is a single specification, which is complex enough for both `VIEW` and `SYMMETRY` to be
meaningfully applied.

## Test Model

All test cases use the same TLA+ specification file `SymmetrySpec.tla`

Test cases are created for every pairwise combination of `SYMMETRY` and

* `CHECK_DEADLOCK` (`TRUE`/`FALSE`)
* `VIEW` (present or not)
* `INVARIANT` (present or not)
* `PROPERTY` (present or not)

Reference configuration uses the same TLA+ specification and the same CFG file without `SYMMETRY`.

All test cases are of TestCaseType_RefTlc type: results from created model with `SYMMETRY` must be the same as results for the
reference model (without `SYMMETRY`)
