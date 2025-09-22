<!-- SPDX-FileCopyrightText: Copyright (c) 2022 NVIDIA CORPORATION & AFFILIATES. All rights reserved. -->


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
