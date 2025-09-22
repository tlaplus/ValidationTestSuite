<!--
SPDX-FileCopyrightText: Copyright (c) 2022 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
SPDX-License-Identifier: Apache-2.0

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-->

# Validation Test Suite for TLA+

The **Validation Test Suite for TLA+** is a comprehensive testing framework that enables the use of TLC in safety-critical software development contexts, including ISO 26262 certification. This Python-based tool automatically generates and executes extensive test cases for [TLC](https://github.com/tlaplus/tlaplus), the TLA+ model checker, to help verify that it satisfies the requirements defined by Automotive Functional Safety Standard ISO 26262 for safety-critical software development.

The suite runs both TLC and [Apalache](https://github.com/apalache-mc/apalache) model checkers, comparing results to ensure consistency and validates results through cross-checking. It produces test suites that support qualifying TLC for use in safety-critical applications including automotive systems, aerospace applications, medical devices, and industrial control systems.

This suite was created by Dmitry Kulagin (GitHub: craft095) at NVIDIA and initially contributed by NVIDIA, which successfully used this generator to qualify TLC for their safety-critical applications. Contributions are welcome! Please check the [issues](https://github.com/tlaplus/ValidationTestSuite/issues) for ways to contribute.

## Key Features and Technical Approach

The suite employs a systematic strategy with the following key capabilities:

- **Systematic Testing**: Defines a constrained TLA+ subset suitable for safety-critical use cases, then automatically creates test suites using pairwise feature combinations of TLA+ language constructs
- **Cross-Validation**: Runs both TLC and Apalache model checkers, comparing results to ensure consistency and validates results through cross-checking
- **Comprehensive Coverage**: Tests over 100 TLA+ language features including operators, constants, variables, and other constructs, categorized by type and kind
- **Multi-Core Support**: Tests TLC with different worker configurations (-workers 1, 2, auto)
- **Detailed Reporting**: Generates HTML reports with test specifications, execution results, and coverage information
- **Anomalous Condition Testing**: Includes testing under resource constraints and edge cases
- **Deviation Documentation**: Documents and explains all divergences between tools to provide complete transparency

## Why This Matters for Safety-Critical Applications

The qualification suite addresses a critical need in the TLA+ ecosystem: providing the rigorous testing and documentation required to use TLC in safety-critical contexts such as:
- Automotive systems (ISO 26262)
- Aerospace applications
- Medical devices
- Industrial control systems

By systematically exercising TLC's behavior across thousands of test cases and documenting known deviations, this suite provides the evidence base needed for tool qualification in regulated industries.

## Prerequisites

* Before cloning the repository ensure that `git-lfs` is installed
* Python 3.9+ - it is known work with versions 3.9 and 3.10; it doesn't work with earlier or newer versions
* Python libraries:
  - PyYAML
  - jinja2
* OpenJDK Runtime Environment 17
* bubblewrap 0.4.0 (Linux only)

## Usage

### Basic Usage

```bash
python -m testgen -o <PATH_TO_REPORTS> -s -e --html -x explanation.yaml -w <NUM_OF_WORKERS> $*
```

* Always run the generator from its top level source directory
* `<PATH_TO_REPORTS>` is where all the artifacts are put; if `<PATH_TO_REPORTS>` exists, ensure it is empty
* For better performance, `<NUM_OF_WORKERS>` should correspond to number of physical cores

For a complete and up-to-date list of all available command-line options, run:

```bash
python -m testgen --help
```

### Advanced Usage

Test generator has four independent steps:
- `--specification` - generate test cases and test case specification report
- `--execute` - execute tests and create execution report
- `--coverage` - collect coverage information with JaCoCo
- `--html` - create HTML report

These steps can be used together (as for basic usage) or separately.

It is often convenient to limit scope of test suite. To do so specification step can be supplied with following flags:
- `--no-symmetry` - do not generate SYMMETRY cases
- `--filter-any-side VAL0 [VAL1 ...]` - only include test cases with features, whose name include any of `VALn`
- `--filter-any-side-exact VAL0 [VAL1 ...]` - only include test cases with features, whose name is exactly any of `VALn`
- `--filter-double-side VAL0 VAL1` - only include test cases, where case feature name include `VAL0` and plug feature name include `VAL1`

The longest step is test execution. By default, a model is only checked if:
- There is no previous run results
- It has changed since previous run
- Its latest checking result is "crash"

Such behavior saves a lot of time. If it is not desireable, there is an option `--force` to check the model unconditionally.

Finally, there is `--debug` option to enable verbose mode.

## Validation Reports and Releases

The most recent validation report is available at https://dl.tlapl.us/validation-test-suite. Both recent and older reports can be found on the [GitHub releases page](https://github.com/tlaplus/ValidationTestSuite/releases). Each release's SHA identifies the Git commit from which it was created. The TLC tool is stored in the Git repository using Git LFS.

## Further Reading

- [Test Strategy](test-strategy.md) - Comprehensive overview of the systematic testing approach, including feature identification, pairwise combinations, and test case generation methodology
- [Symmetry Testing](symmetry.md) - Specialized testing strategy for TLC's `SYMMETRY` optimization setting and its interactions with other configuration options
