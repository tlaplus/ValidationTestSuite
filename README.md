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

 # Test Suite Generator

## Intro

This program generates and executes test cases for TLC (TLA+ Model Checker Tool).

## Prerequisites

* Before cloning the repository ensure that `git-lfs` is installed
* Python 3.9+ - it is known work with versions 3.9 and 3.10; it doesn't work with earlier versions
* Python libraries:
  - PyYAML
  - jinja2
* bubblewrap 0.4.0
* OpenJDK Runtime Environment 16.0.1

## Clean Run

```
python3.9 -m testgen --output-dir <PATH_TO_REPORTS> --specification --execution --html --workers <NUM_OF_WORKERS> --explanation-db explanation.yaml
```

* Always run the generator from its top level source directory
* `PATH_TO_REPORTS` is where all the artifacts are put; if `PATH_TO_REPORTS` exists, ensure it is empty
* For better performance, `NUM_OF_WORKER` should correspond to number of physical cores

## Debug Run

Test generator has four independent steps:
- `--specification` - generate test cases and test case specification report
- `--execution` - run test cases and create detailed JSON execution report
- `--coverage` - run test cases and collect coverage information
- `--html-report` - generate HTML reports

These steps can be used together (as for clean run) or separately.

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

## Full list of options

```
testgen [-h] [-s] [-e] [-g] [--html] -o OUTPUT_DIR [-f] [-w WORKERS] [-x FILE] [-d] [-n] [-a VAL [VAL ...] | -y VAL [VAL ...] | -u VAL VAL]

optional arguments:
  -h, --help            show this help message and exit
  -s, --specification   Generate test specification
  -e, --execute         Execute tests and create execution report
  -g, --coverage        Collect coverage information with JaCoCo
  --html                Create HTML report
  -o OUTPUT_DIR, --output-dir OUTPUT_DIR
                        Output directory
  -f, --force           Force recheck cached models
  -w WORKERS, --workers WORKERS
                        Number of workers (normally number of physical cores)
  -x FILE, --explanation-db FILE
                        YAML file with tests failure explanations
  -d, --debug           Enable debug output
  -n, --no-symmetry     Sandboxing: do not generate SYMMETRY cases
  -a VAL [VAL ...], --filter-any-side VAL [VAL ...]
                        Sandboxing: any-side filter
  -y VAL [VAL ...], --filter-any-side-exact VAL [VAL ...]
                        Sandboxing: any-side-exact filter
  -u VAL VAL, --filter-double-side VAL VAL
                        Sandboxing: any-side-exact filter
```
