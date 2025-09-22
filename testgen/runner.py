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

import logging
import os
import json
import tempfile
from .parallel import *

'''
TLC Error Codes

| Class | Name                          | Code |
|:-----:|:------------------------------|----:|
| 1     | SUCCESS                       |   0 |
| 2     | VIOLATION_ASSUMPTION          |  10 |
| 2     | VIOLATION_DEADLOCK            |  11 |
| 2     | VIOLATION_SAFETY              |  12 |
| 2     | VIOLATION_LIVENESS            |  13 |
| 2     | VIOLATION_ASSERT              |  14 |
| 3     | FAILURE_SPEC_EVAL             |  75 |
| 3     | FAILURE_SAFETY_EVAL           |  76 |
| 3     | FAILURE_LIVENESS_EVAL         |  77 |
| 3     | ERROR_SPEC_PARSE              | 150 |
| 3     | ERROR_CONFIG_PARSE            | 151 |
| 4     | ERROR_STATESPACE_TOO_LARGE    | 152 |
| 4     | ERROR_SYSTEM                  | 153 |
| 4     | ERROR_GENERIC                 | 255 |
'''

VIOLATION_ASSUMPTION = 10
VIOLATION_DEADLOCK = 11
VIOLATION_SAFETY = 12
VIOLATION_LIVENESS = 13
VIOLATION_ASSERT = 14

# Even though TLC qualification only covers safety properties,
# VIOLATION_LIVENESS is also included. The reason: TLC _can_ use
# this error code for safety violation
tlc_violation_codes = [VIOLATION_SAFETY, VIOLATION_LIVENESS]

RESULT_SUCCESS='success'
RESULT_VIOLATION='violation'
RESULT_DEADLOCK='deadlock'
RESULT_ASSUMPTION='assumption'
RESULT_CRASH='crash'

tlc_jar = None
apalache_jar = None
jacoco_jar = None

tmp_dir = None

def setup():
    global tlc_jar, apalache_jar, tmp_dir, jacoco_jar
    working_dir = os.getcwd()
    tlc_jar = os.path.join(working_dir, 'tools', '1.7.2', 'tla2tools.jar')
    apalache_jar = os.path.join(working_dir, 'tools', 'apalache-0.28.0.jar')
    jacoco_jar = os.path.join(working_dir, 'tools', 'jacoco-0.8.8', 'jacocoagent.jar')

    tmp_dir = tempfile.TemporaryDirectory()

def teardown():
    tmp_dir.cleanup()

async def run_wrapper(exec_dir, id, force, f):
    cache = os.path.join(exec_dir, id)
    os.makedirs(cache, exist_ok = True)

    meta_file = os.path.join(cache, 'execution_result.json')
    if not force:
        try:
            with open(meta_file, 'r') as h:
                d = json.load(h)
                non_crash = [RESULT_SUCCESS, RESULT_VIOLATION, RESULT_DEADLOCK]
                if 'status' in d and d['status'] in non_crash:
                    return d['status']
        except json.JSONDecodeError:
            pass
        except FileNotFoundError:
            pass

    (exec_args, status, returncode, stdout) = await f()

    # Save execution results into cache
    meta = {
        'retcode' : returncode,
        'status' : status
    }

    with open(meta_file, 'w') as h:
        h.write(json.dumps(meta, indent = 2))

    with open(os.path.join(cache, 'execution_args.cmd'), 'w') as h:
        h.write(exec_args)

    with open(os.path.join(cache, 'execution_output.log'), 'wb') as h:
        h.write(stdout)

    return status

def mk_tmp(desc):
    dir_name = os.path.join(tmp_dir.name, desc['id'])
    os.makedirs(dir_name, exist_ok = True)
    return dir_name

def tlc_args(spec_dir, exec_dir, desc, coverage):
    # Add TLA-Library option if needed
    relative_search_paths = desc['search_paths']
    if relative_search_paths:
        search_paths = os.pathsep.join([os.path.join(spec_dir, p) for p in relative_search_paths])
        search_paths_opts = [f'-DTLA-Library={search_paths}']
    else:
        search_paths_opts = []

    # Add coverage agent if needed
    if coverage:
        sample_file = os.path.join(exec_dir, 'jacoco.exec')
        jacoco = [f'-javaagent:{jacoco_jar}=destfile={sample_file}']
    else:
        jacoco = []

    # Compose cmd line
    return [
        'java', '-XX:+UseParallelGC',
        # Disable LazyValue optimization, which has at least one known issue #798
        '-Dtlc2.value.impl.LazyValue.off=true',
    ] + jacoco + [
        '-cp', tlc_jar,
    ] + search_paths_opts + [
        'tlc2.TLC', '-lncheck', 'final',
        '-metadir', mk_tmp(desc)
    ] + desc['cmd_options'] + [
        '-config', os.path.join(spec_dir, desc['cfg']['file']),
        os.path.join(spec_dir, desc['main_module']) + '.tla'
    ]

async def run_tlc_internal(spec_dir, exec_dir, desc, coverage, is_anomalous, max_concurrent_tasks=1):
    env = os.environ.copy()
    env['TMPDIR'] = mk_tmp(desc)

    args = tlc_args(spec_dir, exec_dir, desc, coverage)

    if not is_anomalous:
        result = await run_process(*args, env = env, max_concurrent_tasks=max_concurrent_tasks)
    else:
        result = await run_process_anomalous(desc['anomalous_conditions'], *args, env = env, max_concurrent_tasks=max_concurrent_tasks)

    (exec_desc, returncode, stdout) = result

    # As of 1.7.2 TLC has no option to turn warnings into errors
    # At the same time, all TLC warnings are actually avoidable and some
    # of them really dangerous
    if b'*** Warnings:' in stdout:
        status = f'warning<{returncode}>'
    elif returncode == 0:
        status = RESULT_SUCCESS
    elif returncode == VIOLATION_DEADLOCK:
        status = RESULT_DEADLOCK
    elif returncode == VIOLATION_ASSUMPTION:
        status = RESULT_ASSUMPTION
    elif returncode in tlc_violation_codes:
        status = RESULT_VIOLATION
    else:
        status = RESULT_CRASH

    return (exec_desc, status, returncode, stdout)

def apalache_args(spec_dir, desc):
    cfg = os.path.join(spec_dir, desc['cfg']['file'])
    return [
        'java', '-XX:+UseParallelGC',
        f'-DTLA-Library={spec_dir}',
        '-jar', apalache_jar,
        f'--out-dir={mk_tmp(desc)}',
        f'--run-dir={mk_tmp(desc)}',
        'check',
    ] + desc['cmd_options'] + [
        f'--config={cfg}',
        '--length=5',
        os.path.join(spec_dir, desc['main_module']) + '.json'
    ]

async def run_apalache_internal(spec_dir, desc, max_concurrent_tasks=1):
    env = os.environ.copy()
    env['TMPDIR'] = mk_tmp(desc)
    args = apalache_args(spec_dir, desc)

    (exec_desc, returncode, stdout) = await run_process(*args, env = env, max_concurrent_tasks=max_concurrent_tasks)

    if b'*** Warnings:' in stdout:
        status = f'warning<{returncode}>'
    elif b'Error parsing file' in stdout:
        status = f'parseerror<{returncode}>'
    elif b'meow' in stdout:
        # Type errors, which are not signalled with exit code
        status = f'typeerror<{returncode}>'
    elif returncode == 0:
        status = RESULT_SUCCESS
    elif returncode == 12:
        if b'The outcome is: Deadlock' in stdout:
            status = RESULT_DEADLOCK
        else:
            status = RESULT_VIOLATION
    else:
        status = RESULT_CRASH

    return (exec_desc, status, returncode, stdout)

async def run_tlc(spec_dir, exec_dir, desc, force, execution_results, coverage, is_anomalous, max_concurrent_tasks=1):
    async def f():
        r = await run_tlc_internal(spec_dir, exec_dir, desc, coverage, is_anomalous, max_concurrent_tasks)
        return r
    r = await run_wrapper(exec_dir, desc['id'], force, f)
    execution_results[desc['id']] = r

async def run_apalache(spec_dir, exec_dir, desc, force, execution_results, max_concurrent_tasks=1):
    async def f():
        r = await run_apalache_internal(spec_dir, desc, max_concurrent_tasks)
        return r
    r = await run_wrapper(exec_dir, desc['id'], force, f)
    execution_results[desc['id']] = r

def collect_testcase(spec_dir, exec_dir, desc, force, tasks, execution_results, coverage, max_concurrent_tasks=1):
    assert desc['type'] in [TestCaseType_RefApalache, TestCaseType_RefTlc, TestCaseType_RefAnomalous]
    logging.debug(f'collect_testcase: {desc["desc"]}')

    tc = { 'desc' : desc }

    tlc_path = os.path.join(spec_dir, desc['tlc']['path'])
    tc['tlc_path'] = tlc_path

    if desc['type'] != TestCaseType_RefAnomalous:
        ref_path = os.path.join(spec_dir, desc['ref']['path'])
        tc['ref_path'] = ref_path

    tlc_id = desc['tlc']['id']
    if tlc_id not in tasks:
        tasks[tlc_id] = run_tlc(
            tlc_path,
            exec_dir,
            desc['tlc'],
            force,
            execution_results,
            coverage,
            is_anomalous = desc['type'] == TestCaseType_RefAnomalous,
            max_concurrent_tasks = max_concurrent_tasks)

    # Do not execute reference model if coverage is collected or
    # this is an anomalous conditions test
    if not coverage and desc['type'] != TestCaseType_RefAnomalous:
        ref_id = desc['ref']['id']
        if ref_id not in tasks:
            if desc['type'] == TestCaseType_RefApalache:
                tasks[ref_id] = run_apalache(
                    ref_path, exec_dir, desc['ref'], force, execution_results, max_concurrent_tasks)
            elif desc['type'] == TestCaseType_RefTlc:
                tasks[ref_id] = run_tlc(
                    ref_path, exec_dir, desc['ref'], force, execution_results,
                    coverage = False, is_anomalous = False, max_concurrent_tasks = max_concurrent_tasks)
            else:
                assert False, f'Unknown case type {desc["type"]}'
    return tc

# Update the report with execution results for specific testcase
def testcase_execution_report(report, explanation_db, execution_results):
    desc = report['desc']
    tc_type = desc['type']
    assert tc_type in [TestCaseType_RefApalache, TestCaseType_RefTlc, TestCaseType_RefAnomalous]
    tlc_id = desc['tlc']['id']
    tlc = execution_results.get(tlc_id)
    assert tlc

    logging.debug(f'testcase_execution_report: {desc["desc"]}')

    verdict = None
    explanation = None

    if tc_type == TestCaseType_RefAnomalous:
        # Expected behavior when TLC is run under anomalous condition is detectable crash
        ref = RESULT_CRASH
        if tlc == ref:
            verdict = 'Passed'
        else:
            verdict = 'Failed'
    else:
        ref_id = desc['ref']['id']
        ref = execution_results.get(ref_id)
        assert ref

        if tc_type == TestCaseType_RefApalache:
            if tlc == RESULT_ASSUMPTION and ref == RESULT_VIOLATION:
                # Apalache treats ASSUME statements as invariants
                verdict = 'Passed'
            elif tlc != ref or tlc not in [RESULT_SUCCESS, RESULT_VIOLATION, RESULT_DEADLOCK]:
                verdict = 'Failed'
                explanation = explanation_db.find_explanation(desc['desc'], tlc, ref)
                if not explanation:
                    logging.info(f'Unexplained results for: {report["desc"]}')
                    logging.info(f'\t{tlc} :: {ref}')
            else:
                verdict = 'Passed'
        elif tc_type == TestCaseType_RefTlc:
            if tlc != ref:
                verdict = 'Failed'
                explanation = explanation_db.find_explanation(desc['desc'], tlc, ref)
                if not explanation:
                    logging.info(f'Unexplained results for: {report["desc"]}')
                    logging.info(f'\t{tlc} :: {ref}')
            else:
                verdict = 'Passed'

    assert verdict

    report['tlc_status'] = tlc
    report['ref_status'] = ref
    report['verdict'] = verdict
    report['explained'] = explanation != None
    if explanation != None:
        report['explanation'] = explanation.explanation

def load_spec(spec_file):
    with open(spec_file, 'r') as h:
        return json.load(h)

def run_testcases_parallel(
        spec_dir,
        spec_file,
        exec_report_file,
        exec_dir,
        force = False,
        workers = 1,
        explanation_db = None,
        coverage = False):

    spec = load_spec(spec_file)
    setup()

    try:
        report = {}
        tasks = {}
        execution_results = {}

        for tc in spec.values():
            if tc['type'] == 'skipped':
                continue
            # Prepare meta information; the report is updated with actual results later on
            report[tc['id']] = collect_testcase(
                spec_dir, exec_dir, tc, force, tasks, execution_results, coverage, workers)

        run_tasks(list(tasks.values()), max_concurrent_tasks = workers)

        if not coverage:
            for tc in report.values():
                # Update report with results
                testcase_execution_report(tc, explanation_db, execution_results)

            with open(exec_report_file, 'w') as h:
                return json.dump(report, h, indent = 2)
    finally:
        teardown()
