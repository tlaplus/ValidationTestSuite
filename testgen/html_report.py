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

import os
import json
from jinja2 import Environment, FileSystemLoader
from .testcasedefs import *

def get_template_path():
    return os.path.join(os.path.dirname(__file__), 'templates')

def get_file_content(name):
    file_path = os.path.join(os.path.dirname(__file__), name)
    with open(file_path) as h:
        content = h.read()
    return content

def save_file(file, content):
    with open(file, mode = 'w', encoding = 'utf-8') as h:
        h.write(content)

def copy_site_file(name, html_dir):
    content = get_file_content(os.path.join('templates', name))
    save_file(os.path.join(html_dir, name), content)

def calculate_statistics(spec, results):
    # Total number of skipped feature combinations
    skipped = 0
    # Total number of generated test cases
    generated = 0
    # Total number of passed test cases
    passed = 0
    # Total number of failed test cases with explanation
    failed_explained = 0
    # Total number of failed test cases without explanation
    failed_unexplained = 0

    for tc_id, tc in spec.items():
        if tc['type'] == 'skipped':
            skipped += 1
            continue

        generated += 1
        result = results[tc_id]

        if result['verdict'] == 'Passed':
            passed += 1
        elif result['explained']:
            failed_explained += 1
        else:
            failed_unexplained += 1

    return {
        'skipped' : skipped,
        'generated' : generated,
        'passed' : passed,
        'failed_explained' : failed_explained,
        'failed_unexplained' : failed_unexplained,
    }

WORKERS_1 = '1'
WORKERS_2 = '2'
WORKERS_AUTO = 'auto'

workers = [WORKERS_1, WORKERS_2, WORKERS_AUTO]

class Index:
    def __init__(self):
        self.cases = {}
        self.plugs = {}
        self.symmetry = []

class IndexRefs:
    def __init__(self):
        self.cases = {}
        self.plugs = {}
        self.symmetry = None

class IndexSkippedRefs:
    def __init__(self):
        self.cases_skipped = {}
        self.plugs_skipped = {}

def find_workers(tc):
    options = tc['tlc']['cmd_options']
    for w in workers:
        if w in options:
            return w
    assert False, 'Non-reachable code'
    return None

def build_index(spec):
    index = {}
    features = set()

    for tc in spec.values():
        desc = tc['desc']
        if 'case_feature' in desc:
            case_id = desc['case_feature']
            plug_id = desc['plug_feature']

            features.add(case_id)
            features.add(plug_id)

        if tc['type'] == 'skipped':
            assert 'case_feature' in desc, "Only test cases based on feature combination can be skipped"
            continue

        # Index does not include anomalous tests, because they do not need indexing
        if tc['type'] == TestCaseType_RefAnomalous:
            continue

        workers = find_workers(tc)
        active_index = index.setdefault(workers, Index())
        if 'case_feature' in desc:
            case = active_index.cases.setdefault(case_id, [])
            plug = active_index.plugs.setdefault(plug_id, [])
            case.append(tc)
            plug.append(tc)
        else:
            assert 'view' in desc
            active_index.symmetry.append(tc)

    fs = list(features)
    fs.sort()

    return (index, fs)

def generate_index_skipped_html(env, html_dir, spec, toc):
    cases_skipped = {}
    plugs_skipped = {}

    # Build index for skipped test cases; index must include all features, even if there are skipped test
    # cases for a particular feature
    for id, tc in spec.items():
        desc = tc['desc']

        if 'case_feature' not in desc:
            assert tc['type'] != 'skipped', "Only test cases based on feature combination can be skipped"
            continue

        case_id = desc['case_feature']
        plug_id = desc['plug_feature']

        case = cases_skipped.setdefault(case_id, [])
        plug = plugs_skipped.setdefault(plug_id, [])
        if tc['type'] == 'skipped':
            case.append(tc)
            plug.append(tc)

    features = sorted(cases_skipped.keys())

    # Generate index files per case/plug
    index_refs = IndexSkippedRefs()

    feature_template_file = "test-feature-skipped-case-plug.html"
    feature_template = env.get_template(feature_template_file)

    for case_feature, case_tcs in cases_skipped.items():
        content = feature_template.render(feature_role = 'case', feature = case_feature, spec = case_tcs, toc = toc)

        html_file = f'test-feature-skipped-case-{case_feature.lower()}.html'
        save_file(os.path.join(html_dir, html_file), content)

        index_refs.cases_skipped[case_feature] = html_file

    for plug_feature, plug_tcs in plugs_skipped.items():
        content = feature_template.render(feature_role = 'plug', feature = plug_feature, spec = plug_tcs, toc = toc)

        html_file = f'test-feature-skipped-plug-{plug_feature.lower()}.html'
        save_file(os.path.join(html_dir, html_file), content)

        index_refs.plugs_skipped[plug_feature] = html_file

    # Generate top level skipped index
    template_file = "test-feature-skipped.html"
    template = env.get_template(template_file)
    content = template.render(index_refs = index_refs, features = features, toc = toc)

    html_file = template_file
    save_file(os.path.join(html_dir, html_file), content)

    return html_file

feature_template_file = 'test-feature-case-plug.html'

def feature_case_html_file(workers, feature):
    return f'test-feature-case-workers_{workers}-{feature.lower()}.html'

def feature_plug_html_file(workers, feature):
    return f'test-feature-plug-workers_{workers}-{feature.lower()}.html'

symmetry_template_file = "test-symmetry.html"

def symmetry_html_file(workers):
    return f'test-symmetry-workers_{workers}.html'

def generate_index_workers_html(env, html_dir, index, workers, results, toc):
    index_refs = IndexRefs()

    feature_template = env.get_template(feature_template_file)

    for case_feature, case_tcs in index[workers].cases.items():
        content = feature_template.render(feature_role = 'case', feature = case_feature, workers = workers, spec = case_tcs, results = results, toc = toc)

        html_file = feature_case_html_file(workers, case_feature)
        save_file(os.path.join(html_dir, html_file), content)

        index_refs.cases[case_feature] = html_file

    for plug_feature, plug_tcs in index[workers].plugs.items():
        content = feature_template.render(feature_role = 'plug', feature = plug_feature, workers = workers, spec = plug_tcs, results = results, toc = toc)

        html_file = feature_plug_html_file(workers, plug_feature)
        save_file(os.path.join(html_dir, html_file), content)

        index_refs.plugs[plug_feature] = html_file

    template_file = symmetry_template_file
    template = env.get_template(template_file)
    content = template.render(spec = index[workers].symmetry, workers = workers, results = results, toc = toc)

    html_file = symmetry_html_file(workers)
    save_file(os.path.join(html_dir, html_file), content)

    index_refs.symmetry = html_file

    return index_refs

anomalous_html_file = "test-anomalous-conditions.html"

def generate_anomalous_html(env, html_dir, spec, results, toc):
    anomalous = []
    for tc in spec.values():
        if tc['type'] != TestCaseType_RefAnomalous:
            continue

        desc = tc['desc']
        assert 'tag' in desc, "tag must present in description"
        anomalous.append(tc)

    template_file = anomalous_html_file
    template = env.get_template(template_file)
    content = template.render(spec = anomalous, results = results, toc = toc)
    save_file(os.path.join(html_dir, anomalous_html_file), content)

failed_html_file = "test-feature-failed.html"

# Generate report with failed test cases
def generate_failed_html(env, html_dir, spec, results, toc):
    failed_template = env.get_template(failed_html_file)

    failed = []
    for id, tc in spec.items():
        if tc['type'] == 'skipped':
            continue

        if results[id]['verdict'] == 'Passed':
            continue

        desc = tc['desc']
        assert 'case_feature' in desc, "Do not expect failed test cases in SYMMETRY"

        # There must be no failed testcase for all workers except WORKERS_1
        assert find_workers(tc) == WORKERS_1, f"Unexpected failed test cases for '{find_workers(tc)}'"

        failed.append(tc)

    content = failed_template.render(spec = failed, results = results, toc = toc)
    save_file(os.path.join(html_dir, failed_html_file), content)

def generate_index_html(env, html_dir, index, results, toc):
    index_refs = {}
    for w in workers:
        index_refs[w] = generate_index_workers_html(env, html_dir, index, w, results, toc)

    return index_refs

def generate_feature_toc(env, html_dir, index_refs, features, toc):
    for w in workers:
        template_file = "test-feature.html"
        template = env.get_template(template_file)
        content = template.render(
            workers = w, features = features, index_refs = index_refs[w], toc = toc)

        html_file = f'test-feature-workers_{w}.html'
        save_file(os.path.join(html_dir, html_file), content)

def generate_models_html(env, html_dir, spec_dir, result_dir, models, index_refs, toc):
    for id, model in models.items():
        template_file = "test-model.html"
        template = env.get_template(template_file)
        content = template.render(
            model = model,
            spec_dir = spec_dir,
            result_dir = result_dir,
            index_refs = index_refs,
            find_workers = find_workers,
            toc = toc,
            RefTlc = TestCaseType_RefTlc,
            RefApalache = TestCaseType_RefApalache,
            RefAnomalous = TestCaseType_RefAnomalous,
            os = os)

        html_file = f'test-model-{id}.html'
        save_file(os.path.join(html_dir, html_file), content)

def generate_main_html(env, html_dir, spec, results, toc):
        statistics = calculate_statistics(spec, results)

        template_file = "test-toc.html"
        template = env.get_template(template_file)
        content = template.render(workers = workers, statistics = statistics, toc = toc)

        html_file = template_file
        save_file(os.path.join(html_dir, html_file), content)

def get_index_toc_html(env):
        template_file = "test-side-toc.html"
        template = env.get_template(template_file)
        return template.render(workers = workers)

def add_model(models, tc, model, result):
    id = model['id']
    if id not in models:
        models[id] = model
        models[id]['test_cases'] = [tc]
        models[id]['result'] = result
    else:
        models[id]['test_cases'].append(tc)

def generate_html_report(
        spec_dir,
        spec_file,
        exec_dir,
        exec_report_file,
        output_dir):

    html_dir = os.path.join(output_dir, 'html')
    os.makedirs(html_dir, exist_ok = True)

    # Load test specification
    with open(spec_file) as spec_h:
        spec = json.load(spec_h)

    # Load test results
    with open(exec_report_file) as report_h:
        results = json.load(report_h)

    # Enrich a model specification with test case and test result information
    models = {}
    for tc_id, tc in spec.items():
        if tc['type'] != 'skipped':
            add_model(models, tc, tc['tlc'], results[tc_id]['tlc_status'])
            # Anomalous conditions tests have no reference model
            if tc['type'] != TestCaseType_RefAnomalous:
                add_model(models, tc, tc['ref'], results[tc_id]['ref_status'])

    # Generate HTML site
    template_path = get_template_path()
    env = Environment(loader = FileSystemLoader(template_path))

    toc = get_index_toc_html(env)

    (index, features) = build_index(spec)
    index_refs = generate_index_html(env, html_dir, index, results, toc)

    generate_main_html(env, html_dir, spec, results, toc)
    generate_feature_toc(env, html_dir, index_refs, features, toc)
    generate_index_skipped_html(env, html_dir, spec, toc)
    generate_failed_html(env, html_dir, spec, results, toc)
    generate_anomalous_html(env, html_dir, spec, results, toc)

    generate_models_html(env, html_dir, spec_dir, exec_dir, models, index_refs, toc)

    copy_site_file('style.css', html_dir)
    copy_site_file('index.html', output_dir)
