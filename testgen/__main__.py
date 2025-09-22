# SPDX-FileCopyrightText: Copyright (c) 2022 NVIDIA CORPORATION & AFFILIATES. All rights reserved.

import os
import logging
from argparse import ArgumentParser
from .ast import *
from .feature import *
from .spec import *
from .runner import *
from .explanation import *
from .html_report import *

# Enable debugging capabilities
debug = False

def any_side(*fs):
    def feature_filter(f1, f2):
        return any(f in f1 for f in fs) or any(f in f2 for f in fs)
    return feature_filter

def any_side_exact(*fs):
    def feature_filter(f1, f2):
        return any(f == f1 for f in fs) or any(f == f2 for f in fs)
    return feature_filter

def double_side(f1, f2):
    def feature_filter(f1n, f2n):
        return f1 in f1n and f2 in f2n
    return feature_filter

def load_json(file_path):
    try:
        with open(file_path) as h:
            return json.load(h)
    except FileNotFoundError:
        return None
    except json.JSONDecodeError:
        return None

def get_relative_spec_dir(output_dir):
    return 'specification'

def get_spec_dir(output_dir):
    return os.path.join(output_dir, get_relative_spec_dir(output_dir))

def get_spec_report_file(output_dir):
    spec_dir = get_spec_dir(output_dir)
    return os.path.join(spec_dir, 'specification.json')

def get_relative_exec_dir(output_dir):
    return 'execution'

def get_exec_dir(output_dir):
    return os.path.join(output_dir, get_relative_exec_dir(output_dir))

def get_exec_report_file(output_dir):
    exec_dir = get_exec_dir(output_dir)
    return os.path.join(exec_dir, 'execution.json')

def get_coverage_dir(output_dir):
    return os.path.join(output_dir, 'coverage')

def get_coverage_report_file(output_dir):
    exec_dir = get_coverage_dir(output_dir)
    return os.path.join(exec_dir, 'execution.json')

# Create/load test specification
#   output_dir: where to store the files
#   filter: predicate to select desired features
#   symmetry: if symmetry test cases have to be generated
#   force: if False, the function loads existing specification,
#          it doesn't guarantee its consistency with filter/symmetry
#
# Production shall use this function with default settings
def make_specification(output_dir, filter, symmetry, anomalous):
    spec_dir = get_spec_dir(output_dir)
    spec_file = get_spec_report_file(output_dir)

    # Generate test specification
    render_spec(spec_dir, spec_file, filter, symmetry = symmetry, anomalous = anomalous)

def execute_tests(output_dir, workers, explanation_db, force):
    spec_dir = get_spec_dir(output_dir)
    spec_file = get_spec_report_file(output_dir)
    exec_dir = get_exec_dir(output_dir)
    exec_report_file = get_exec_report_file(output_dir)
    run_testcases_parallel(
        spec_dir = spec_dir,
        spec_file = spec_file,
        exec_report_file = exec_report_file,
        exec_dir = exec_dir,
        force = force,
        workers = workers,
        explanation_db = explanation_db,
        coverage = False)

def collect_coverage(output_dir, workers):
    spec_dir = get_spec_dir(output_dir)
    spec_file = get_spec_report_file(output_dir)
    exec_dir = get_coverage_dir(output_dir)
    run_testcases_parallel(
        spec_dir = spec_dir,
        spec_file = spec_file,
        exec_report_file = None,
        exec_dir = exec_dir,
        force = True,
        workers = workers,
        explanation_db = None,
        coverage = True)

def generate_html(output_dir):
    spec_dir = get_relative_spec_dir(output_dir)
    spec_file = get_spec_report_file(output_dir)
    exec_dir = get_relative_exec_dir(output_dir)
    exec_report_file = get_exec_report_file(output_dir)

    generate_html_report(
        spec_dir = spec_dir,
        spec_file = spec_file,
        exec_dir = exec_dir,
        exec_report_file = exec_report_file,
        output_dir = output_dir)

def main():
    parser = ArgumentParser()

    parser.add_argument("-s", "--specification", dest='spec',
                        action='store_true', default=False,
                        help="Generate test specification")
    parser.add_argument("-e", "--execute", dest='execute',
                        action='store_true', default=False,
                        help="Execute tests and create execution report")
    parser.add_argument("-g", "--coverage", dest='coverage',
                        action='store_true', default=False,
                        help="Collect coverage information with JaCoCo")
    parser.add_argument("--html",
                        action='store_true', dest='html', default=False,
                        help="Create HTML report")

    parser.add_argument("-o", "--output-dir", dest="output_dir",
                        required=True,
                        help="Output directory")
    parser.add_argument("-f", "--force", dest="force",
                        action='store_true', default=False,
                        help="Force recheck cached models")
    parser.add_argument("-w", "--workers", dest="workers",
                        help="Number of workers (normally number of physical cores)", metavar="WORKERS", default = 4, type = int)
    parser.add_argument("-x", "--explanation-db", dest="explanation_db", default=None,
                        help="YAML file with tests failure explanations", metavar="FILE")
    parser.add_argument('-d', '--debug',
                        action='store_true', dest="debug", default=False,
                        help='Enable debug output')

    # Test case filtering
    parser.add_argument("-n", "--no-symmetry", dest='no_symmetry',
                        action='store_true', default=False,
                        help="Sandboxing: do not generate SYMMETRY cases")
    parser.add_argument("--no-anomalous", dest='no_anomalous',
                        action='store_true', default=False,
                        help="Sandboxing: do not test under anomalous conditions")
    filters = parser.add_mutually_exclusive_group()
    filters.add_argument("-a", "--filter-any-side", dest="filter_any_side", nargs = '+',
                        help="Sandboxing: any-side filter", metavar="VAL")
    filters.add_argument("-y", "--filter-any-side-exact", dest="filter_any_side_exact", nargs = '+',
                        help="Sandboxing: any-side-exact filter", metavar="VAL")
    filters.add_argument("-u", "--filter-double-side", dest="filter_double_side", nargs = 2,
                        help="Sandboxing: any-side-exact filter", metavar="VAL")

    args = parser.parse_args()

    # Ensure that output directory path is absolute
    args.output_dir = os.path.abspath(args.output_dir)

    global debug
    debug = args.debug
    logging.basicConfig(level = logging.DEBUG if args.debug else logging.INFO)
    logging.debug(f'Args: {args}')

    explanation_db = ExplanationDB(args.explanation_db)

    if args.spec:
        if args.filter_any_side:
            filter = any_side(*args.filter_any_side)
        elif args.filter_any_side_exact:
            filter = any_side_exact(*args.filter_any_side_exact)
        elif args.filter_double_side:
            filter = double_side(*args.filter_double_side)
        else:
            filter = any_side('')
        make_specification(
            output_dir = args.output_dir,
            filter = filter,
            symmetry = not args.no_symmetry,
            anomalous = not args.no_anomalous)

    if args.execute:
        execute_tests(
            output_dir = args.output_dir,
            workers = args.workers,
            explanation_db = explanation_db,
            force = args.force)

    if args.coverage:
        collect_coverage(
            output_dir = args.output_dir,
            workers = args.workers)

    if args.html:
        generate_html(output_dir = args.output_dir)

if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        if debug:
            logging.exception(error)
        else:
            logging.error(error)
        exit(1)
