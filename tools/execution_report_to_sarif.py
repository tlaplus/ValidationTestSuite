#!/usr/bin/env python3
#
# SPDX-FileCopyrightText: Copyright (c) 2026 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
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

import argparse
import json
import os
import sys
from typing import Any, Dict, List, Optional


PASS_VERDICT = "Passed"
LEVEL_ERROR = "error"
LEVEL_WARNING = "warning"
FALLBACK_ARTIFACT_URI = "README.md"


def read_json(path: str) -> Dict[str, Any]:
    with open(path, "r", encoding="utf-8") as handle:
        return json.load(handle)


def ensure_parent_dir(path: str) -> None:
    parent = os.path.dirname(path)
    if parent:
        os.makedirs(parent, exist_ok=True)


def to_location_uri(testcase: Dict[str, Any]) -> Optional[str]:
    """
    Prefer linking to generated spec files so SARIF entries are clickable in Actions.
    """
    tlc_desc = testcase.get("desc", {}).get("tlc", {})
    spec_rel_path = tlc_desc.get("file")
    if spec_rel_path:
        return spec_rel_path
    return None


def testcase_descriptor(testcase: Dict[str, Any], testcase_id: str) -> str:
    desc = testcase.get("desc", {})
    case_feature = desc.get("case_feature")
    plug_feature = desc.get("plug_feature")
    check_deadlock = desc.get("check_deadlock")
    if case_feature and plug_feature and check_deadlock is not None:
        return f"{case_feature}/{plug_feature} (check_deadlock={check_deadlock})"
    if "tag" in desc:
        return f"anomalous:{desc['tag']}"
    return testcase_id


def make_result(
    testcase_id: str,
    testcase: Dict[str, Any],
    level: str,
    rule_id: str,
) -> Dict[str, Any]:
    descriptor = testcase_descriptor(testcase, testcase_id)
    tlc_status = testcase.get("tlc_status", "unknown")
    ref_status = testcase.get("ref_status", "unknown")
    explanation = testcase.get("explanation")
    message = f"Validation testcase {descriptor} failed (tlc={tlc_status}, ref={ref_status})"
    if explanation:
        message += f". Explanation: {explanation}"

    uri = to_location_uri(testcase) or FALLBACK_ARTIFACT_URI

    result: Dict[str, Any] = {
        "ruleId": rule_id,
        "level": level,
        "message": {"text": message},
        "locations": [
            {
                "physicalLocation": {
                    "artifactLocation": {"uri": uri},
                    "region": {"startLine": 1},
                }
            }
        ],
        "properties": {
            "testcaseId": testcase_id,
            "tlcStatus": tlc_status,
            "refStatus": ref_status,
            "explained": bool(testcase.get("explained", False)),
            "verdict": testcase.get("verdict"),
        },
    }

    return result


def build_sarif(execution_report: Dict[str, Any]) -> Dict[str, Any]:
    unexplained_results: List[Dict[str, Any]] = []
    explained_results: List[Dict[str, Any]] = []

    for testcase_id, testcase in execution_report.items():
        verdict = testcase.get("verdict")
        if verdict == PASS_VERDICT:
            continue
        if testcase.get("explained", False):
            explained_results.append(
                make_result(
                    testcase_id=testcase_id,
                    testcase=testcase,
                    level=LEVEL_WARNING,
                    rule_id="TLA-EXPLAINED-DEVIATION",
                )
            )
        else:
            unexplained_results.append(
                make_result(
                    testcase_id=testcase_id,
                    testcase=testcase,
                    level=LEVEL_ERROR,
                    rule_id="TLA-UNEXPLAINED-DEVIATION",
                )
            )

    return {
        "version": "2.1.0",
        "$schema": "https://json.schemastore.org/sarif-2.1.0.json",
        "runs": [
            {
                "tool": {
                    "driver": {
                        "name": "TLA Validation Test Suite",
                        "informationUri": "https://github.com/tlaplus/ValidationTestSuite",
                        "rules": [
                            {
                                "id": "TLA-UNEXPLAINED-DEVIATION",
                                "name": "Unexplained deviation",
                                "shortDescription": {
                                    "text": "A testcase failed without a known explanation."
                                },
                                "fullDescription": {
                                    "text": "Unexplained testcase failures indicate a regression and should fail CI."
                                },
                                "defaultConfiguration": {"level": LEVEL_ERROR},
                            },
                            {
                                "id": "TLA-EXPLAINED-DEVIATION",
                                "name": "Explained deviation",
                                "shortDescription": {
                                    "text": "A testcase failed but is documented in explanation.yaml."
                                },
                                "fullDescription": {
                                    "text": "Explained deviations are tracked mismatches and do not fail CI."
                                },
                                "defaultConfiguration": {"level": LEVEL_WARNING},
                            },
                        ],
                    }
                },
                "results": unexplained_results + explained_results,
            }
        ],
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Convert testgen execution report to SARIF and optionally fail on unexplained regressions."
    )
    parser.add_argument(
        "--execution-report",
        required=True,
        help="Path to execution.json generated by testgen.",
    )
    parser.add_argument(
        "--sarif-output",
        required=True,
        help="Path to write generated SARIF output.",
    )
    parser.add_argument(
        "--summary-output",
        default=None,
        help="Optional path to write machine-readable summary JSON.",
    )
    parser.add_argument(
        "--fail-on-unexplained",
        action="store_true",
        default=False,
        help="Exit non-zero when unexplained failed testcases are detected.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    report = read_json(args.execution_report)
    sarif = build_sarif(report)

    ensure_parent_dir(args.sarif_output)
    with open(args.sarif_output, "w", encoding="utf-8") as handle:
        json.dump(sarif, handle, indent=2)

    total_failed = 0
    explained_failed = 0
    unexplained_failed = 0
    for testcase in report.values():
        if testcase.get("verdict") == PASS_VERDICT:
            continue
        total_failed += 1
        if testcase.get("explained", False):
            explained_failed += 1
        else:
            unexplained_failed += 1

    summary = {
        "failed_total": total_failed,
        "failed_explained": explained_failed,
        "failed_unexplained": unexplained_failed,
    }

    if args.summary_output:
        ensure_parent_dir(args.summary_output)
        with open(args.summary_output, "w", encoding="utf-8") as handle:
            json.dump(summary, handle, indent=2)

    print(
        "Execution summary:"
        f" failed_total={total_failed},"
        f" failed_explained={explained_failed},"
        f" failed_unexplained={unexplained_failed}"
    )

    if args.fail_on_unexplained and unexplained_failed > 0:
        print("Unexplained deviations detected: failing CI.")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
