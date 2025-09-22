#!/bin/bash
#
# SPDX-FileCopyrightText: Copyright (c) 2019 NVIDIA CORPORATION & AFFILIATES. All rights reserved.
#

set -eo pipefail
readonly PROJECT_DIR=$( readlink -f `dirname $0`/.. )
readonly CPUS=$( nproc )
readonly REPORT_DIR=${PROJECT_DIR}/mount/tqr
python -m testgen -o ${REPORT_DIR} -s -e --html -x ${PROJECT_DIR}/explanation.yaml -w ${CPUS} $*
