#!/bin/bash
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

set -eo pipefail

TOOL_DIR=$( readlink -f `dirname $0` )
TLA_SRC=${TOOL_DIR}/../coverage/tlaplus/tlatools/org.lamport.tlatools/src

SOURCES="
    --sourcefiles ${TLA_SRC}/model \
    --sourcefiles ${TLA_SRC}/tla2sany \
    --sourcefiles ${TLA_SRC}/tlc2 \
    --sourcefiles ${TLA_SRC}/util"

java \
    -jar ${TOOL_DIR}/jacoco-0.8.8/jacococli.jar \
    report $1 \
    --classfiles ${TOOL_DIR}/1.7.2/tla2tools.jar \
    --html $1.report \
    --name the-report \
    ${SOURCES}