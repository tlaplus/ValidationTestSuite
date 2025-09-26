#!/bin/bash
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