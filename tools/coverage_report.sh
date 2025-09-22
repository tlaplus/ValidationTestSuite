#!/bin/bash
# SPDX-FileCopyrightText: Copyright (c) 2022 NVIDIA CORPORATION & AFFILIATES. All rights reserved.

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