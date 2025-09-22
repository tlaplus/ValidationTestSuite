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

import asyncio
import platform
from .testcasedefs import *

def prepare_command(program, *args):
    cmd = []
    if platform.system() == "Linux":
        cmd = 'bwrap --bind / / --ro-bind /usr /usr --proc /proc --dev /dev --tmpfs /tmp'.split(' ')

    cmd.append(program)
    cmd.extend(args)
    return cmd

# Collect shell command out of command line arguments
def collect_args(args):
    args_quoted = [f"'{arg}'" if ' ' in arg else arg for arg in args]
    return ' '.join(args_quoted)

# Run process under normal conditions
async def run_process(program, *args, env = None):
    cmd = prepare_command(program, *args)
    exec_desc = collect_args(args)
    process = await asyncio.create_subprocess_exec(
        *cmd,
        stdout = asyncio.subprocess.PIPE,
        stderr = asyncio.subprocess.STDOUT,
        env = env)

    output, _ = await process.communicate()

    return (exec_desc, process.returncode, output)

# Run process under specified anomalous conditions
async def run_process_anomalous(anomalous, program, *args, env = None):
    assert platform.system() != "Windows", "Not supported on Windows"

    cmd = prepare_command(program, *args)

    if anomalous['tag'] == AnomalousCondition.OutOfMemory.value:
        memory = anomalous['memory']
        limit = f"-Sv {memory} -Hv {memory}"
    elif anomalous['tag'] == AnomalousCondition.OutOfSpace.value:
        limit = f"-f {anomalous['max-file-size']}"
    elif anomalous['tag'] == AnomalousCondition.OutOfHandles.value:
        limit = f"-n {anomalous['max-handles']}"
    else:
        assert False, f'Unsupported anomalous condition {anomalous["tag"]}'

    wrapped_cmd = f"ulimit {limit}; {' '.join(cmd)}"
    process = await asyncio.create_subprocess_exec(
        '/bin/bash', '-c', wrapped_cmd,
        stdout = asyncio.subprocess.PIPE,
        stderr = asyncio.subprocess.STDOUT,
        env = env)

    exec_desc = wrapped_cmd
    output, _ = await process.communicate()

    return (exec_desc, process.returncode, output)

def run_tasks(tasks, max_concurrent_tasks):
    todo = tasks

    async def worker():
        while todo != []:
            task = todo.pop()
            await task

    workers = [worker() for _ in range(max_concurrent_tasks)]

    if asyncio.get_event_loop().is_closed():
        asyncio.set_event_loop(asyncio.new_event_loop())
    if platform.system() == "Windows":
        asyncio.set_event_loop(asyncio.ProactorEventLoop())
    loop = asyncio.get_event_loop()

    commands = asyncio.gather(*workers)
    loop.run_until_complete(commands)

    loop.close()
