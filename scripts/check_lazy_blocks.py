#!/usr/bin/env python3
"""Compile finite verification blocks sequentially, recording every build PID."""
import datetime
import subprocess
import sys

for block in range(63):
    command = ["lake", "build", f"KleinFour.LazyBlocks.Block{block:02}"]
    child = subprocess.Popen(command)
    with open("jobs.txt", "a") as jobs:
        jobs.write(f"{datetime.datetime.now(datetime.timezone.utc).isoformat()} PID {child.pid}: {' '.join(command)}\n")
    print(f"Checking block {block+1}/63; PID {child.pid}", flush=True)
    result = child.wait()
    with open("jobs.txt", "a") as jobs:
        jobs.write(f"PID {child.pid}: exited {result}\n")
    if result:
        sys.exit(result)
