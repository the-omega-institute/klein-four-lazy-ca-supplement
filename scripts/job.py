#!/usr/bin/env python3
"""Run a tracked foreground job; termination is restricted to this job's PID."""
import datetime
import os
import pathlib
import signal
import subprocess
import sys

log_path, *command = sys.argv[1:]
with open(log_path, "w") as log:
    child = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             start_new_session=True, text=True)
    with open("jobs.txt", "a") as jobs:
        jobs.write(f"{datetime.datetime.now(datetime.timezone.utc).isoformat()} PID {child.pid}: {' '.join(command)}; {log_path}\n")
    print(f"PID {child.pid}; log {log_path}", flush=True)
    try:
        for line in child.stdout:
            log.write(line)
            log.flush()
            print(line, end="", flush=True)
        result = child.wait()
    except KeyboardInterrupt:
        os.killpg(child.pid, signal.SIGTERM)
        result = child.wait()
    with open("jobs.txt", "a") as jobs:
        jobs.write(f"PID {child.pid}: exited {result}\n")
sys.exit(result)
