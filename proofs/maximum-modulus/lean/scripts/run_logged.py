#!/usr/bin/env python3
"""Run an actual command, recording argv, cwd, full output, and exit status."""
import argparse
import datetime
import json
import os
import pathlib
import shutil
import subprocess
import sys
import time

parser = argparse.ArgumentParser()
parser.add_argument("--quiet", action="store_true")
parser.add_argument("name")
parser.add_argument("command", nargs=argparse.REMAINDER)
args = parser.parse_args()
command = args.command
if command and command[0] == "--":
    command = command[1:]
if not command:
    parser.error("missing command")
root = pathlib.Path(__file__).resolve().parent.parent
logdir = root / "logs"
logdir.mkdir(exist_ok=True)
previous_log = logdir / f"{args.name}.log"
previous_record = logdir / f"{args.name}.json"
if previous_log.exists() or previous_record.exists():
    previous_stamp = str(time.time_ns())
    if previous_record.exists():
        previous_stamp = json.loads(previous_record.read_text()).get("started_utc", previous_stamp)
    previous_stamp = previous_stamp.replace(":", "-").replace("+", "_")
    archive = logdir / "history" / previous_stamp
    archive.mkdir(parents=True, exist_ok=True)
    for previous in (previous_log, previous_record):
        if previous.exists():
            shutil.copy2(previous, archive / previous.name)
record = {
    "command": command,
    "cwd": str(pathlib.Path.cwd()),
    "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
}
started = time.monotonic()
with (logdir / f"{args.name}.log").open("wb") as out:
    result = subprocess.run(command, stdout=out, stderr=subprocess.STDOUT)
record["exit_code"] = result.returncode
record["elapsed_seconds"] = time.monotonic() - started
(logdir / f"{args.name}.json").write_text(json.dumps(record, indent=2) + "\n")
if args.quiet:
    sys.stdout.write(json.dumps(record) + "\n")
else:
    sys.stdout.write((logdir / f"{args.name}.log").read_text(errors="replace"))
sys.exit(result.returncode)
