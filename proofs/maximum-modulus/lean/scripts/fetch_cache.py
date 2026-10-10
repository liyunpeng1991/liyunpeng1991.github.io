#!/usr/bin/env python3
"""Fetch only the pinned cache needed for this project's imported mathlib modules."""
import os
import pathlib
import re
import subprocess

root = pathlib.Path(__file__).resolve().parent.parent
local_bin = root / ".tools" / "lean-4.35.0-rc4-darwin_aarch64" / "bin"
env = os.environ.copy()
if (local_bin / "lake").exists():
    env["PATH"] = str(local_bin) + os.pathsep + env["PATH"]
env.setdefault("MATHLIB_CACHE_DIR", str(root / ".tools" / "mathlib-cache"))
env.setdefault("MATHLIB_CACHE_DEBUG_USE_LEGACY", "1")
modules = set()
for path in (root / "MaximumModulus").glob("*.lean"):
    modules.update(re.findall(r"^(?:public )?import (Mathlib\.[A-Za-z0-9_.]+)$", path.read_text(), re.M))
command = ["lake", "exe", "cache", "get", *sorted(modules)]
raise SystemExit(subprocess.call(command, cwd=root, env=env))
