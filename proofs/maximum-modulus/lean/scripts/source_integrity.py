#!/usr/bin/env python3
"""Audit this project's source and exact dependency checkouts; no theorem inference."""
import hashlib
import json
import pathlib
import re
import subprocess

root = pathlib.Path(__file__).resolve().parent.parent
manifest = json.loads((root / "lake-manifest.json").read_text())
dependencies = []
for package in manifest["packages"]:
    checkout = root / ".lake" / "packages" / package["name"]
    actual = subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
    assert actual == package["rev"], (package["name"], actual, package["rev"])
    dirty = subprocess.check_output(["git", "-C", str(checkout), "status", "--porcelain", "--untracked-files=no"], text=True).strip()
    assert not dirty, (package["name"], dirty)
    dependencies.append({"name": package["name"], "revision": actual, "url": package["url"], "tracked_tree": "clean"})
paths = [root / "MaximumModulus.lean", root / "CheckAxioms.lean", *sorted((root / "MaximumModulus").glob("*.lean"))]
for path in paths:
    text = path.read_text()
    code = re.sub(r"/-.*?-/|--[^\n]*", "", text, flags=re.S)
    assert not re.search(r"\b(sorry|admit|sorryAx|axiom|native_decide|implemented_by|extern)\b|debug\.skipKernelTC", code), path
hash_paths = paths + [root / "lean-toolchain", root / "lakefile.toml", root / "lake-manifest.json"] + sorted((root / "scripts").glob("*.*"))
hashes = {str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest() for path in hash_paths}
manuscript = root.parent / "maximum_modulus_points.tex"
manuscript_hash = hashlib.sha256(manuscript.read_bytes()).hexdigest()
expected = "bc951c3ffa7d3579b2f39a0949e38db27338ac32ac050e3f5359d4452573a7b1"
assert manuscript_hash == expected, "The manuscript differs from the original read."
report = {"dependencies": dependencies, "source_sha256": hashes, "manuscript_sha256": manuscript_hash,
          "scan": "No prohibited placeholder/custom-axiom/native-computation/kernel-skip keywords in project Lean code after removing comments."}
(root / "logs" / "source-integrity-data.json").write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report, indent=2))
