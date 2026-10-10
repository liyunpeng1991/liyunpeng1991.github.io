#!/bin/sh
set -eu

PROJECT_DIR=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$PROJECT_DIR"
LOCAL_BIN="$PROJECT_DIR/.tools/lean-4.35.0-rc4-darwin_aarch64/bin"
if [ -x "$LOCAL_BIN/lean" ]; then
  PATH="$LOCAL_BIN:$PATH"
  export PATH
fi

python3 scripts/run_logged.py verification-lean-version -- lean --version
python3 scripts/run_logged.py verification-lake-version -- lake --version
python3 scripts/run_logged.py clean-project -- python3 -c 'import shutil; shutil.rmtree(".lake/build", ignore_errors=True)'
python3 scripts/run_logged.py clean-build -- lake build
for source in MaximumModulus/*.lean MaximumModulus.lean; do
  label=$(basename "$source" .lean)
  python3 scripts/run_logged.py "target-$label" -- lake env lean "$source"
done
python3 scripts/run_logged.py axioms -- lake env lean CheckAxioms.lean
for source in MaximumModulus/*.lean; do
  label=$(basename "$source" .lean)
  python3 scripts/run_logged.py "kernel-$label" -- lake env leanchecker --verbose "MaximumModulus.$label"
done
python3 scripts/run_logged.py source-integrity -- python3 scripts/source_integrity.py
python3 scripts/run_logged.py verification-summary-command -- python3 scripts/summarize_verification.py
