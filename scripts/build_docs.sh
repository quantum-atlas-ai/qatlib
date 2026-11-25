#!/usr/bin/env bash
# Copyright (c) 2026 Qatlib Contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
set -euo pipefail

case "${LEAN_NUM_THREADS:-}" in
  ''|*[!0-9]*) echo 'LEAN_NUM_THREADS must be a positive integer' >&2; exit 1 ;;
esac
test "$LEAN_NUM_THREADS" -gt 0
unset LAKE_PKG_URL_MAP
export DISABLE_EQUATIONS=1 DOCGEN_SRC=github MATHLIB_NO_CACHE_ON_UPDATE=1
# The dependency exporter reads the public, server, and private module parts from the build tree.
export LAKE_RESTORE_ARTIFACTS=true
ROOT="$PWD"
LOG="$RUNNER_TEMP/docgen.log"
exec 9>"${DOCS_PACKAGE_CACHE:?}/.build.lock"
flock 9

# Each Docs checkout has its own package directory and analysis DB. Build never
# reads or cleans this cache. Hosted runners can use the same read-only fallback.
mkdir -p .lake
cp lean-toolchain docbuild/lean-toolchain
mkdir -p docbuild/docs
cp docs/references.bib docbuild/docs/references.bib
# doc-gen4 derives source links from origin. This isolated checkout only reads
# the canonical public remote; credentials are not persisted by checkout.
git remote set-url origin https://github.com/quantum-atlas-ai/qatlib.git

lake exe get_cache --no-qatlib
TC_DIR="$(sed -e 's|/|--|g' -e 's|:|---|g' < lean-toolchain | tr -d '[:space:]')"
INPUT_TREE="$(git rev-parse HEAD:Qatlib HEAD:Qatlib.lean HEAD:lakefile.toml HEAD:lean-toolchain HEAD:lake-manifest.json | sha256sum | cut -d' ' -f1)"
BASE="https://lake-cache.quantum-atlas.ai/revisions/quantum-atlas-ai/qatlib/tc/$TC_DIR"
CANDIDATE="$RUNNER_TEMP/docs-outputs.jsonl"
FOUND=false
for KEY in "inputs/$INPUT_TREE.jsonl" "$(git rev-parse HEAD).jsonl" $(git rev-list --max-count=25 HEAD~1 2>/dev/null || true); do
  case "$KEY" in
    *.jsonl) ;;
    *) KEY="$KEY.jsonl" ;;
  esac
  if curl --connect-timeout 10 --max-time 30 --retry 3 -fsSL \
    "$BASE/$KEY" -o "$CANDIDATE" && \
    python3 - "$CANDIDATE" <<'PY'
import json, sys
from pathlib import Path
rows = [json.loads(line) for line in Path(sys.argv[1]).read_text().splitlines()[1:] if line.strip()]
raise SystemExit(0 if any(isinstance(row, list) and len(row) >= 2 for row in rows) else 1)
PY
  then
    FOUND=true
    break
  fi
done
export LAKE_CONFIG="$ROOT/lake-cache.toml"
if [ "$FOUND" = true ]; then
  lake cache get "$CANDIDATE" --package=Qatlib --repo=quantum-atlas-ai/qatlib
fi
# Lake validates restored dependency hashes. Reuse complete artifacts or compile
# only missing/stale modules, including when no precompiled mapping is available.
if ! lake --no-build build Qatlib; then
  lake --fail-fast build --wfail Qatlib
fi
# Materialize exactly the checked-in docbuild manifest, never lake update.
lake --dir docbuild env lean --version
git diff --exit-code -- docbuild/lake-manifest.json
python3 scripts/docs_cache.py restore-analysis
python3 scripts/docs_cache.py prune

phase() {
  local label="$1" threads="$2" target="$3" started=$SECONDS
  echo "Starting $label (threads=$threads)"
  if ! LEAN_NUM_THREADS="$threads" lake --dir docbuild build "$target" > "$LOG" 2>&1; then
    tail -n 100 "$LOG"
    return 1
  fi
  echo "$label completed in $((SECONDS - started))s" | tee -a "$GITHUB_STEP_SUMMARY"
}

analyze() {
  phase coreDocs 1 @doc-gen4/coreDocs &&
    phase docInfo "$LEAN_NUM_THREADS" @Qatlib/+Qatlib:docInfo
}
if ! analyze; then
  if grep -q 'Database schema is outdated' "$LOG"; then
    python3 scripts/docs_cache.py reset
    analyze
  else
    exit 1
  fi
fi
# Canonical source links are also needed for read-only builds without an upload key.
python3 scripts/docs_cache.py normalize-analysis
# Persist expensive analysis before rendering HTML when this runner can publish.
if [ -n "${LAKE_CACHE_KEY:-}" ]; then
  python3 scripts/docs_cache.py publish-analysis
else
  echo 'No LAKE_CACHE_KEY; generating Docs without publishing R2 snapshots'
fi
python3 scripts/docs_cache.py clean-html
# A cached bibPrepass retains references.json, but clean-html removes its Bib side effect.
mkdir -p docbuild/.lake/build/doc
cp docs/references.bib docbuild/.lake/build/doc/references.bib
phase fromDb "$LEAN_NUM_THREADS" @Qatlib/Qatlib:docs
python3 scripts/build_dependency_graph.py --output-dir docbuild/.lake/build/doc
python3 scripts/docs_cache.py verify-html
if [ -n "${LAKE_CACHE_KEY:-}" ]; then
  python3 scripts/docs_cache.py publish-html
fi
