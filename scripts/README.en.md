# Qatlib Scripts

> 🌐 [中文版](./README.md)

This directory contains the Lean maintenance and verification executables registered in [`lakefile.toml`](../lakefile.toml), along with the documentation portal builder:

- **`get_cache.lean`** (`lake exe get_cache`):
  Fetches three-tier precompiled build caches for upstream `Mathlib`, `Physlib`, and `Qatlib` as configured in [`lake-cache.toml`](../lake-cache.toml).
- **`lint.lean`** (`lake lint` or `lake exe lint`, configured as `lintDriver = "lint"`):
  Read-only static source, style, import, fidelity, and bibliography linter:
  1. **Source & Style Check**: Verifies Apache-2.0 copyright headers, allowed top-level `Qatlib/` directories (`Foundations`, `Concepts`, `Papers`), strict `UpperCamelCase` directory and file names, zero case-insensitive path collisions (`ERR_CASE`), Unix `\n` line endings, no trailing whitespace, no space before semicolons, and no forbidden debug `set_option` commands.
  2. **Module Tree & Layer Check**: Verifies that `Qatlib.lean` imports all modules under `Qatlib/` in sorted order, no bare `import Mathlib` exists, every `import Qatlib.*` statement resolves to an existing source file, and dependencies strictly follow `Foundations ← Concepts ← Papers` (reverse imports report `ERR_LAY`).
- **`test.lean`** (`lake test` or `lake exe test`, configured as `testDriver = "test"`):
  Kernel-level `.olean` environment soundness and axiom auditor. Loads the compiled `Qatlib` environment into the Lean 4 kernel and verifies via `Lean.collectAxioms` (transitive axiom closure) that every declaration in `Qatlib` is `sorry`-free (`0 sorryAx`), avoids unverified evaluation (`Lean.ofReduceBool` / `native_decide`), and depends exclusively on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- **`build_site.py`** (`python3 scripts/build_site.py`):
  Dependency-free Python generator that assembles the bilingual documentation portal, interactive module explorer, `docs/references.bib` bibliography explorer, and `doc-gen4` API reference into a unified GitHub Pages artifact (configured in [`.github/workflows/docs.yml`](../.github/workflows/docs.yml)).
- **`docs_cache.py` / `build_docs.sh`**:
  A self-maintained documentation snapshot protocol stored in R2, separate from Lake's compiled artifact cache. It depends on doc-gen4 internals rather than a stable public interface. HTML reuse requires an exact fingerprint of source and rendering inputs; analysis reuse requires compatible Lean toolchains, dependency locks and protocol identifiers. Portal text changes can reuse raw HTML.

  On an exact HTML miss, both hosted and self-hosted runners restore compatible analysis and generate HTML incrementally for the current source. Compiled Lean cache lookup tries identical inputs, the current commit and the most recent 25 ancestors; Lake validates dependency hashes and builds missing or stale modules. Without `LAKE_CACHE_KEY`, generation, portal validation and Pages deployment remain available while R2 snapshot uploads are skipped; workflow settings still control Pages deployment. `CHANGELOG.md` changes trigger portal updates. Documentation-only PRs return a successful `Build and kernel audit` result after lightweight change classification; Lean, dependency and build-tool changes still require compilation and kernel auditing.

  Objects live under `docs/quantum-atlas-ai/qatlib/tc/<toolchain>/`:

  ```text
  html/<fingerprint>.tar.gz
  html/<fingerprint>.json
  analysis/<compatible>/latest.tar.gz
  analysis/<compatible>/latest.json
  ```

  Each JSON contains only the protocol identifier, input fingerprint, compatibility key and archive SHA-256. Archives sort paths, zero tar/gzip timestamps and uid/gid, clear user/group names and normalize permissions. Writers must run serially: upload the archive, read it back to verify its checksum, then publish JSON. Readers validate compatibility, checksums and contents before replacing local output. An interruption between the two writes can cause a checksum failure; publishing a complete snapshot again repairs the pair. SQLite backup captures committed WAL data together with `.doc` analysis markers, excluding HTML rendering markers. Only when the direct analysis archive is absent, readers may follow the previous `latest.json` to `objects/<sha256>.tar.gz`. The next publication migrates it to direct storage without writing the old object path.

  `DOCGEN_SRC=github` and the canonical Git remote select the source repository. The pinned doc-gen4 v4.35 still embeds the build commit and has no environment override for a branch, so Qatlib `source_url` values are normalized to public `main` links before HTML rendering, including builds without upload credentials. Before restore, pruning or publication, `assert_analysis_schema` checks `modules(name TEXT PRIMARY KEY, source_url TEXT)` and cascading deletion of dependent rows, with explicit upgrade instructions on mismatch. doc-gen4 retains responsibility for validating other tables and serialized data.

  Analysis packaging keeps only `schemaVersion` and `depHash` in copies of `.doc.trace` and bibliography preprocessing `.trace` JSON. Lake v4.35 checks these markers using the dependency hash and file existence; omitted `inputs` and `log` default to empty, and `outputs` defaults to null. Removing dependency path captions and logs therefore preserves cache hits. Local traces remain intact; the archived database, markers and HTML must still pass strict publication content checks.

  When upgrading Lean or doc-gen4, review `srcUri.github` in `lakefile.lean`, `DocGen4/DB/Schema.lean`, `BuildMetadata` parsing and marker checks in `Lake/Build/Common.lean`, analysis/rendering marker conventions and the script's schema guards. Run `python3 scripts/test_docs_pipeline.py` and verify cold builds, incremental restore, deleted-module pruning and final source links. Bump `FORMAT` and rebuild analysis for incompatible protocol semantics; preserve compatibility keys for storage-only migrations or removal of trace diagnostic fields so existing analysis remains reusable.
