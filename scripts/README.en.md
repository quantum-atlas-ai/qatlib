# Qatlib Scripts

> 🌐 [中文版](./README.md)

This directory contains the Lean maintenance and verification executables registered in [`lakefile.toml`](../lakefile.toml), along with the documentation portal builder:

- **`get_cache.lean`** (`lake exe get_cache`):
  Fetches three-tier precompiled build caches for upstream `Mathlib`, `Physlib`, and `Qatlib` as configured in [`lake-cache.toml`](../lake-cache.toml).
- **`lint.lean`** (`lake lint` or `lake exe lint`, configured as `lintDriver = "lint"`):
  Fast, read-only static source, style, and import graph linter (~1 second across the library):
  1. **Source & Style Check**: Verifies Apache-2.0 copyright headers, allowed top-level `Qatlib/` directories (`Foundations`, `Concepts`, `Papers`), strict `UpperCamelCase` directory and file names, zero case-insensitive path collisions (`ERR_CASE`), Unix `\n` line endings, no trailing whitespace, no space before semicolons, and no forbidden debug `set_option` commands.
  2. **Module Tree & Layer Check**: Verifies that `Qatlib.lean` imports all modules under `Qatlib/` in sorted order, no bare `import Mathlib` exists, every `import Qatlib.*` statement resolves to an existing source file, and dependencies strictly follow `Foundations ← Concepts ← Papers` (reverse imports report `ERR_LAY`).
- **`test.lean`** (`lake test` or `lake exe test`, configured as `testDriver = "test"`):
  Kernel-level `.olean` environment soundness and axiom auditor. Loads the compiled `Qatlib` environment into the Lean 4 kernel and verifies via `Lean.collectAxioms` (transitive axiom closure) that every declaration in `Qatlib` is `sorry`-free (`0 sorryAx`), avoids unverified evaluation (`Lean.ofReduceBool` / `native_decide`), and depends exclusively on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
- **`build_site.py`** (`python3 scripts/build_site.py`):
  Dependency-free Python generator that assembles the bilingual documentation portal, interactive module explorer, `docs/references.bib` bibliography explorer, and `doc-gen4` API reference into a unified GitHub Pages artifact (configured in [`.github/workflows/docs.yml`](../.github/workflows/docs.yml)).
