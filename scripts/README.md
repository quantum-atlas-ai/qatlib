# Qatlib Scripts

This directory contains the Lean maintenance and verification executables registered in [`lakefile.toml`](../lakefile.toml):

- **`get_cache.lean`** (`lake exe get_cache`):
  Fetches precompiled build caches for upstream `Mathlib`, `Physlib`, and `Qatlib`.
- **`lint.lean`** (`lake lint` or `lake exe lint`, configured as `lintDriver = "lint"`):
  Fast, read-only static source, style, and import graph linter (~1 second):
  1. **Source & Style Check**: Verifies Apache-2.0 copyright headers, allowed top-level `Qatlib/` directories (`Foundations`, `Concepts`, `Papers`), strict `UpperCamelCase` names, Unix `\n` line endings, no trailing whitespace, no space before semicolons, and no forbidden debug `set_option` commands.
  2. **Module Tree & Import Check**: Verifies that `Qatlib.lean` imports all modules under `Qatlib/` in sorted order, no bare `import Mathlib` exists, and all `import Qatlib.*` statements resolve to existing source files.
- **`test.lean`** (`lake test` or `lake exe test`, configured as `testDriver = "test"`):
  Kernel-level `.olean` environment soundness and axiom auditor. Loads the compiled `Qatlib` environment into the Lean 4 kernel and verifies via `Lean.collectAxioms` (transitive axiom closure) that every declaration in `Qatlib` is `sorry`-free (`0 sorryAx`), avoids unverified evaluation (`Lean.ofReduceBool` / `native_decide`), and depends exclusively on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
