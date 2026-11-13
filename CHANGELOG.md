# Changelog

All notable changes to **Qatlib** are documented in this file.

## Versioning Policy

* **Toolchain baseline tags (`v4.X.0`)**: Immutable tags pinned 1:1 to the initial
  verified snapshot for Lean / Mathlib / Physlib toolchain `v4.X.0`.
* **Rolling `main` branch**: Continuously receives newly proved modules,
  statement-fidelity repairs, documentation improvements, and corresponding
  precompiled Lake caches (`lake update && lake exe get_cache`).

---

## [Unreleased — `main`]

### Added
* **Lean 4 `module` system**: Migrated `Qatlib` modules to Lean v4.35 `module` /
  `public import` headers with strict zero-warning compilation (`--wfail`).
* **Third-party attribution (`NOTICE`)**: Added Apache-2.0 `NOTICE` and restored
  upstream copyright & commit provenance for adapted `TauCeti` and
  `CausalSmith` (`Causalean`) components under `Qatlib/Foundations/CbmdAnalysis/`.
* **Semantic & source-hygiene gate (`scripts/check_fidelity.py`)**: Added static
  enforcement against leaked internal workflow notes, root-namespace pollution,
  and kernel-bypass options, alongside statement-fidelity reporting templates.
* **Unified bilingual documentation portal (`scripts/build_site.py`)**: Added
  searchable module/paper explorer and transparent AI-assisted provenance and
  scope documentation.
* **Expanded `Papers/` formalizations**: Promoted additional zero-`sorry`
  formalizations across quantum algorithms, Hamiltonian simulation, query
  complexity, and quantum information literature.

### Fixed
* Repaired vacuous or over-claimed paper-layer models (`TriangleFind14`,
  `QLSBeyondCond25`, `MUBSixOpenAI26`, `SpectralGap11`, `ElemDistinct00`) so
  formalized statements and docstrings accurately reflect proved mathematical
  content.
* Scoped root-namespace declarations (`SubgroupEndpointCounterex`) and global
  typeclass instances on Mathlib types to prevent downstream namespace/instance
  pollution.
* Restored mangled `_root_.` identifiers in adapted complex-analysis modules and
  removed file-wide `set_option warningAsError false` suppressions.

---

## [`v4.35.0`] — Initial Lean v4.35.0 Baseline

* Initial open-source baseline of `Qatlib` on `leanprover/lean4:v4.35.0`,
  `mathlib4` (`v4.35.0`), and `Physlib` (`v4.35.0`), organized into
  `Foundations`, `Concepts`, and `Papers` with `lake exe get_cache`,
  `lake lint`, and `lake test` kernel axiom auditing.
