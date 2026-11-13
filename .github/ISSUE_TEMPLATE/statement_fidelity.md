---
name: Statement Fidelity Report
about: Report a discrepancy between a formalized Lean statement/model and its source paper
title: "[Fidelity] "
labels: ["fidelity", "mathematics"]
---

## Source Paper & Claim

- **Paper directory**: e.g. `Qatlib/Papers/TriangleFind14/`
- **Module & declaration**: e.g. `Qatlib.Papers.TriangleFind14.MainResults.SourceTheorem11.theorem1_1`
- **Source citation**: arXiv ID / DOI, Theorem / Lemma / Equation number, and page

## Nature of Discrepancy

- [ ] **Missing hypothesis / premise** (statement is false or vacuous in ZFC without an implicit paper assumption)
- [ ] **Permissive / unconstrained model field** (conclusion is trivially satisfiable due to unconstrained cost/output fields)
- [ ] **Weaker or stronger statement than source** (docstring or name over-claims what the Lean type proves)
- [ ] **Source paper erratum / counterexample** (source claim itself requires correction)

## Mathematical Details

<!-- Explain the discrepancy, counterexample, or trivial witness, and the mathematically faithful Lean formulation. -->

## Proposed Resolution

<!-- Suggested hypothesis, model constraint, or docstring/scope clarification. -->
