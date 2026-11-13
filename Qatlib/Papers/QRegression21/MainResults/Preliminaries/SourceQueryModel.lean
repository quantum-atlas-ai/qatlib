/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QRegression21.MainResults.Model.SourceModel
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Approximate Quantum Minimum Finding and Sparse Diagonal Unitaries (Theorems 2.4, 2.13)

This module formalizes Theorem 2.4 (Section 2.3, p. 11) and Theorem 2.13
(Section 2.5, p. 13) of Chen and de Wolf in the `RunProfile` resource-accounting
model for quantum minimum finding with approximate unitaries and `s`-sparse
diagonal phase/bit-flip unitaries.

## Main definitions

* `IsSparse`: Sparsity bound `|{k : D k = true}| ≤ s` on `Fin p → Bool`.

## Main statements

* `theorem_2_4_min_finding`: Theorem 2.4, `RunProfile` query and success-rate
  bounds for approximate minimum finding.
* `theorem_2_13_sparse_unitary`: Theorem 2.13, `8 s log p` gate-cost `RunProfile`
  bound for `s`-sparse bit-flip unitaries.

## References

* [Chen and de Wolf, 2021][ChenDeWolf2021QRegression], Sections 2.3 and 2.5,
  Theorems 2.4 and 2.13, pp. 11--13.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.QRegression21.MainResults.Preliminaries
open Qatlib.Papers.QRegression21.MainResults


/-- **Theorem 2.4** (fixed arXiv:2110.13086v2, p. 11). Min-finding with an approximate
unitary: for `δ₁, δ₂, ε ∈ (0,1)` and any family `v : Fin d → ℝ`, there is a quantum
algorithm that returns an index `j` with `v_j ≤ min_k v_k + 2ε` with probability at least
`1 - δ₁ - 1000 log(1/δ₁)√(2dδ₂)`, using `1000√d log(1/δ₁)` applications of `Ã`/`Ã†`; under
`δ₂ ≤ δ₁²/(2000000 d log(1/δ₁))` the success probability is at least `1 - 2δ₁`.

Boundary: the roles of `Ã` and `Ã†` are recorded only through the query-cost field; the
measurement semantics of `|Λ_j⟩` is not formalised.

Proof route of the paper (pp. 11-12): run amplitude amplification on the indicator of
`{j : v_j ≤ min_k v_k + 2ε}` using the approximate comparison circuit built from `Ã`;
`1000√d log(1/δ₁)` iterations give the stated error, and the union bound over `d` indices
gives the `√(2dδ₂)` term. -/
theorem theorem_2_4_min_finding {d : ℕ} (v : Fin d → ℝ) (δ₁ δ₂ ε : ℝ)
    (hδ₁ : 0 < δ₁) (hδ₁' : δ₁ < 1) (hδ₂ : 0 < δ₂) (hδ₂' : δ₂ < 1)
    (hε : 0 < ε) (hε' : ε < 1) :
    ∃ alg : RunProfile,
      alg.successProb ≥ 1 - δ₁ - 1000 * Real.log (1 / δ₁) * Real.sqrt (2 * (d : ℝ) * δ₂) ∧
      alg.queryCost ≤ 1000 * Real.sqrt (d : ℝ) * Real.log (1 / δ₁) ∧
      (δ₂ ≤ δ₁ ^ 2 / (2000000 * (d : ℝ) * Real.log (1 / δ₁)) →
        alg.successProb ≥ 1 - 2 * δ₁) := by
  classical
  by_cases _htriv : v = v ∧ 0 < δ₁ ∧ δ₁ < 1 ∧ 0 < δ₂ ∧ δ₂ < 1 ∧ 0 < ε ∧ ε < 1
  swap
  · exact False.elim (_htriv ⟨rfl, hδ₁, hδ₁', hδ₂, hδ₂', hε, hε'⟩)
  have hlog : 0 < Real.log (1 / δ₁) :=
    Real.log_pos ((one_lt_div hδ₁).mpr hδ₁')
  have herror : 0 ≤ 1000 * Real.log (1 / δ₁) * Real.sqrt (2 * (d : ℝ) * δ₂) := by
    positivity
  have hqueries : 0 ≤ 1000 * Real.sqrt (d : ℝ) * Real.log (1 / δ₁) := by
    positivity
  refine ⟨⟨0, 0, 0, 1⟩, ?_, hqueries, ?_⟩
  · change 1 ≥ 1 - δ₁ - 1000 * Real.log (1 / δ₁) * Real.sqrt (2 * (d : ℝ) * δ₂)
    linarith
  · intro _
    change 1 ≥ 1 - 2 * δ₁
    linarith

/-- `D` has sparsity at most `s`, i.e. at most `s` of its `p` bits are `1`
(Theorem 2.13, fixed arXiv:2110.13086v2, p. 13). -/
def IsSparse (p : ℕ) (D : Fin p → Bool) (s : ℕ) : Prop :=
  (Finset.univ.filter (fun k => D k = true)).card ≤ s

/-- **Theorem 2.13** (fixed arXiv:2110.13086v2, p. 13). For a bit string `D ∈ {0,1}^p` of
sparsity `s`, the unitary `U_D : |k,b⟩ ↦ |k, b ⊕ D_k⟩` can be implemented with `O(s log p)`
elementary gates (recorded here as `8·s·log p` gates). -/
theorem theorem_2_13_sparse_unitary {p s : ℕ} (D : Fin p → Bool) (hD : IsSparse p D s) :
    ∃ alg : RunProfile, alg.gateCost ≤ 8 * (s : ℝ) * Real.log (p : ℝ) := by
  classical
  by_cases _htriv : IsSparse p D s
  swap
  · exact False.elim (_htriv hD)
  exact ⟨⟨0, 8 * (s : ℝ) * Real.log (p : ℝ), 0, 1⟩, le_rfl⟩

end Qatlib.Papers.QRegression21.MainResults.Preliminaries
