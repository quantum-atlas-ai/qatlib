/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QRegression21.MainResults.Model.SourceModel
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# SourceQueryModel

The `_statement` definitions are unproved resource specifications requiring an
implementation relation. Numeric records alone do not certify execution or correctness.
No quantum circuit synthesis is proved here.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.QRegression21.MainResults.Preliminaries
open Qatlib.Papers.QRegression21.MainResults


/-- **Statement only — not proved in Qatlib.** Resource specification for `theorem_2_4_min_finding`.
`Realizes` must certify the intended output, error or success event and an
implementation whose counted operations equal the recorded resources. No such
implementation is constructed here. The explicit numeric bounds are specifications. -/
def theorem_2_4_min_finding_statement {d : ℕ} (v : Fin d → ℝ) (δ₁ δ₂ ε : ℝ)
    (hδ₁ : 0 < δ₁) (hδ₁' : δ₁ < 1) (hδ₂ : 0 < δ₂) (hδ₂' : δ₂ < 1)
    (hε : 0 < ε) (hε' : ε < 1)
    (Realizes : RunProfile → (Fin d → Prop) → Prop) : Prop :=
    ∃ alg : RunProfile, Realizes alg (fun j => ∀ k, v j ≤ v k + 2 * ε) ∧
      alg.successProb ≥ 1 - δ₁ - 1000 * Real.log (1 / δ₁) * Real.sqrt (2 * (d : ℝ) * δ₂) ∧
      alg.queryCost ≤ 1000 * Real.sqrt (d : ℝ) * Real.log (1 / δ₁) ∧
      (δ₂ ≤ δ₁ ^ 2 / (2000000 * (d : ℝ) * Real.log (1 / δ₁)) →
        alg.successProb ≥ 1 - 2 * δ₁)


/-- `D` has sparsity at most `s`, i.e. at most `s` of its `p` bits are `1`
(Theorem 2.13, fixed arXiv:2110.13086v2, p. 13). -/
def IsSparse (p : ℕ) (D : Fin p → Bool) (s : ℕ) : Prop :=
  (Finset.univ.filter (fun k => D k = true)).card ≤ s

/-- **Statement only — not proved in Qatlib.** Resource specification for `theorem_2_13_sparse_unitary`.
`Realizes` must certify the intended output, error or success event and an
implementation whose counted operations equal the recorded resources. No such
implementation is constructed here. The explicit numeric bounds are specifications. -/
def theorem_2_13_sparse_unitary_statement {p s : ℕ} (D : Fin p → Bool) (hD : IsSparse p D s)
    (Realizes : RunProfile → Prop) : Prop :=
    ∃ alg : RunProfile, Realizes alg ∧ alg.gateCost ≤ 8 * (s : ℝ) * Real.log (p : ℝ)


end Qatlib.Papers.QRegression21.MainResults.Preliminaries
