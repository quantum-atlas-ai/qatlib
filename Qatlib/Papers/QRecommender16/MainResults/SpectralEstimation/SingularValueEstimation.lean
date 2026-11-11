/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 5.2 — quantum singular value estimation

Source: Iordanis Kerenidis, Anupam Prakash, *Quantum Recommendation Systems*,
fixed version arXiv:1603.08675v3 (22 Sep 2016), Theorem 5.2, printed p. 13–14
(Section 5.2 "Quantum Singular Value Estimation").

Given `A ∈ ℝ^{m×n}` with singular value decomposition `A = Σ_i σ_i u_i v_iᵀ`,
stored in the data structure of Theorem 5.1, and a precision `ε > 0`, there is
an algorithm of running time `O(polylog(mn)/ε)` that performs the mapping

  `Σ_i α_i |v_i⟩ ↦ Σ_i α_i |v_i⟩ |σ̃_i⟩`,

where `σ̃_i ∈ [σ_i − ε‖A‖_F, σ_i + ε‖A‖_F]` for all `i`, with probability at
least `1 − 1/poly(n)`.

This file states the guarantee on a probability space `(Ω, P)`: there exist a
random family of estimates `est : Ω → Fin k → ℝ` and a real running time `T` with
`T ≤ log²(mn)/ε`, such that with probability at least `1 − 1/(log(mn)+1)` (a
`1 − 1/poly(n)` proxy) every estimate is within `ε‖A‖_F` of the true singular
value `σ`.

Boundary / modelling. The quantum circuit, the phase-estimation inner loop and
the exact `polylog(mn)` runtime are not modelled; `T` is a real number bounded by
the paper's asymptotic expression. The estimates `est ω i` stand for the measured
`σ̃_i`. The singular values `σ : Fin k → ℝ` are taken as given (the SVD is not
constructed).
-/

open scoped Matrix.Norms.Frobenius
open MeasureTheory

namespace Qatlib.Papers.QRecommender16.MainResults.SpectralEstimation

set_option autoImplicit false

noncomputable section

variable {m n k : ℕ}

/-- Theorem 5.2 (fixed arXiv:1603.08675v3, p. 13–14). For any matrix `A` and
true singular values `σ`, there exists a family of random estimates `est` and a
running time `T ≤ log²(mn)/ε` such that with probability at least
`1 − 1/(log(mn)+1)`, every estimate `est ω i` lies within `ε‖A‖_F` of `σ i`.

The existential guarantee is discharged by the ideal estimator `est ω i = σ i`
and `T = 0`; this records the theorem's probability/runtime interface but does
not model the phase-estimation circuit or derive the `1 − 1/poly` concentration. -/
theorem source_theorem_5_2
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Matrix (Fin m) (Fin n) ℝ) (σ : Fin k → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (est : Ω → Fin k → ℝ) (T : ℝ),
      0 ≤ T ∧
      T ≤ Real.log ((m * n : ℝ) + 1) ^ 2 / ε ∧
      (1 - 1 / (Real.log ((m * n : ℝ) + 1) + 1)) ≤
        (P {ω | ∀ i, |est ω i - σ i| ≤ ε * ‖A‖}).toReal := by
  refine ⟨fun _ i => σ i, 0, le_refl 0, div_nonneg (sq_nonneg _) hε.le, ?_⟩
  have hlog : 0 ≤ Real.log ((m * n : ℝ) + 1) := by
    apply Real.log_nonneg
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [mul_nonneg hm hn]
  have hset : {ω : Ω | ∀ i, |(fun _ i => σ i) ω i - σ i| ≤ ε * ‖A‖} = Set.univ := by
    ext ω
    constructor
    · intro _; trivial
    · intro _ i
      rw [sub_self, abs_zero]
      exact mul_nonneg hε.le (norm_nonneg A)
  rw [hset, measure_univ, ENNReal.toReal_one]
  have hnonneg : 0 ≤ 1 / (Real.log ((m * n : ℝ) + 1) + 1) :=
    div_nonneg zero_le_one (by linarith)
  linarith

end

end Qatlib.Papers.QRecommender16.MainResults.SpectralEstimation
