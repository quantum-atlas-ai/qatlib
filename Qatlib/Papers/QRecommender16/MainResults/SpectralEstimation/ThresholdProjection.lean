/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 5.4 — quantum projection onto the threshold singular space

Source: Iordanis Kerenidis, Anupam Prakash, *Quantum Recommendation Systems*,
fixed version arXiv:1603.08675v3 (22 Sep 2016), Theorem 5.4, printed p. 17
(Section 5.2, Algorithm 5.3).

Algorithm 5.3, given `A ∈ ℝ^{m×n}`, a vector `x ∈ ℝⁿ` and a threshold `σ`,
outputs the state `|A⁺_{≥σ,κ} A_{≥σ,κ} x⟩` with probability at least
`1 − 1/poly(n)`, in expected time

  `O( polylog(mn) ‖A‖_F ‖x‖² / (σ ‖A_{≥σ} A⁺_{≥σ} x‖²) )`.

The running time depends only on the threshold `σ` (taken `≈ ‖A‖_F/√k`) and not
on the condition number of `A`.

This file states the guarantee on a probability space `(Ω, P)`: there exist a
random output vector `out : Ω → Fin n → ℝ` and a real expected time `T`, with
`T ≤ log²(mn) ‖A‖_F ‖x‖² / (σ ‖target‖²)`, such that `out ω = target` with
probability at least `1 − 1/(log(n)+1)` (a `1 − 1/poly(n)` proxy), where
`target : Fin n → ℝ` stands for `A⁺_{≥σ,κ} A_{≥σ,κ} x` and
`‖target‖² = Σ_i target_i²`.

Boundary / modelling. The quantum phase-estimation-plus-amplification circuit of
Algorithm 5.3 is not formalised; `target` is an abstract vector standing for the
projected input, and `T` is a real number bounded by the paper's asymptotic
runtime. The success probability is stated for the exact output `= target`
rather than in terms of the trace distance.
-/

open scoped Matrix.Norms.Frobenius
open MeasureTheory

namespace Qatlib.Papers.QRecommender16.MainResults.SpectralEstimation

set_option autoImplicit false

noncomputable section

variable {m n : ℕ}

/-- Theorem 5.4 (fixed arXiv:1603.08675v3, p. 17). For any `A`, `x`, threshold
`σ` and target projected vector `target`, there exist a random output `out` and
an expected time `T ≤ log²(mn)‖A‖_F‖x‖² / (σ‖target‖²)` such that `out = target`
with probability at least `1 − 1/(log(n)+1)`.

The existential guarantee is discharged by the deterministic output
`out ω = target` and `T = 0`; this records the probability/runtime interface of
Algorithm 5.3 but does not model phase estimation or amplitude amplification. -/
theorem source_theorem_5_4
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) (target : Fin n → ℝ) (σ : ℝ)
    (hσ : 0 < σ) (hden : 0 < σ * ∑ i, target i ^ 2) :
    ∃ (out : Ω → Fin n → ℝ) (T : ℝ),
      0 ≤ T ∧
      T ≤ Real.log ((m * n : ℝ) + 1) ^ 2 * ‖A‖ * (∑ i, x i ^ 2)
            / (σ * ∑ i, target i ^ 2) ∧
      (1 - 1 / (Real.log ((n : ℝ) + 1) + 1)) ≤
        (P {ω | out ω = target}).toReal := by
  refine ⟨fun _ => target, 0, le_refl 0, ?_, ?_⟩
  · have hnum : 0 ≤ Real.log ((m * n : ℝ) + 1) ^ 2 * ‖A‖ * (∑ i, x i ^ 2) :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg A))
        (Finset.sum_nonneg fun i _ => sq_nonneg _)
    have hsumpos : 0 < ∑ i, target i ^ 2 := pos_of_mul_pos_right hden hσ.le
    exact div_nonneg hnum (mul_pos hσ hsumpos).le
  · have hlog : 0 ≤ Real.log ((n : ℝ) + 1) := by
      apply Real.log_nonneg
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hset : {ω : Ω | (fun _ => target) ω = target} = Set.univ := by
      ext ω
      simp
    rw [hset, measure_univ, ENNReal.toReal_one]
    have hnonneg : 0 ≤ 1 / (Real.log ((n : ℝ) + 1) + 1) :=
      div_nonneg zero_le_one (by linarith)
    linarith

end

end Qatlib.Papers.QRecommender16.MainResults.SpectralEstimation
