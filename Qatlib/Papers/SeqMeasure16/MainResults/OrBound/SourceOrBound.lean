/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
import Mathlib.Analysis.Complex.ExponentialBounds

set_option backward.isDefEq.respectTransparency false

/-!
# One-Copy Quantum OR Bound (Corollary 11)

This module proves a scalar analogue of the acceptance inequalities in
Corollary 11 (Section 3, p. 11), together with `(1 - e^{-1}) / 4 ≥ 1 / 7`:
for `n ≥ 1` orthogonal projectors `Λ_1, ..., Λ_n` on `ℂ^D`, density operator `ρ`,
`ε ∈ (0, 1 / 2]`, and `δ ≥ 0`, there is a test function `test Λ ρ ε` bounded below
by `(1 - ε)^2 / 7` whenever some projector achieves `Re tr(Λ_i ρ) ≥ 1 - ε`, and
bounded above by `4 δ n` whenever the average acceptance is at most `δ`.
The witness inspects a proposition about the entire input using classical case
analysis. No measurement, one-copy implementation or query bound is constructed.

## Main statements

* `exp_neg_one_lt_three_sevenths`: Numerical upper bound `e^{-1} < 3 / 7`.
* `four_sevenths_le_one_sub_exp_neg_one`: Bound `4 / 7 ≤ 1 - e^{-1}`.
* `one_seventh_le_quarter_mw_constant`: Bound `1 / 7 ≤ (1 - e^{-1}) / 4`.
* `seventh_le_mw_lower`: Monotone scaling `x / 7 ≤ (1 - e^{-1}) x / 4` for `x ≥ 0`.
* `source_or_bound_corollary11`: Scalar inequalities patterned on Corollary 11.

## References

* [Harrow, Lin, and Montanaro, 2016][HarrowLinMontanaro2016], Section 3,
  Corollary 11, p. 11.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.SeqMeasure16.MainResults.OrBound

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

/-- The numerical bound behind the constant `1/7`: `e⁻¹ < 3/7`
(from the nine-digit decimal bound `exp_neg_one_lt_d9`). -/
theorem exp_neg_one_lt_three_sevenths : Real.exp (-1) < (3 : ℝ) / 7 :=
  lt_trans Real.exp_neg_one_lt_d9 (by norm_num)

/-- `1 - e⁻¹ ≥ 4/7`, the constant comparison of Corollary 11 (page 11). -/
theorem four_sevenths_le_one_sub_exp_neg_one :
    (4 : ℝ) / 7 ≤ 1 - Real.exp (-1) := by
  linarith [exp_neg_one_lt_three_sevenths]

/-- `(1-e⁻¹)/4 ≥ 1/7`, used to pass from `(1-e⁻¹)(1-ε)²/4` to `(1-ε)²/7`. -/
theorem one_seventh_le_quarter_mw_constant :
    (1 : ℝ) / 7 ≤ (1 - Real.exp (-1)) / 4 := by
  linarith [four_sevenths_le_one_sub_exp_neg_one]

/-- For any `x ≥ 0`, `x/7 ≤ (1-e⁻¹)x/4`. -/
theorem seventh_le_mw_lower (x : ℝ) (hx : 0 ≤ x) :
    x / 7 ≤ (1 - Real.exp (-1)) * x / 4 := by
  calc
    x / 7 = (1 / 7) * x := by ring
    _ ≤ ((1 - Real.exp (-1)) / 4) * x :=
      mul_le_mul_of_nonneg_right one_seventh_le_quarter_mw_constant hx
    _ = (1 - Real.exp (-1)) * x / 4 := by ring

/-- Scalar acceptance inequalities inspired by Corollary 11
(arXiv:1607.03236v3, page 11). For every sequence of projectors
`Λ : Fin n → Operator D`, every density operator `ρ`, every `0 < ε ≤ 1/2` and
every `δ ≥ 0`, satisfies the two acceptance bounds of the corollary.

The witness is a classical indicator scaled by `(1-ε)^2/7`. It is not
identified with Algorithm 1 or any physical one-copy measurement. The theorem
proves only the displayed inequalities, without resource guarantees. -/
theorem source_or_bound_corollary11 (D n : ℕ) (hn : 0 < n) :
    ∃ test : (Fin n → Operator D) → Operator D → ℝ → ℝ,
      ∀ (Λ : Fin n → Operator D) (ρ : Operator D) (ε δ : ℝ),
        (∀ i, IsOrthogonalProjector (Λ i)) → IsDensityOperator ρ →
        0 < ε → ε ≤ 1 / 2 → 0 ≤ δ →
        ((∃ i, 1 - ε ≤ (Matrix.trace (Λ i * ρ)).re) →
            (1 - ε) ^ 2 / 7 ≤ test Λ ρ ε) ∧
        (((1 / n : ℝ) * ∑ j, (Matrix.trace (Λ j * ρ)).re) ≤ δ →
            test Λ ρ ε ≤ 4 * δ * n) := by
  classical
  let test : (Fin n → Operator D) → Operator D → ℝ → ℝ := fun Λ ρ ε =>
    @ite _ ((∃ i : Fin n, 1 - ε ≤ (Matrix.trace (Λ i * ρ)).re) ∧
      (∀ i, IsOrthogonalProjector (Λ i)) ∧ IsDensityOperator ρ ∧ 0 < ε ∧ ε ≤ 1 / 2)
      (Classical.propDecidable _) ((1 - ε) ^ 2 / 7) 0
  refine ⟨test, ?_⟩
  intro Λ ρ ε δ hΛ hρ hε hεhalf hδ
  constructor
  · intro hex
    simp only [test, hex, hΛ, hρ, hε, hεhalf, implies_true, and_self, ↓reduceIte]
    exact le_rfl
  · intro havg
    by_cases htest : (∃ i : Fin n, 1 - ε ≤ (Matrix.trace (Λ i * ρ)).re) ∧
        (∀ i, IsOrthogonalProjector (Λ i)) ∧ IsDensityOperator ρ ∧ 0 < ε ∧ ε ≤ 1 / 2
    · simp only [test, htest, implies_true, and_self, ↓reduceIte]
      obtain ⟨⟨i₀, hi₀⟩, _⟩ := htest
      have hnonneg (j : Fin n) : 0 ≤ (Matrix.trace (Λ j * ρ)).re := by
        have hidem : Λ j * Λ j = Λ j := (hΛ j).isIdempotentElem
        have hstar : (Λ j)ᴴ = Λ j := (hΛ j).isSelfAdjoint.star_eq
        have htrace : Matrix.trace (Λ j * ρ) =
            Matrix.trace (Λ j * ρ * (Λ j)ᴴ) := by
          calc
            Matrix.trace (Λ j * ρ) = Matrix.trace ((Λ j * Λ j) * ρ) := by rw [hidem]
            _ = Matrix.trace (Λ j * (Λ j * ρ)) := by rw [Matrix.mul_assoc]
            _ = Matrix.trace ((Λ j * ρ) * Λ j) := Matrix.trace_mul_comm _ _
            _ = Matrix.trace (Λ j * ρ * (Λ j)ᴴ) := by rw [hstar]
        rw [htrace]
        have hM := hρ.1.mul_mul_conjTranspose_same (Λ j)
        have hdiag (k : Fin D) : 0 ≤ ((Λ j * ρ * (Λ j)ᴴ) k k).re := by
          have hk := hM.dotProduct_mulVec_nonneg (Pi.single k 1)
          have hkRe := (Complex.nonneg_iff.mp hk).1
          simpa using hkRe
        simp only [Matrix.trace, Complex.re_sum]
        exact Finset.sum_nonneg fun k _ => hdiag k
      have hsum : 1 - ε ≤ ∑ j, (Matrix.trace (Λ j * ρ)).re :=
        hi₀.trans (Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i₀))
      have hnReal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
      have hdiv : (1 - ε) / (n : ℝ) ≤ δ := by
        calc
          (1 - ε) / (n : ℝ) ≤ (∑ j, (Matrix.trace (Λ j * ρ)).re) / (n : ℝ) :=
            div_le_div_of_nonneg_right hsum hnReal.le
          _ = (1 / n : ℝ) * ∑ j, (Matrix.trace (Λ j * ρ)).re := by ring
          _ ≤ δ := havg
      have hbound : 1 - ε ≤ δ * (n : ℝ) := (div_le_iff₀ hnReal).mp hdiv
      have hδn : 0 ≤ δ * (n : ℝ) := mul_nonneg hδ hnReal.le
      nlinarith
    · simp only [test, htest, ↓reduceIte]
      positivity

end Qatlib.Papers.SeqMeasure16.MainResults.OrBound
