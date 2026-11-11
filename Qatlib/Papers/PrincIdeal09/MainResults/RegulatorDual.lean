/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PrincIdeal09.MainResults.Framework
import Qatlib.Papers.PrincIdeal09.MainResults.Periodicity
import Qatlib.Papers.PrincIdeal09.MainResults.NumericBounds
import Qatlib.Papers.PrincIdeal09.MainResults.Amplitude

/-!
# Regulator dual sampling and reconstruction bounds

The record `RegulatorDualModel` collects sampling, counting, approximation, and register-size
hypotheses. These imply a bounded-error dual sample and explicit success and resource bounds;
separate ratio estimates give the accuracy used for continued-fraction reconstruction, and
`RegulatorModel` packages the final success expression [Schmidt2009].

## Main statements

* `theorem1_regulator_dual`: Combines the sample relation, success lower bound, and resource
  upper bound.
* `lemma3_continued_fraction_regime`: The sample ratio approximates the integer ratio within 1 /
  (2z₂²).
* `theorem2_regulator`: The final model has success at least 2⁻²⁶ and the inherited resource
  bound.

## References

* [Schmidt, 2009][Schmidt2009]
-/

set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Classical

namespace Qatlib.Papers.PrincIdeal09.MainResults

/-- A record of regulator dual-sampling parameters with size, sample-error, counting, success,
and register-size hypotheses. -/
structure RegulatorDualModel where

  Δ : ℝ
  Δ_gt_one : 1 < Δ

  R : ℝ
  R_pos : 0 < R

  reg_large : 32 * Real.log Δ ≤ R

  q : ℝ
  q_pos : 0 < q
  q_pow_two : ∃ t : ℕ, q = (2 : ℝ) ^ t
  q_lower : q / 2 ≤ 5 * Δ * (Real.log Δ) ^ 2
  q_upper : 5 * Δ * (Real.log Δ) ^ 2 < q

  y : ℝ
  z : ℤ

  ω : ℝ
  y_eq : y = (q / R) * (z : ℝ) + ω
  ω_bound : |ω| ≤ 1 / 2

  mmin : ℕ
  mmax : ℕ
  mmin_ge_one : 1 ≤ mmin
  mrange : mmax ≤ mmin + 4

  p : ℕ
  p_lower : (q / (8 * R)) * ((mmin : ℝ) + 1) ≤ (p : ℝ)

  cardY : ℕ
  cardY_lower : R / (8 * ((mmax : ℝ) + 1)) ≤ (cardY : ℝ)

  perY : ℝ
  perY_lower : (p : ℝ) / (8 * q) ≤ perY

  successProb : ℝ
  successProb_eq : successProb = (cardY : ℝ) * perY

  a : ℝ
  b : ℝ
  a_pos : 0 < a
  b_pos : 0 < b
  a_le_sqrt : a ≤ Real.sqrt Δ
  b_le_sqrt : b ≤ Real.sqrt Δ

  qbits : ℝ
  formBits : ℝ
  N : ℝ
  qbits_eq : qbits = Real.logb 2 q
  formBits_eq : formBits = Real.logb 2 a + Real.logb 2 b + 2
  qubits : ℝ
  qubits_eq : qubits = qbits + formBits + N

namespace RegulatorDualModel

/-- The dual model's register parameter satisfies `q ≤ 10 * Δ * (log Δ)²`. -/
theorem q_le_ten (M : RegulatorDualModel) :
    M.q ≤ 10 * M.Δ * (Real.log M.Δ) ^ 2 := by
  have h1 := M.q_lower
  have h2 := M.q_upper
  linarith

/-- The regulator dual model has success value at least `2^(-11)` [Schmidt2009]. -/
theorem success_ge (M : RegulatorDualModel) :
    (2 : ℝ) ^ (-11 : ℤ) ≤ M.successProb := by
  have hR : 0 < M.R := M.R_pos
  have hq : 0 < M.q := M.q_pos
  have hA : (0 : ℝ) ≤ (M.mmin : ℝ) + 1 := by positivity
  have hB : (0 : ℝ) < (M.mmax : ℝ) + 1 := by positivity

  have hstep1 :
      (M.R / (8 * ((M.mmax : ℝ) + 1))) * ((M.p : ℝ) / (8 * M.q)) ≤ M.successProb := by
    rw [M.successProb_eq]
    refine mul_le_mul M.cardY_lower M.perY_lower ?_ ?_
    · exact by positivity
    · exact_mod_cast Nat.zero_le M.cardY

  have hcore :
      ((M.mmin : ℝ) + 1) / (2 ^ 9 * ((M.mmax : ℝ) + 1)) ≤
        (M.R / (8 * ((M.mmax : ℝ) + 1))) * ((M.p : ℝ) / (8 * M.q)) := by
    have hk_nonneg : (0 : ℝ) ≤
        (M.R / (8 * ((M.mmax : ℝ) + 1))) * (1 / (8 * M.q)) := by positivity
    have hprod := mul_le_mul_of_nonneg_left M.p_lower hk_nonneg
    have hleft :
        (M.R / (8 * ((M.mmax : ℝ) + 1))) * (1 / (8 * M.q)) *
            ((M.q / (8 * M.R)) * ((M.mmin : ℝ) + 1)) =
          ((M.mmin : ℝ) + 1) / (2 ^ 9 * ((M.mmax : ℝ) + 1)) := by
      field_simp
      ring
    have hright :
        (M.R / (8 * ((M.mmax : ℝ) + 1))) * (1 / (8 * M.q)) * (M.p : ℝ) =
          (M.R / (8 * ((M.mmax : ℝ) + 1))) * ((M.p : ℝ) / (8 * M.q)) := by
      field_simp
    rw [← hleft, ← hright]
    exact hprod
  exact le_trans (dual_count_bound M.mmin_ge_one M.mrange) (le_trans hcore hstep1)

end RegulatorDualModel

/-- A regulator dual model possesses the stated integer sample relation with error at most one
half, success value at least `2^(-11)`, and the logarithmic resource bound [Schmidt2009]. -/
theorem theorem1_regulator_dual (M : RegulatorDualModel) :
    (∃ z : ℤ, ∃ ω : ℝ, |ω| ≤ 1 / 2 ∧ M.y = (M.q / M.R) * (z : ℝ) + ω) ∧
      (2 : ℝ) ^ (-11 : ℤ) ≤ M.successProb ∧
      M.qubits ≤ 2 * Real.logb 2 M.Δ + 2 * Real.logb 2 (Real.log M.Δ) + M.N + 7 := by
  refine ⟨⟨M.z, M.ω, M.ω_bound, M.y_eq⟩, M.success_ge, ?_⟩
  have hΔpos : (0 : ℝ) < M.Δ := by linarith [M.Δ_gt_one]
  have hqb : M.qbits ≤ Real.logb 2 M.Δ + 2 * Real.logb 2 (Real.log M.Δ) + 5 := by
    rw [M.qbits_eq]
    exact first_register_bits_bound M.Δ_gt_one M.q_pos M.q_le_ten
  have hfb : M.formBits ≤ Real.logb 2 M.Δ + 2 := by
    rw [M.formBits_eq]
    exact form_register_bits_bound hΔpos M.a_pos M.b_pos M.a_le_sqrt M.b_le_sqrt
  rw [M.qubits_eq]
  linarith

/-- The resource value of a regulator dual model is at most `2 * logb 2 Δ + 2 * logb 2 (log Δ) +
N + 7` [Schmidt2009]. -/
theorem theorem1_qubit_clause (M : RegulatorDualModel) :
    M.qubits ≤ 2 * Real.logb 2 M.Δ + 2 * Real.logb 2 (Real.log M.Δ) + M.N + 7 :=
  theorem1_regulator_dual M |>.2.2

/-- Under the stated sample and positivity bounds, the ratio error `|y1 / y2 - z1 / z2|` is at
most `R / (q * z2 - R / 2)` [Schmidt2009]. -/
theorem lemma3_intermediate
    (q R y1 y2 z1 z2 ω1 ω2 : ℝ)
    (hR : 0 < R) (hq : R ^ 2 < q)
    (hy2 : y2 ≠ 0) (hy2_pos : 0 < y2) (hzden : 0 < q * z2 - R / 2)
    (hz1_0 : 0 ≤ z1) (hz1_z2 : z1 ≤ z2) (hz2_1 : 1 ≤ z2)
    (hω1 : |ω1| ≤ 1 / 2) (hω2 : |ω2| ≤ 1 / 2)
    (hy1 : y1 = (q / R) * z1 + ω1) (hy2eq : y2 = (q / R) * z2 + ω2) :
    |y1 / y2 - z1 / z2| ≤ R / (q * z2 - R / 2) := by
  have hz2pos : 0 < z2 := by linarith
  have hkey : y1 / y2 - z1 / z2 = (ω1 * z2 - z1 * ω2) / (y2 * z2) := by
    have hkey0 : y1 / y2 - z1 / z2 = (y1 * z2 - z1 * y2) / (y2 * z2) := by
      rw [div_sub_div _ _ hy2 (ne_of_gt hz2pos)]
      ring
    have hnum_eq : y1 * z2 - z1 * y2 = ω1 * z2 - z1 * ω2 := by
      rw [hy1, hy2eq]; ring
    rw [hkey0, hnum_eq]
  have hnum : |ω1 * z2 - z1 * ω2| ≤ (z1 + z2) / 2 := by
    have h1 : |ω1 * z2| ≤ (1 / 2) * z2 := by
      rw [abs_mul, abs_of_pos hz2pos]
      nlinarith [hω1, hz2pos]
    have h2 : |z1 * ω2| ≤ z1 * (1 / 2) := by
      rw [abs_mul, abs_of_nonneg hz1_0]
      nlinarith [hω2, hz1_0]
    calc |ω1 * z2 - z1 * ω2| ≤ |ω1 * z2| + |z1 * ω2| := abs_sub _ _
      _ ≤ (1 / 2) * z2 + z1 * (1 / 2) := by linarith
      _ = (z1 + z2) / 2 := by ring
  have hnum2 : |ω1 * z2 - z1 * ω2| ≤ z2 := by
    have : (z1 + z2) / 2 ≤ z2 := by linarith
    linarith [hnum, this]
  have hden : 0 < y2 * z2 := mul_pos hy2_pos hz2pos
  have hstep1 : |ω1 * z2 - z1 * ω2| / (y2 * z2) ≤ 1 / y2 := by
    rw [div_le_iff₀ hden]
    have hrhs : (1 / y2) * (y2 * z2) = z2 := by field_simp [hy2]
    rw [hrhs]
    exact hnum2
  have hstep2 : 1 / y2 ≤ R / (q * z2 - R / 2) := by
    rw [div_le_div_iff₀ hy2_pos hzden]
    have hRy : R * y2 = q * z2 + R * ω2 := by
      rw [hy2eq]; field_simp
    have hω : -(1 / 2 : ℝ) ≤ ω2 := (abs_le.mp hω2).1
    have hRω : -(R / 2) ≤ R * ω2 := by
      have := mul_le_mul_of_nonneg_left hω (le_of_lt hR)
      linarith
    linarith [hRy, hRω]
  rw [hkey, abs_div, abs_of_pos hden]
  exact le_trans hstep1 hstep2

/-- Under the stated sample bounds, including `z2 ≤ R / 4` and `R² < q`, the ratio error is at
most `1 / (2 * z2²)` [Schmidt2009]. -/
theorem lemma3_continued_fraction_regime
    (q R y1 y2 z1 z2 ω1 ω2 : ℝ)
    (hR : 0 < R) (hq : R ^ 2 < q)
    (hy2 : y2 ≠ 0)
    (hz1_0 : 0 ≤ z1) (hz1_z2 : z1 ≤ z2) (hz2_1 : 1 ≤ z2) (hz2_le : z2 ≤ R / 4)
    (hω1 : |ω1| ≤ 1 / 2) (hω2 : |ω2| ≤ 1 / 2)
    (hy1 : y1 = (q / R) * z1 + ω1) (hy2eq : y2 = (q / R) * z2 + ω2) :
    |y1 / y2 - z1 / z2| ≤ 1 / (2 * z2 ^ 2) := by
  have hz2pos : 0 < z2 := by linarith
  have hz2sq : 0 < 2 * z2 ^ 2 := by positivity
  have hz2sq1 : 1 ≤ z2 ^ 2 := by nlinarith [hz2_1]
  have hkey : y1 / y2 - z1 / z2 = (ω1 * z2 - z1 * ω2) / (y2 * z2) := by
    have hkey0 : y1 / y2 - z1 / z2 = (y1 * z2 - z1 * y2) / (y2 * z2) := by
      rw [div_sub_div _ _ hy2 (ne_of_gt hz2pos)]
      ring
    have hnum_eq : y1 * z2 - z1 * y2 = ω1 * z2 - z1 * ω2 := by
      rw [hy1, hy2eq]; ring
    rw [hkey0, hnum_eq]
  have hRv : R * z2 ≤ (q / R) * z2 := by
    have hlt : R < q / R := by
      rw [lt_div_iff₀ hR]
      nlinarith [hq]
    nlinarith [hlt, hz2pos]
  have hy2_low : 2 * z2 ^ 2 ≤ y2 := by
    have hgap : 4 * z2 ^ 2 ≤ R * z2 := by nlinarith [hz2_le, hz2pos, hR]
    have hω : -(1 / 2 : ℝ) ≤ ω2 := (abs_le.mp hω2).1
    rw [hy2eq]
    nlinarith [hRv, hgap, hω, hz2sq1]
  have hy2_pos : 0 < y2 := lt_of_lt_of_le (by positivity) hy2_low
  have hnum : |ω1 * z2 - z1 * ω2| ≤ z2 := by
    have h1 : |ω1 * z2| ≤ (1 / 2) * z2 := by
      rw [abs_mul, abs_of_pos hz2pos]
      nlinarith [hω1, hz2pos]
    have h2 : |z1 * ω2| ≤ z2 * (1 / 2) := by
      rw [abs_mul, abs_of_nonneg hz1_0]
      nlinarith [hω2, hz1_z2, hz2pos]
    calc |ω1 * z2 - z1 * ω2| ≤ |ω1 * z2| + |z1 * ω2| := abs_sub _ _
      _ ≤ (1 / 2) * z2 + z2 * (1 / 2) := by linarith
      _ = z2 := by ring
  have hden : 0 < y2 * z2 := mul_pos hy2_pos hz2pos
  have hstep : |ω1 * z2 - z1 * ω2| / (y2 * z2) ≤ 1 / y2 := by
    rw [div_le_iff₀ hden]
    have hrhs : (1 / y2) * (y2 * z2) = z2 := by field_simp [hy2]
    rw [hrhs]
    exact hnum
  have hstep2 : 1 / y2 ≤ 1 / (2 * z2 ^ 2) := one_div_le_one_div_of_le hz2sq hy2_low
  rw [hkey, abs_div, abs_of_pos hden]
  exact le_trans hstep hstep2

/-- A regulator dual model together with a success value equal to `(6 / π²) * 2^(-25)`. -/
structure RegulatorModel where
  dual : RegulatorDualModel
  successProb : ℝ
  prob_eq : successProb = (6 / Real.pi ^ 2) * (2 : ℝ) ^ (-25 : ℤ)

/-- A regulator model has success value at least `2^(-26)` and inherits the stated logarithmic
resource bound from its dual model [Schmidt2009]. -/
theorem theorem2_regulator (M : RegulatorModel) :
    (2 : ℝ) ^ (-26 : ℤ) ≤ M.successProb ∧
      M.dual.qubits ≤
        2 * Real.logb 2 M.dual.Δ + 2 * Real.logb 2 (Real.log M.dual.Δ) + M.dual.N + 7 := by
  refine ⟨?_, ?_⟩
  · rw [M.prob_eq]
    exact thm2_prob_bound
  · exact theorem1_qubit_clause M.dual

end Qatlib.Papers.PrincIdeal09.MainResults
