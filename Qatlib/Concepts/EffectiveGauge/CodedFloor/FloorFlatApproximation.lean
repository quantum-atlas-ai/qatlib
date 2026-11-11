/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.CutoffPolynomial
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.NegativeExpProgram

/-!
# Floor Flat Approximation

Coded Floor constructions for Effective Gauge.
Defines `floorFlatPolynomialValue`, `floorFlatApproximation`.
Proves `floorFlatPolynomialValue_cast`, `floorFlatApproximation_error`.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.CodedFloor
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Definition of floor Flat Polynomial Value in the Coded Floor construction. -/
def floorFlatPolynomialValue (n : ℕ) (x : ℚ) : ℚ :=
  ∑ m ∈ Finset.range (2*n+1), (cutoffCoefficientAt (cutoffCoefficientRow n) m : ℚ)*x^m

/-- The rational argument is tested exactly. No approximate branch decision at the flat boundary. -/
def floorFlatApproximation (n : ℕ) (p tolerance : ℚ) : ℚ :=
  if p ≤ 0 then 0 else
    let c := floorFlatPolynomialValue n p⁻¹
    c*(rationalNegativeExp p⁻¹ (tolerance/(|c|+1))).value

noncomputable section

/-- Original `floorFlatPolynomialValue_cast` guarantee for the `FloorFlatApproximation` construction; the complete source hypotheses are retained. -/
theorem floorFlatPolynomialValue_cast (n : ℕ) (x : ℚ) :
    (floorFlatPolynomialValue n x : ℝ)=(cutoffRealPolynomial n).eval (x : ℝ) := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (cutoffRealPolynomial_degree n))]
  simp [floorFlatPolynomialValue,cutoffRealPolynomial_coeff,cutoffCoefficientAt_eq]

/-- Original `floorFlatApproximation_error` guarantee for the `FloorFlatApproximation` construction; the complete source hypotheses are retained. -/
theorem floorFlatApproximation_error (n : ℕ) (p tolerance : ℚ) (ht : 0<tolerance) :
    |(floorFlatApproximation n p tolerance : ℝ)-iteratedDeriv n expNegInvGlue (p : ℝ)| ≤
      (tolerance : ℝ) := by
  have htR : (0 : ℝ)<tolerance := Rat.cast_pos.mpr ht
  rw [congrFun (iteratedDeriv_expNegInvGlue n) (p : ℝ)]
  by_cases hp : p ≤ 0
  · have hpR : (p : ℝ) ≤ 0 := Rat.cast_nonpos.mpr hp
    simp only [floorFlatApproximation,if_pos hp,Rat.cast_zero,expNegInvGlue.zero_of_nonpos hpR,
      mul_zero,sub_self,abs_zero]
    exact htR.le
  · let c := floorFlatPolynomialValue n p⁻¹
    have hp0 : 0<p := lt_of_not_ge hp
    have hpR : ¬(p : ℝ) ≤ 0 := not_le.mpr (Rat.cast_pos.mpr hp0)
    have htol : 0<tolerance/(|c|+1) := div_pos ht (by positivity)
    have hr := rationalNegativeExp_spec p⁻¹ (tolerance/(|c|+1)) (by positivity) htol
    have he := hr.1.trans (by exact_mod_cast hr.2.2.2.2.1 :
      ((rationalNegativeExp p⁻¹ (tolerance/(|c|+1))).error : ℝ) ≤ (tolerance/(|c|+1) : ℚ))
    have hc : (c : ℝ)=(cutoffRealPolynomial n).eval (p : ℝ)⁻¹ := by
      simpa only [c,Rat.cast_inv] using floorFlatPolynomialValue_cast n p⁻¹
    rw [floorFlatApproximation,if_neg hp]
    change |((c*(rationalNegativeExp p⁻¹ (tolerance/(|c|+1))).value : ℚ) : ℝ)-
      (cutoffRealPolynomial n).eval (p : ℝ)⁻¹*expNegInvGlue (p : ℝ)| ≤ _
    rw [← hc]
    simp only [Rat.cast_mul,expNegInvGlue,if_neg hpR]
    rw [← mul_sub,abs_mul]
    have heR : |((rationalNegativeExp p⁻¹ (tolerance/(|c|+1))).value : ℝ)-
        Real.exp (-(p : ℝ)⁻¹)| ≤ (tolerance : ℝ)/(|(c : ℝ)|+1) := by
      simpa only [Rat.cast_inv,Rat.cast_div,Rat.cast_add,Rat.cast_abs,Rat.cast_one] using he
    calc
      _ ≤ |(c : ℝ)| * ((tolerance : ℝ)/(|(c : ℝ)|+1)) :=
        mul_le_mul_of_nonneg_left heR (abs_nonneg _)
      _ ≤ (tolerance : ℝ) := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < |(c : ℝ)|+1)).mpr
        nlinarith [abs_nonneg (c : ℝ)]

end
end Qatlib.Concepts.EffectiveGauge.CodedFloor
