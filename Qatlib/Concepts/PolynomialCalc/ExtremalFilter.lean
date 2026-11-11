/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PolynomialCalc.ChebyshevScale

/-!
# Admissibility and band edge of Chebyshev filters

This module verifies the scaled Chebyshev candidate from `ChebyshevScale.filterPolynomial`. It
identifies the supremal point where the candidate takes the value `ε`, and proves its
admissibility and exact degree under the stated parameter restrictions. The construction is
related to the Chebyshev filters in [YoderLowChuang2014].

## Main statements

* `candidate_band_edge`: the upper level-set edge is `1 - bandWidth ε k`.
* `candidate_membership`: the candidate is admissible and has degree exactly `k`.

## References

* [Yoder et al., 2014][YoderLowChuang2014]
-/

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Concepts.PolynomialCalc.ExtremalFilter
open Qatlib.Concepts.PolynomialCalc.ChebyshevScale

/-- The hyperbolic scaling point used by the Chebyshev filter is at least one. -/
lemma cheb_band_const_one_le (ε : ℝ) (k : ℕ) :
    1 ≤ hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) := by
  have hc : Real.cosh (((k : ℝ))⁻¹ * Real.arcosh (1 / ε))
      = hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) := rfl
  rw [← hc]
  exact Real.one_le_cosh _

/-- One minus the filter bandwidth equals the reciprocal of its hyperbolic scaling point. -/
lemma one_sub_delta_eq (ε : ℝ) (k : ℕ) :
    1 - bandWidth ε k = (hyperbolicScale ((k : ℝ))⁻¹ (1 / ε))⁻¹ := by
  have hc0 : 0 < hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) :=
    lt_of_lt_of_le zero_lt_one (cheb_band_const_one_le ε k)
  rw [bandWidth, div_eq_inv_mul, mul_sub, inv_mul_cancel₀ (ne_of_gt hc0), mul_one]
  ring

/-- For `ε > 0` and positive degree, the supremum of points in `[-1, 1]` where the filter equals
`ε` is `1 - bandWidth ε k`. -/
theorem candidate_band_edge
    (ε : ℝ) (k : ℕ) (hε0 : 0 < ε) (hk : 1 ≤ k) :
    sSup {x : ℝ | |x| ≤ 1 ∧ filterValue ε k x = ε} = 1 - bandWidth ε k := by
  have hc1 : 1 ≤ hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) := cheb_band_const_one_le ε k
  have hc0 : 0 < hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) := lt_of_lt_of_le zero_lt_one hc1
  have hkne : (k : ℕ) ≠ 0 := by omega
  have hT1 : (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval 1 = 1 := by
    simp
  have hup : ∀ t : ℝ, filterValue ε k t = ε * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval
      (hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) * t) := chebPoly_eval ε k
  have hmem : (1 : ℝ) - bandWidth ε k ∈ {x : ℝ | |x| ≤ 1 ∧ filterValue ε k x = ε} := by
    refine ⟨?_, ?_⟩
    · rw [one_sub_delta_eq ε k, abs_of_pos (inv_pos.2 hc0)]
      exact (inv_le_one₀ hc0).mpr hc1
    · rw [hup, one_sub_delta_eq ε k,
        mul_inv_cancel₀ (ne_of_gt hc0), hT1, mul_one]
  set S : Set ℝ := {x : ℝ | |x| ≤ 1 ∧ filterValue ε k x = ε} with hS
  have hSne : S.Nonempty := ⟨1 - bandWidth ε k, hmem⟩
  have hSbd : BddAbove S := ⟨1, by rintro x ⟨hx, -⟩; exact (abs_le.mp hx).2⟩
  have hkey : ∀ x ∈ S, x ≤ 1 - bandWidth ε k := by
    rintro x ⟨-, hxv⟩
    rw [hup] at hxv
    have hT : (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval
        (hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) * x) = 1 := by
      have h' : ε * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval
          (hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) * x) = ε * 1 := by rw [hxv, mul_one]
      exact mul_left_cancel₀ (ne_of_gt hε0) h'
    obtain ⟨m, -, -, hy⟩ :=
      (Polynomial.Chebyshev.eval_T_real_eq_one_iff hkne _).mp hT
    have hcos : Real.cos (m * Real.pi / k) ≤ 1 := Real.cos_le_one _
    have hcxe : hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) * x ≤ 1 := by rw [hy]; exact hcos
    rw [one_sub_delta_eq ε k, inv_eq_one_div]
    exact (le_div_iff₀ hc0).mpr (mul_comm (hyperbolicScale ((k : ℝ))⁻¹ (1 / ε)) x ▸ hcxe)
  rw [le_antisymm (csSup_le hSne hkey) (le_csSup hSbd hmem)]

/-- For `0 < ε < 1` and positive `k`, the scaled Chebyshev candidate satisfies
`AdmissibleFilter` and has natural degree exactly `k`. -/
theorem candidate_membership
    (ε : ℝ) (k : ℕ) (hε0 : 0 < ε) (hε1 : ε < 1) (hk : 1 ≤ k) :
    AdmissibleFilter ε k (filterPolynomial ε k) ∧ (filterPolynomial ε k).natDegree = k := by
  have hc1 : 1 ≤ hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) := cheb_band_const_one_le ε k
  have hc0 : 0 < hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) := lt_of_lt_of_le zero_lt_one hc1
  have hTc : (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval
      (hyperbolicScale ((k : ℝ))⁻¹ (1 / ε)) = 1 / ε := eval_T_band_const ε k (by omega) hε0 hε1.le

  have hCXdeg : (Polynomial.C (hyperbolicScale ((k : ℝ))⁻¹ (1 / ε)) * Polynomial.X).natDegree = 1 := by
    rw [Polynomial.natDegree_mul (by simpa using ne_of_gt hc0) (by simp),
      Polynomial.natDegree_C, Polynomial.natDegree_X, zero_add]
  have hCXne : Polynomial.C (hyperbolicScale ((k : ℝ))⁻¹ (1 / ε)) * Polynomial.X ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hCXdeg
    omega
  have hTdeg : (Polynomial.Chebyshev.T ℝ (k : ℤ)).natDegree = k := by
    rw [Polynomial.Chebyshev.natDegree_T ℝ (k : ℤ), Int.natAbs_natCast]
  have hTne : (Polynomial.Chebyshev.T ℝ (k : ℤ)) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hTdeg
    omega
  have hcompdeg : ((Polynomial.Chebyshev.T ℝ (k : ℤ)).comp
      (Polynomial.C (hyperbolicScale ((k : ℝ))⁻¹ (1 / ε)) * Polynomial.X)).natDegree = k := by
    rw [Polynomial.natDegree_comp, hTdeg, hCXdeg, mul_one]
  have hcompne : ((Polynomial.Chebyshev.T ℝ (k : ℤ)).comp
      (Polynomial.C (hyperbolicScale ((k : ℝ))⁻¹ (1 / ε)) * Polynomial.X)) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hcompdeg
    omega
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · have hnp : ∀ x : ℝ, (filterPolynomial ε k).eval x
        = ε * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval
            (hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) * x) := chebPoly_eval ε k
    by_cases hke : Even k
    · refine Or.inl ?_
      intro x
      rw [hnp, hnp, ← neg_mul_eq_mul_neg,
        Polynomial.Chebyshev.T_eval_neg ℝ (k : ℤ)
          (hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) * x),
        Int.cast_negOnePow_natCast,
        Iff.mpr (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℝ) ≠ 1)) hke,
        one_mul]
    · refine Or.inr ?_
      intro x
      have hko : Odd k := by
        rcases Nat.even_or_odd k with h | h
        · exact absurd h hke
        · exact h
      rw [hnp, hnp, ← neg_mul_eq_mul_neg,
        Polynomial.Chebyshev.T_eval_neg ℝ (k : ℤ)
          (hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) * x),
        Int.cast_negOnePow_natCast,
        Iff.mpr (neg_one_pow_eq_neg_one_iff_odd (by norm_num : (-1 : ℝ) ≠ 1)) hko]
      ring
  · intro x hxr
    rw [Polynomial.IsRoot.def, chebPoly_eval] at hxr
    have h0 : (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval
        (hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) * x) = 0 := by
      rcases mul_eq_zero.mp hxr with h | h
      · exact absurd h (ne_of_gt hε0)
      · exact h
    have habs : |hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) * x| < 1 := by
      by_contra hcon
      push Not at hcon
      rcases le_or_gt x 0 with hx0 | hx0
      · have hnx : hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) * x ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hc0.le hx0
        rw [abs_of_nonpos hnx] at hcon
        have hcxle : hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) * x ≤ -1 := by linarith
        have h1 := Polynomial.Chebyshev.one_le_negOnePow_mul_eval_T_real
          (k : ℤ) hcxle
        rw [h0] at h1
        linarith
      · have hnn : 0 ≤ hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) * x := mul_nonneg hc0.le hx0.le
        rw [abs_of_nonneg hnn] at hcon
        have h1 := Polynomial.Chebyshev.one_le_eval_T_real (k : ℤ) hcon
        rw [h0] at h1
        linarith
    rw [abs_lt] at habs
    refine ⟨?_, ?_⟩
    · by_contra hcon
      push Not at hcon
      have hstep : hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) * x
          ≤ hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) * (-1 : ℝ) :=
        mul_le_mul_of_nonneg_left hcon hc0.le
      rw [mul_neg, mul_one] at hstep
      linarith [hstep, habs.1, hc1]
    · by_contra hcon
      push Not at hcon
      have hstep : hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) * (1 : ℝ)
          ≤ hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) * x :=
        mul_le_mul_of_nonneg_left hcon hc0.le
      rw [mul_one] at hstep
      linarith [hstep, habs.2, hc1]
  · rw [chebPoly_eval, mul_one, hTc]
    field_simp
  · intro x hx1 hx2
    have hlow : hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) * x ≥ -1 := by
      have hx1' : -(1 - bandWidth ε k) ≤ x := by linarith
      rw [one_sub_delta_eq ε k] at hx1'
      have hstep : hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) * (-(hyperbolicScale ((k : ℝ))⁻¹ (1 / ε))⁻¹)
          ≤ hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) * x :=
        mul_le_mul_of_nonneg_left hx1' hc0.le
      rw [mul_neg, mul_inv_cancel₀ (ne_of_gt hc0)] at hstep
      linarith
    have hhigh : hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) * x ≤ 1 := by
      rw [one_sub_delta_eq ε k] at hx2
      have hstep : hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) * x
          ≤ hyperbolicScale ((k : ℝ))⁻¹ (1 / ε) * (hyperbolicScale ((k : ℝ))⁻¹ (1 / ε))⁻¹ :=
        mul_le_mul_of_nonneg_left hx2 hc0.le
      rwa [mul_inv_cancel₀ (ne_of_gt hc0)] at hstep
    rw [chebPoly_eval, abs_mul, abs_of_pos hε0]
    simpa using mul_le_mul_of_nonneg_left
      (Polynomial.Chebyshev.abs_eval_T_real_le_one (k : ℤ)
        (abs_le.mpr ⟨hlow, hhigh⟩)) hε0.le
  · rw [filterPolynomial, Polynomial.natDegree_mul (by simpa using ne_of_gt hε0) hcompne,
      Polynomial.natDegree_C, hcompdeg, zero_add]

end Qatlib.Concepts.PolynomialCalc.ExtremalFilter
