/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ProjectorQAOA26.StageStability.OpNormBridge

/-!
# Operator norm of rank-one differences

This module defines `rankOne` and computes the exact operator norm of its difference for
normalized complex vectors. Bessel's inequality and overlap estimates establish the comparison
with `phaseDist` needed for learned complementary-projector stability in [ZhouAnLiu2026].

## Main statements

* `bessel_two`: For two orthogonal normalized vectors, the sum of the squared overlap magnitudes
  with any vector is at most that vector's squared norm.
* `opNorm_rankOne_sub`: For normalized vectors, the operator norm of their rank-one difference
  is the square root of one minus the squared overlap magnitude.
* `mixerGen_diff_le`: The norm distance between the complementary projectors of normalized
  vectors is at most their phase distance.

## References

* [Zhou et al., 2026][ZhouAnLiu2026]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.ProjectorQAOA26.StageStability

open scoped BigOperators Matrix Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The outer-product matrix with entries `u i * star (u j)`. -/
noncomputable def rankOne (u : I → ℂ) : Matrix I I ℂ := Matrix.vecMulVec u (star u)

omit [DecidableEq I] in

/-- The rank-one operator sends `x` to `l2inner u x • u`. -/
theorem rankOne_mulVec (u x : I → ℂ) : rankOne u *ᵥ x = l2inner u x • u := by
  funext i
  show (∑ j, u i * star (u j) * x j) = l2inner u x * u i
  rw [l2inner, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

omit [Fintype I] [DecidableEq I] in

/-- Multiplication of the defining vector by a unit phase leaves its rank-one operator
unchanged. -/
theorem rankOne_smul_unit {z : ℂ} (hz : Complex.normSq z = 1) (v : I → ℂ) :
    rankOne (z • v) = rankOne v := by
  funext i j
  simp only [rankOne, Matrix.vecMulVec_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_mul]
  have h1 : z * star z = 1 := by
    rw [mul_comm, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, hz, Complex.ofReal_one]
  calc z * v i * (star (v j) * star z) = (z * star z) * (v i * star (v j)) := by ring
    _ = 1 * (v i * star (v j)) := by rw [h1]
    _ = v i * star (v j) := one_mul _

omit [DecidableEq I] in

/-- A normalized vector has inner product one with itself. -/
theorem l2inner_self_of_norm {u : I → ℂ} (hu : l2norm u = 1) : l2inner u u = 1 := by
  have hc : ∀ i : I, star (u i) * u i = (Complex.normSq (u i) : ℂ) := by
    intro i
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  have hsum : ∑ i, Complex.normSq (u i) = 1 := by
    rw [← l2norm_sq, hu]
    simp
  rw [l2inner, Finset.sum_congr rfl (fun i _ => hc i), ← Complex.ofReal_sum, hsum,
    Complex.ofReal_one]

/-- The real part of a real scalar times a complex number is the scalar times the real part. -/
private theorem re_ofReal_mul (x : ℝ) (z : ℂ) : (((x : ℂ)) * z).re = x * z.re := by
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Complex conjugation fixes a real number embedded in the complex numbers. -/
private theorem star_ofReal' (t : ℝ) : star ((t : ℂ)) = (t : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal]

/-- The real part of `star a * a` equals the squared complex norm of `a`. -/
private theorem re_conj_mul_self (a : ℂ) : (star a * a).re = Complex.normSq a := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

omit [DecidableEq I] in

/-- The overlap magnitude of two normalized vectors is at most one. -/
theorem l2abs_le_one {u v : I → ℂ} (hu : l2norm u = 1) (hv : l2norm v = 1) :
    l2abs u v ≤ 1 := by
  have h := phaseDist_sq u v
  rw [hu, hv] at h
  have hnn := phaseDist_nonneg u v
  nlinarith

omit [DecidableEq I] in

/-- Negating a vector preserves its Euclidean norm. -/
theorem l2norm_neg (x : I → ℂ) : l2norm (-x) = l2norm x := by
  refine eq_of_sq_eq (l2norm_nonneg _) (l2norm_nonneg _) ?_
  rw [l2norm_sq, l2norm_sq]
  simp only [Pi.neg_apply, Complex.normSq_neg]

omit [DecidableEq I] in

/-- The squared norm of a vector sum is the sum of squared norms plus twice the real part of the
inner product. -/
theorem l2norm_add_sq (x y : I → ℂ) :
    l2norm (x + y) ^ 2 = l2norm x ^ 2 + l2norm y ^ 2 + 2 * (l2inner x y).re := by
  have h := l2norm_sub_sq x (-(y : I → ℂ))
  simp only [sub_neg_eq_add, l2inner_neg_right, Complex.neg_re, l2norm_neg] at h
  linarith

omit [DecidableEq I] in

/-- For two orthogonal normalized vectors, the sum of the squared overlap magnitudes with any
vector is at most that vector's squared norm. -/
theorem bessel_two {u w x : I → ℂ} (hu : l2norm u = 1) (hw : l2norm w = 1)
    (hperp : l2inner u w = 0) :
    Complex.normSq (l2inner u x) + Complex.normSq (l2inner w x) ≤ l2norm x ^ 2 := by
  set a := l2inner u x with ha
  set β := l2inner w x with hb
  have h1 : l2norm (a • u) ^ 2 = Complex.normSq a := by
    rw [l2norm_smul, hu, mul_one, Real.sq_sqrt (Complex.normSq_nonneg a)]
  have h2 : l2norm (β • w) ^ 2 = Complex.normSq β := by
    rw [l2norm_smul, hw, mul_one, Real.sq_sqrt (Complex.normSq_nonneg β)]
  have hcross : l2inner (a • u) (β • w) = 0 := by
    rw [l2inner_smul_left, l2inner_smul_right, hperp]
    ring
  have hyn : l2norm (a • u + β • w) ^ 2 = Complex.normSq a + Complex.normSq β := by
    rw [l2norm_add_sq, h1, h2, hcross, Complex.zero_re, mul_zero, add_zero]
  have hxy : l2inner x (a • u + β • w) = (Complex.normSq a + Complex.normSq β : ℂ) := by
    rw [l2inner_add_right, l2inner_smul_right, l2inner_smul_right, l2inner_symm u x,
      l2inner_symm w x, ← ha, ← hb]
    have e1 : a * star a = (Complex.normSq a : ℂ) := by
      rw [mul_comm, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    have e2 : β * star β = (Complex.normSq β : ℂ) := by
      rw [mul_comm, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    rw [e1, e2]
  have hres := l2norm_sub_sq x (a • u + β • w)
  rw [hyn, hxy] at hres
  have hre : ((Complex.normSq a + Complex.normSq β : ℂ)).re
      = Complex.normSq a + Complex.normSq β := by
    rw [Complex.add_re, Complex.ofReal_re, Complex.ofReal_re]
  rw [hre] at hres
  have hnn : 0 ≤ l2norm (x - (a • u + β • w)) ^ 2 := sq_nonneg _
  linarith

/-- Under `c ^ 2 + t ^ 2 = 1`, the stated quadratic expression in `a` and `β` equals `t ^ 2 *
(Complex.normSq a + Complex.normSq β)`. -/
private theorem split_identity (c t : ℝ) (a β : ℂ) (hct : c ^ 2 + t ^ 2 = 1) :
    Complex.normSq a + Complex.normSq (((c : ℂ)) * a + ((t : ℂ)) * β)
      - 2 * c * (star a * (((c : ℂ)) * a + ((t : ℂ)) * β)).re
      = t ^ 2 * (Complex.normSq a + Complex.normSq β) := by
  have h1 : Complex.normSq (((c : ℂ)) * a + ((t : ℂ)) * β)
      = c ^ 2 * Complex.normSq a + t ^ 2 * Complex.normSq β
        + 2 * c * t * (a * star β).re := by
    rw [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_mul,
      Complex.normSq_ofReal, Complex.normSq_ofReal]
    have hstar : (starRingEnd ℂ) (((t : ℂ)) * β) = ((t : ℂ)) * star β := by
      rw [show (starRingEnd ℂ) (((t : ℂ)) * β) = star (((t : ℂ)) * β) from by
          rw [Complex.star_def], star_mul, star_ofReal']
      ring
    rw [hstar]
    have hz : (((c : ℂ)) * a) * (((t : ℂ)) * star β)
        = (((c : ℂ)) * ((t : ℂ))) * (a * star β) := by ring
    have hcast : (((c : ℂ)) * ((t : ℂ))) * (a * star β)
        = Complex.ofReal (c * t) * (a * star β) := by rw [Complex.ofReal_mul]
    rw [hz, hcast, re_ofReal_mul]
    ring
  have h2 : (star a * (((c : ℂ)) * a + ((t : ℂ)) * β)).re
      = c * Complex.normSq a + t * (star a * β).re := by
    have e1 : star a * (((c : ℂ)) * a) = ((c : ℂ)) * (star a * a) := by ring
    have e2 : star a * (((t : ℂ)) * β) = ((t : ℂ)) * (star a * β) := by ring
    rw [mul_add, Complex.add_re, e1, e2, re_ofReal_mul, re_ofReal_mul, re_conj_mul_self]
  have hconj : (a * star β).re = (star a * β).re := by
    have hz : a * star β = star (star a * β) := by
      rw [star_mul, star_star]
      ring
    rw [hz, Complex.star_def]
    exact Complex.conj_re _
  rw [h1, h2, hconj]
  linear_combination (-(Complex.normSq a) * hct)

/-- For normalized vectors, the operator norm of their rank-one difference is the square root of
one minus the squared overlap magnitude. -/
theorem opNorm_rankOne_sub {u v : I → ℂ} (hu : l2norm u = 1) (hv : l2norm v = 1) :
    ‖rankOne u - rankOne v‖ = Real.sqrt (1 - l2abs u v ^ 2) := by
  have hr : rankOne (phaseAlign u v) = rankOne v :=
    rankOne_smul_unit (normSq_phaseFactor u v) v
  rw [show rankOne v = rankOne (phaseAlign u v) from hr.symm]
  set v' : I → ℂ := phaseAlign u v with hv'def
  have hv'1 : l2norm v' = 1 := by rw [l2norm_phaseAlign, hv]
  have hs : l2inner u v' = ((l2abs u v : ℝ) : ℂ) := l2inner_phaseAlign u v
  have hc1 : l2abs u v ≤ 1 := l2abs_le_one hu hv
  rcases eq_or_lt_of_le hc1 with h1 | hlt
  · have hsq : phaseDist u v ^ 2 = 0 := by
      rw [phaseDist_sq, hu, hv, h1]
      norm_num
    have hd0 : phaseDist u v = 0 := sq_eq_zero_iff.mp hsq
    have hzero : u - phaseAlign u v = 0 := (l2norm_eq_zero (u - phaseAlign u v)).mp hd0
    have huv' : u = v' := by
      calc u = (u - v') + v' := by ring
        _ = v' := by rw [show u - v' = 0 from hzero, zero_add]
    have hrhs : Real.sqrt (1 - l2abs u v ^ 2) = 0 := by
      rw [h1]
      simp
    have hdiff : rankOne u - rankOne v' = 0 := by rw [huv', sub_self]
    rw [hdiff, norm_zero, hrhs]
  · have hc0 : 0 ≤ l2abs u v := l2abs_nonneg u v
    set c : ℝ := l2abs u v with hc
    set t : ℝ := Real.sqrt (1 - c ^ 2) with ht
    have hc2 : c ^ 2 ≤ 1 := pow_le_one₀ hc0 (le_of_lt hlt)
    have ht2 : t ^ 2 = 1 - c ^ 2 := Real.sq_sqrt (sub_nonneg.mpr hc2)
    have htpos : 0 < t := Real.sqrt_pos.mpr (by nlinarith)
    have htne : t ≠ 0 := ne_of_gt htpos
    have htc : ((t : ℂ)) ≠ 0 := by exact_mod_cast htne
    set w : I → ℂ := ((1 / (t : ℂ))) • (v' - ((c : ℂ)) • u) with hw
    have huperp : l2inner u w = 0 := by
      rw [hw, l2inner_smul_right, l2inner_sub_right, l2inner_smul_right,
        l2inner_self_of_norm hu, hs]
      ring
    have hv'u : l2norm (v' - ((c : ℂ)) • u) = t := by
      refine eq_of_sq_eq (l2norm_nonneg _) (by positivity) ?_
      have hre : (l2inner v' (((c : ℂ)) • u)).re = c * c := by
        rw [l2inner_smul_right, l2inner_symm, hs, star_ofReal', ← Complex.ofReal_mul,
          Complex.ofReal_re]
      rw [l2norm_sub_sq, hv'1, l2norm_smul, hu, mul_one,
        Real.sq_sqrt (Complex.normSq_nonneg _), Complex.normSq_ofReal, hre, ht2]
      ring
    have hwnorm : l2norm w = 1 := by
      rw [hw, l2norm_smul, hv'u]
      have hcoe : ((1 / t : ℝ) : ℂ) = 1 / ((t : ℂ)) := by
        rw [Complex.ofReal_div, Complex.ofReal_one]
      rw [← hcoe, Complex.normSq_ofReal]
      have hsq' : (1 / t) * (1 / t) = (1 / t) ^ 2 := by ring
      rw [hsq', Real.sqrt_sq (one_div_nonneg.mpr (le_of_lt htpos))]
      field_simp
    have hv'sum : v' = ((c : ℂ)) • u + ((t : ℂ)) • w := by
      have hmul : ((t : ℂ)) * (1 / ((t : ℂ))) = 1 := by field_simp
      have hcancel : ((t : ℂ)) • (((1 / (t : ℂ))) • (v' - ((c : ℂ)) • u))
          = v' - ((c : ℂ)) • u := by
        rw [smul_smul, hmul, one_smul]
      calc v' = ((c : ℂ)) • u + (v' - ((c : ℂ)) • u) := by abel
        _ = ((c : ℂ)) • u + ((t : ℂ)) • w := by rw [hw, hcancel]
    refine le_antisymm ?_ ?_
    · refine opNorm_le_of_l2 (Real.sqrt_nonneg _) ?_
      intro x
      set a := l2inner u x with hax
      set β := l2inner w x with hbx
      have hb : l2inner v' x = ((c : ℂ)) * a + ((t : ℂ)) * β := by
        rw [hv'sum, l2inner_add_left, l2inner_smul_left, l2inner_smul_left,
          star_ofReal', star_ofReal', ← hax, ← hbx]
      have hexp : l2norm (a • u - (((c : ℂ)) * a + ((t : ℂ)) * β) • v') ^ 2
          = Complex.normSq a + Complex.normSq (((c : ℂ)) * a + ((t : ℂ)) * β)
            - 2 * c * (star a * (((c : ℂ)) * a + ((t : ℂ)) * β)).re := by
        have hrw : star a * ((((c : ℂ)) * a + ((t : ℂ)) * β) * ((c : ℂ)))
            = ((c : ℂ)) * (star a * (((c : ℂ)) * a + ((t : ℂ)) * β)) := by ring
        rw [l2norm_sub_sq, l2norm_smul, hu, mul_one,
          Real.sq_sqrt (Complex.normSq_nonneg a), l2norm_smul, hv'1, mul_one,
          Real.sq_sqrt (Complex.normSq_nonneg _), l2inner_smul_left, l2inner_smul_right,
          hs, hrw, re_ofReal_mul]
        ring
      have hkey := split_identity c t a β (by linarith)
      have hbes := bessel_two (x := x) hu hwnorm huperp
      rw [Matrix.sub_mulVec, rankOne_mulVec, rankOne_mulVec, hb, ← hax]
      refine le_of_sq_le (l2norm_nonneg _) (mul_nonneg (le_of_lt htpos) (l2norm_nonneg x)) ?_
      have hR : (t * l2norm x) ^ 2 = t ^ 2 * l2norm x ^ 2 := by ring
      rw [hexp, hkey, hR]
      exact mul_le_mul_of_nonneg_left hbes (sq_nonneg t)
    · have hact := l2norm_mulVec_le (rankOne u - rankOne v') u
      rw [hu, mul_one] at hact
      have hTu : (rankOne u - rankOne v') *ᵥ u = u - ((c : ℂ)) • v' := by
        rw [Matrix.sub_mulVec, rankOne_mulVec, rankOne_mulVec, l2inner_self_of_norm hu,
          one_smul, l2inner_symm, hs, star_ofReal']
      rw [hTu] at hact
      have hex : l2norm (u - ((c : ℂ)) • v') = t := by
        refine eq_of_sq_eq (l2norm_nonneg _) (by positivity) ?_
        have hre : (l2inner u (((c : ℂ)) • v')).re = c * c := by
          rw [l2inner_smul_right, hs, ← Complex.ofReal_mul, Complex.ofReal_re]
        rw [l2norm_sub_sq, hu, l2norm_smul, hv'1, mul_one,
          Real.sq_sqrt (Complex.normSq_nonneg _), Complex.normSq_ofReal, hre, ht2]
        ring
      rw [hex] at hact
      exact hact

omit [DecidableEq I] in

/-- For normalized vectors, the square root of one minus the squared overlap magnitude is at
most their phase distance. -/
theorem sqrt_le_phaseDist {u v : I → ℂ} (hu : l2norm u = 1) (hv : l2norm v = 1) :
    Real.sqrt (1 - l2abs u v ^ 2) ≤ phaseDist u v := by
  have hc1 := l2abs_le_one hu hv
  refine le_of_sq_le (Real.sqrt_nonneg _) (phaseDist_nonneg u v) ?_
  rw [phaseDist_sq, hu, hv, Real.sq_sqrt (by nlinarith [l2abs_nonneg u v])]
  nlinarith [sq_nonneg (1 - l2abs u v)]

/-- The norm distance between the complementary projectors of normalized vectors is at most
their phase distance. -/
theorem mixerGen_diff_le {u v : I → ℂ} (hu : l2norm u = 1) (hv : l2norm v = 1) :
    ‖(1 - rankOne u) - (1 - rankOne v)‖ ≤ phaseDist u v := by
  have e : (1 - rankOne u) - (1 - rankOne v) = -(rankOne u - rankOne v) := by abel
  rw [e, norm_neg]
  calc ‖rankOne u - rankOne v‖ = Real.sqrt (1 - l2abs u v ^ 2) := opNorm_rankOne_sub hu hv
    _ ≤ phaseDist u v := sqrt_le_phaseDist hu hv

end Qatlib.Papers.ProjectorQAOA26.StageStability
