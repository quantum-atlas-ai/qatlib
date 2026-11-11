/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Qatlib.Papers.Recommender18.MainResults.SourceDefinitions
import Qatlib.Concepts.SqEstimation.InnerProduct.SQInnerProductEstimation
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 4.2 — estimating an inner product by ℓ₂ sampling

Fixed arXiv:1807.04271, Proposition 4.2 (p. 12).  Given query access to
`x, y ∈ ℝⁿ`, sample access to `D_x`, and knowledge of `‖x‖`, the inner product
`⟨x, y⟩` can be estimated to additive error `‖x‖ ‖y‖ ε` with probability at
least `1 − δ` using `O((1/ε²) log(1/δ))` queries and samples.

Formalisation route: the paper's estimator is exactly the finite
sample-based mean/median estimator of the frozen SQ framework.  We instantiate
`FiniteSQInput` with envelope `x` (sampled from `D_x`), target `x` and the
query vector `y` (both coerced to `ℂ`), so that `sqInnerTarget` is `⟨x,y⟩`.
The statistical guarantee is the frozen
`finite_sq_component_median_complex_guarantee`; we additionally exhibit the
sample counts `m = ⌈64/ε²⌉`, `r = ⌈log₂(1/δ)⌉ − 1` and bound the total number
of samples `m (2r+1)` by a constant times `(1/ε² + 1)(log₂(1/δ) + 1)`.
-/

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SqEstimation.InnerProduct

namespace Qatlib.Papers.Recommender18.MainResults.SqEstimation

noncomputable section

/-- A real vector, regarded as a complex vector (the paper's real inner
product seen through the complex SQ framework). -/
def toComplex {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) : Fin n → ℂ := fun i => (v i : ℂ)

/-- Paper's real inner product `⟨x,y⟩ = Σ_i x_i y_i`. -/
def innerReal {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) : ℝ := ∑ i, x i * y i

/-- The squared norm of the complexified vector equals the ℓ₂ norm squared. -/
theorem sqSquaredNorm_toComplex {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) :
    sqSquaredNorm (toComplex v) = ‖v‖ ^ 2 := by
  unfold sqSquaredNorm toComplex
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.normSq_ofReal, sq]

/-- The complex SQ target of `(x, y)` is the real inner product `⟨x,y⟩`. -/
theorem sqInnerTarget_toComplex {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) :
    sqInnerTarget (toComplex x) (toComplex y) = (innerReal x y : ℂ) := by
  unfold sqInnerTarget innerReal toComplex
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.star_def, Complex.conj_ofReal]

/-- `FiniteSQInput` with envelope = target = `x`, sampled from `D_x`; the query
vector is supplied separately.  This is the access model of Proposition 4.2. -/
def sqInputOfVector {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    FiniteSQInput (Fin n) where
  target := toComplex x
  envelope := toComplex x
  samples := l2Dist x hx
  cachedEnvelopeSquaredNorm := ‖x‖ ^ 2
  norm_spec := (sqSquaredNorm_toComplex x).symm
  envelope_pos := by
    rw [sqSquaredNorm_toComplex]
    exact pow_pos (norm_pos_iff.mpr hx) 2
  domination i := le_rfl
  sample_spec i := by
    rw [l2Dist_prob, sqSquaredNorm_toComplex]
    simp [toComplex, Complex.normSq_ofReal, sq]

/-- The frozen failure probability `2 · 2^{2r+1} · (1/16)^{r+1}` equals
`(1/4)^{r+1}`. -/
theorem failure_mass_eq (r : ℕ) :
    2 * (2 : ℝ) ^ (2 * r + 1) * ((1 : ℝ) / 16) ^ (r + 1) = ((1 : ℝ) / 4) ^ (r + 1) := by
  induction r with
  | zero => norm_num
  | succ r ih =>
      have h2 : (2 : ℝ) ^ (2 * (r + 1) + 1) = (2 : ℝ) ^ (2 * r + 1) * 4 := by
        rw [show 2 * (r + 1) + 1 = (2 * r + 1) + 2 by omega, pow_add]
        norm_num
      have h16 : ((1 : ℝ) / 16) ^ ((r + 1) + 1) = ((1 : ℝ) / 16) ^ (r + 1) * (1 / 16) :=
        pow_succ _ _
      have h4 : ((1 : ℝ) / 4) ^ ((r + 1) + 1) = ((1 : ℝ) / 4) ^ (r + 1) * (1 / 4) :=
        pow_succ _ _
      calc 2 * (2 : ℝ) ^ (2 * (r + 1) + 1) * ((1 : ℝ) / 16) ^ ((r + 1) + 1)
          = (2 * (2 : ℝ) ^ (2 * r + 1) * ((1 : ℝ) / 16) ^ (r + 1)) * (1 / 4) := by
            rw [h2, h16]; ring
        _ = ((1 : ℝ) / 4) ^ (r + 1) * (1 / 4) := by rw [ih]
        _ = ((1 : ℝ) / 4) ^ ((r + 1) + 1) := by rw [h4]

/-- Fixed arXiv:1807.04271, Proposition 4.2 (p. 12): `⟨x,y⟩` is estimated to
additive error `‖x‖ ‖y‖ ε` with failure probability at most `δ`, using
`m (2r+1)` samples (each costing one query to `y`) with
`m ≈ 64/ε²` and `r ≈ log₂(1/δ)`.  The theorem records the explicit sample
budget `m (2r+1) ≤ 260 (1/ε² + 1)(log₂(1/δ) + 1)`. -/
theorem proposition_4_2 {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) (hy : y ≠ 0)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ m r : ℕ, 0 < m ∧
      (m : ℝ) * (2 * r + 1) ≤
        260 * (1 / ε ^ 2 + 1) * (Real.logb 2 (1 / δ) + 1) ∧
      sqBadMass (sqInputOfVector x hx) (toComplex y) m r (‖x‖ * ‖y‖ * ε) ≤ δ := by
  set L : ℝ := Real.logb 2 (1 / δ) with hL_def
  set k : ℕ := Nat.ceil L with hk_def
  set m : ℕ := Nat.ceil (64 / ε ^ 2) with hm_def
  -- basic positivity
  have h1δ : 1 < 1 / δ := one_lt_one_div hδ hδ1
  have hlogδ : 0 < Real.log (1 / δ) := Real.log_pos h1δ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL_nonneg : 0 ≤ L := by
    rw [hL_def, Real.logb]
    exact div_nonneg hlogδ.le hlog2.le
  have hLpos : 0 < L := by
    rw [hL_def, Real.logb]
    exact div_pos hlogδ hlog2
  have hkpos : 0 < k := by
    rw [hk_def]
    exact Nat.ceil_pos.mpr hLpos
  -- failure probability is at most δ
  have hquarter : ((1 : ℝ) / 4) ^ k ≤ δ := by
    have hmono : ((1 : ℝ) / 4) ^ (k : ℝ) ≤ ((1 : ℝ) / 4) ^ L :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (Nat.le_ceil L)
    have hpow : ((1 : ℝ) / 4) ^ k = ((1 : ℝ) / 4) ^ (k : ℝ) := (Real.rpow_natCast _ _).symm
    have h2L : (2 : ℝ) ^ L = 1 / δ := by
      rw [hL_def]
      exact Real.rpow_logb (b := 2) (x := 1 / δ) (by norm_num) (by norm_num) (by positivity)
    have h4L : (4 : ℝ) ^ L = ((1 / δ) ^ 2) := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.mul_rpow (by norm_num) (by norm_num), h2L]
      ring
    have hLeq : ((1 : ℝ) / 4) ^ L = δ ^ 2 := by
      rw [show (1 : ℝ) / 4 = (4 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num) L, h4L]
      field_simp
    rw [hpow]
    calc ((1 : ℝ) / 4) ^ (k : ℝ) ≤ ((1 : ℝ) / 4) ^ L := hmono
      _ = δ ^ 2 := hLeq
      _ ≤ δ := by nlinarith [hδ.le, hδ1]
  -- the sample budget hypothesis of the frozen estimator
  have hbudget : 64 * sqSquaredNorm (sqInputOfVector x hx).envelope *
      sqSquaredNorm (toComplex y) ≤ (m : ℝ) * (‖x‖ * ‖y‖ * ε) ^ 2 := by
    have hm_ge : (64 : ℝ) / ε ^ 2 ≤ (m : ℝ) := Nat.le_ceil _
    have hmul : (64 : ℝ) ≤ (m : ℝ) * ε ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hm_ge (sq_nonneg ε)
      have heq : (64 : ℝ) / ε ^ 2 * ε ^ 2 = 64 := by field_simp
      linarith
    have hsqx : sqSquaredNorm (sqInputOfVector x hx).envelope = ‖x‖ ^ 2 := by
      simpa only [sqInputOfVector] using sqSquaredNorm_toComplex x
    have hsqy : sqSquaredNorm (toComplex y) = ‖y‖ ^ 2 := sqSquaredNorm_toComplex y
    rw [hsqx, hsqy]
    calc 64 * ‖x‖ ^ 2 * ‖y‖ ^ 2 = 64 * (‖x‖ ^ 2 * ‖y‖ ^ 2) := by ring
      _ ≤ ((m : ℝ) * ε ^ 2) * (‖x‖ ^ 2 * ‖y‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hmul (by positivity)
      _ = (m : ℝ) * (‖x‖ * ‖y‖ * ε) ^ 2 := by ring
  have hmpos : 0 < m := by
    rw [hm_def]
    exact Nat.ceil_pos.mpr (by positivity)
  have hεpaper : 0 < ‖x‖ * ‖y‖ * ε := by
    have hx' : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
    positivity
  have hbad : sqBadMass (sqInputOfVector x hx) (toComplex y) m (k - 1) (‖x‖ * ‖y‖ * ε) ≤ δ := by
    have hbound := finite_sq_component_median_complex_guarantee (Fin n) (sqInputOfVector x hx)
      (toComplex y) m (k - 1) (‖x‖ * ‖y‖ * ε) hmpos hεpaper hbudget
    have hpred : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hkpos
    have hfail : 2 * (2 : ℝ) ^ (2 * (k - 1) + 1) * ((1 : ℝ) / 16) ^ (k - 1 + 1) =
        ((1 : ℝ) / 4) ^ k := by
      simpa [hpred] using failure_mass_eq (k - 1)
    calc sqBadMass (sqInputOfVector x hx) (toComplex y) m (k - 1) (‖x‖ * ‖y‖ * ε)
        ≤ 2 * (2 : ℝ) ^ (2 * (k - 1) + 1) * ((1 : ℝ) / 16) ^ (k - 1 + 1) := hbound
      _ = ((1 : ℝ) / 4) ^ k := hfail
      _ ≤ δ := hquarter
  refine ⟨m, k - 1, hmpos, ?_, hbad⟩
  -- count the samples: m < 64/ε² + 1, 2r+1 ≤ 2L+1
  have hm_ub : (m : ℝ) < 64 / ε ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hk_ub : (k : ℝ) < L + 1 := Nat.ceil_lt_add_one hL_nonneg
  have hk1 : (1 : ℕ) ≤ k := Nat.one_le_iff_ne_zero.mpr hkpos.ne'
  have hkm1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk1]
    norm_num
  rw [hkm1]
  have hk_ge_one : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hcount_nn : 0 ≤ 2 * ((k : ℝ) - 1) + 1 := by linarith
  have hkc : 2 * ((k : ℝ) - 1) + 1 ≤ 2 * L + 1 := by linarith
  have hprod : (m : ℝ) * (2 * ((k : ℝ) - 1) + 1) ≤
      (64 / ε ^ 2 + 1) * (2 * L + 1) :=
    mul_le_mul hm_ub.le hkc hcount_nn (by positivity)
  have hinvε : (0 : ℝ) < 1 / ε ^ 2 := by positivity
  calc (m : ℝ) * (2 * ((k : ℝ) - 1) + 1)
      ≤ (64 / ε ^ 2 + 1) * (2 * L + 1) := hprod
    _ ≤ 260 * (1 / ε ^ 2 + 1) * (L + 1) := by
        have hL0 : 0 ≤ L := hL_nonneg
        have hy0 : 0 ≤ 1 / ε ^ 2 := hinvε.le
        have key : (64 / ε ^ 2 + 1) * (2 * L + 1) =
            128 * (1 / ε ^ 2) * L + 64 * (1 / ε ^ 2) + 2 * L + 1 := by
          field_simp
          try ring
        have key2 : 260 * (1 / ε ^ 2 + 1) * (L + 1) =
            260 * (1 / ε ^ 2) * L + 260 * (1 / ε ^ 2) + 260 * L + 260 := by
          ring
        rw [key, key2]
        nlinarith [mul_nonneg hy0 hL0, hy0, hL0]

end

end Qatlib.Papers.Recommender18.MainResults.SqEstimation
