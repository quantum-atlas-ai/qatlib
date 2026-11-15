/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.LaurentPolys.ProfileFftBound.AnnulusFourierDecay

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- The Fourier coefficient of the unit circle pullback equals the circle average weighted by
the corresponding negative integer power. -/
theorem circle_fourierCoeff_eq_circleAverage (f : ℂ → ℂ) (k : ℤ) :
    fourierCoeff (T := 2 * Real.pi)
      (fun θ : AddCircle (2 * Real.pi) => f (θ.toCircle : ℂ)) k =
      Real.circleAverage (fun z => z ^ (-k) * f z) 0 1 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hc (θ : ℝ) : (AddCircle.toCircle (θ : AddCircle (2 * Real.pi)) : ℂ) =
      Complex.exp (θ * Complex.I) := by
    rw [← fourier_one, fourier_coe_apply]
    congr 1
    push_cast
    field_simp
  rw [fourierCoeff_eq_intervalIntegral _ _ 0, Real.circleAverage]
  simp only [zero_add, one_div]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [smul_eq_mul, fourier_coe_apply, circleMap, zero_add,
    Complex.ofReal_one, one_mul]
  rw [hc, ← Complex.exp_int_mul]
  congr 1
  congr 1
  push_cast
  field_simp

/-- The Fourier coefficient of the unit circle pullback equals the normalized weighted contour
integral on the unit circle. -/
theorem circle_fourierCoeff_eq_contour (f : ℂ → ℂ) (k : ℤ) :
    fourierCoeff (T := 2 * Real.pi)
      (fun θ : AddCircle (2 * Real.pi) => f (θ.toCircle : ℂ)) k =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ •
        ∮ z : ℂ in C(0, 1), z ^ (-k - 1) * f z := by
  rw [Qatlib.Concepts.LaurentPolys.ProfileFftBound.AnnulusFourierDecay.circle_fourierCoeff_eq_circleAverage,
    Real.circleAverage_eq_circleIntegral (by norm_num : (1 : ℝ) ≠ 0)]
  congr 1
  apply circleIntegral.integral_congr (by norm_num : (0 : ℝ) ≤ 1)
  intro z hz
  have hz1 : ‖z‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right, abs_one] using hz
  have hz0 : z ≠ 0 := norm_pos_iff.mp (by rw [hz1]; norm_num)
  simp only [sub_zero, smul_eq_mul]
  rw [← zpow_neg_one, ← mul_assoc, ← zpow_add₀ hz0]
  rw [show (-1 : ℤ) + (-k) = -k - 1 by ring]

/-- For a function analytic near the closed annulus, the weighted contour integral is unchanged
between any two positive radii within the annulus. -/
private theorem annulus_weighted_contour_eq
    (f : ℂ → ℂ) (r : ℝ)
    (hf : AnalyticOnNhd ℂ f {z | r⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ r})
    (k : ℤ) (l u : ℝ) (hl : 0 < l) (hle : l ≤ u)
    (hlr : r⁻¹ ≤ l) (hur : u ≤ r) :
    (∮ z : ℂ in C(0, u), z ^ (-k - 1) * f z) =
      ∮ z : ℂ in C(0, l), z ^ (-k - 1) * f z := by
  let g : ℂ → ℂ := fun z => z ^ (-k - 1) * f z
  have hd (z : ℂ) (hzl : l ≤ ‖z‖) (hzu : ‖z‖ ≤ u) :
      DifferentiableAt ℂ g z := by
    have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hl hzl)
    have hp : AnalyticAt ℂ (fun w : ℂ => w ^ (-k - 1)) z :=
      (analyticAt_id : AnalyticAt ℂ (fun w : ℂ => w) z).zpow hz0
    exact (hp.mul (hf z ⟨hlr.trans hzl, hzu.trans hur⟩)).differentiableAt
  have hc : ContinuousOn g (Metric.closedBall 0 u \ Metric.ball 0 l) := by
    intro z hz
    have hz' : ‖z‖ ≤ u ∧ l ≤ ‖z‖ := by
      simpa only [Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball,
        dist_zero_right, not_lt] using hz
    exact (hd z hz'.2 hz'.1).continuousAt.continuousWithinAt
  apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
    hl hle Set.countable_empty hc
  intro z hz
  have hz' : ‖z‖ < u ∧ l < ‖z‖ := by
    simpa only [Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall,
      dist_zero_right, Set.mem_empty_iff_false, not_false_eq_true,
      and_true, not_le] using hz
  exact hd z hz'.2.le hz'.1.le

/-- An analytic function bounded by `B` on the annulus has its nonnegative Fourier coefficient
norm bounded by `B / r^n`. -/
private theorem annulus_fourierCoeff_nonneg_bound
    (f : ℂ → ℂ) (r B : ℝ) (hr : 1 < r)
    (hf : AnalyticOnNhd ℂ f {z | r⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ r})
    (hbound : ∀ z ∈ {z : ℂ | r⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ r}, ‖f z‖ ≤ B)
    (n : ℕ) :
    ‖fourierCoeff (T := 2 * Real.pi)
      (fun θ : AddCircle (2 * Real.pi) => f (θ.toCircle : ℂ)) (n : ℤ)‖ ≤
      B / r ^ n := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hi1 : r⁻¹ ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hr.le
  rw [Qatlib.Concepts.LaurentPolys.ProfileFftBound.AnnulusFourierDecay.circle_fourierCoeff_eq_contour]
  have he := annulus_weighted_contour_eq f r hf (n : ℤ) 1 r
    zero_lt_one hr.le hi1 le_rfl
  rw [← he]
  have hexp : -(n : ℤ) - 1 = -((n + 1 : ℕ) : ℤ) := by omega
  have hb : ∀ z ∈ Metric.sphere (0 : ℂ) r,
      ‖z ^ (-(n : ℤ) - 1) * f z‖ ≤ (r ^ (n + 1))⁻¹ * B := by
    intro z hz
    have hzr : ‖z‖ = r := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hz
    rw [norm_mul, norm_zpow, hzr, hexp, zpow_neg, zpow_natCast]
    exact mul_le_mul_of_nonneg_left
      (hbound z ⟨by rw [hzr]; exact hi1.trans hr.le, hzr.le⟩)
      (inv_nonneg.mpr (pow_nonneg hr0.le _))
  apply (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr0.le hb).trans
  have hpow : r ^ n ≠ 0 := pow_ne_zero _ hr0.ne'
  rw [pow_succ]
  field_simp
  exact le_rfl

/-- An analytic function bounded by `B` on the annulus has its Fourier coefficient at index
`-((n+1 : ℕ) : ℤ)` bounded in norm by `B / r^(n+1)`. -/
private theorem annulus_fourierCoeff_neg_bound
    (f : ℂ → ℂ) (r B : ℝ) (hr : 1 < r)
    (hf : AnalyticOnNhd ℂ f {z | r⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ r})
    (hbound : ∀ z ∈ {z : ℂ | r⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ r}, ‖f z‖ ≤ B)
    (n : ℕ) :
    ‖fourierCoeff (T := 2 * Real.pi)
      (fun θ : AddCircle (2 * Real.pi) => f (θ.toCircle : ℂ))
      (-((n + 1 : ℕ) : ℤ))‖ ≤ B / r ^ (n + 1) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hi1 : r⁻¹ ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hr.le
  rw [Qatlib.Concepts.LaurentPolys.ProfileFftBound.AnnulusFourierDecay.circle_fourierCoeff_eq_contour]
  have he := annulus_weighted_contour_eq f r hf (-((n + 1 : ℕ) : ℤ)) r⁻¹ 1
    (inv_pos.mpr hr0) hi1 le_rfl hr.le
  rw [he]
  have hexp : -(-((n + 1 : ℕ) : ℤ)) - 1 = (n : ℤ) := by omega
  have hb : ∀ z ∈ Metric.sphere (0 : ℂ) r⁻¹,
      ‖z ^ (-(-((n + 1 : ℕ) : ℤ)) - 1) * f z‖ ≤ (r⁻¹) ^ n * B := by
    intro z hz
    have hzr : ‖z‖ = r⁻¹ := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hz
    rw [norm_mul, norm_zpow, hzr, hexp, zpow_natCast]
    exact mul_le_mul_of_nonneg_left
      (hbound z ⟨hzr.ge, by rw [hzr]; exact hi1.trans hr.le⟩)
      (pow_nonneg (inv_nonneg.mpr hr0.le) _)
  calc
    _ ≤ r⁻¹ * ((r⁻¹) ^ n * B) :=
      circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
        (inv_nonneg.mpr hr0.le) hb
    _ = B / r ^ (n + 1) := by
      rw [div_eq_mul_inv, inv_pow, pow_succ]
      ring

/-- Analyticity and boundedness on the annulus give geometric Fourier coefficient decay,
absolute summability, and a Fourier series summing to the function on the unit circle. -/
theorem annulus_fourier_decay (f : ℂ → ℂ) (r B : ℝ)
    (hr : 1 < r) (_hB : 0 ≤ B) :
    let S : Set ℂ := {z | r⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ r}
    AnalyticOnNhd ℂ f S → (∀ z ∈ S, ‖f z‖ ≤ B) →
    let a : ℤ → ℂ := fourierCoeff (T := 2 * Real.pi)
      (fun θ : AddCircle (2 * Real.pi) => f (θ.toCircle : ℂ))
    (∀ k : ℤ, ‖a k‖ ≤ B / r ^ k.natAbs) ∧
    Summable (fun k : ℤ => ‖a k‖) ∧
    (∀ θ : AddCircle (2 * Real.pi),
      HasSum (fun k : ℤ => a k * fourier k θ) (f (θ.toCircle : ℂ))) := by
  (try dsimp only)
  intro hf hbound
  let a : ℤ → ℂ := fourierCoeff (T := 2 * Real.pi)
    (fun θ : AddCircle (2 * Real.pi) => f (θ.toCircle : ℂ))
  change (∀ k : ℤ, ‖a k‖ ≤ B / r ^ k.natAbs) ∧
    Summable (fun k : ℤ => ‖a k‖) ∧
    (∀ θ : AddCircle (2 * Real.pi),
      HasSum (fun k : ℤ => a k * fourier k θ) (f (θ.toCircle : ℂ)))
  have hdecay : ∀ k : ℤ, ‖a k‖ ≤ B / r ^ k.natAbs := by
    intro k
    cases k with
    | ofNat n => exact annulus_fourierCoeff_nonneg_bound f r B hr hf hbound n
    | negSucc n =>
      change ‖fourierCoeff (T := 2 * Real.pi)
        (fun θ : AddCircle (2 * Real.pi) => f (θ.toCircle : ℂ))
        (-((n + 1 : ℕ) : ℤ))‖ ≤ B / r ^ (n + 1)
      exact annulus_fourierCoeff_neg_bound f r B hr hf hbound n
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hgeom : Summable (fun n : ℕ => (r⁻¹) ^ n) :=
    summable_geometric_of_lt_one (inv_nonneg.mpr hr0.le) ((inv_lt_one₀ hr0).mpr hr)
  have hnat : Summable (fun n : ℕ => B / r ^ n) := by
    simpa only [div_eq_mul_inv, inv_pow] using hgeom.mul_left B
  have hint : Summable (fun k : ℤ => B / r ^ k.natAbs) := by
    apply summable_int_iff_summable_nat_and_neg.mpr
    constructor <;> simpa only [Int.natAbs_natCast, Int.natAbs_neg] using hnat
  have hnormsum : Summable (fun k : ℤ => ‖a k‖) :=
    hint.of_norm_bounded (fun k => by simpa only [norm_norm] using hdecay k)
  have hi1 : r⁻¹ ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hr.le
  have hcont : Continuous (fun θ : AddCircle (2 * Real.pi) => f (θ.toCircle : ℂ)) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    have hz1 : ‖(θ.toCircle : ℂ)‖ = 1 := θ.toCircle.norm_coe
    have hz : (θ.toCircle : ℂ) ∈ {z : ℂ | r⁻¹ ≤ ‖z‖ ∧ ‖z‖ ≤ r} :=
      ⟨by rw [hz1]; exact hi1, by rw [hz1]; exact hr.le⟩
    exact (hf (θ.toCircle : ℂ) hz).continuousAt.comp
      (f := fun u : AddCircle (2 * Real.pi) => (u.toCircle : ℂ))
      (show ContinuousAt (fun u : AddCircle (2 * Real.pi) => (u.toCircle : ℂ)) θ by
        fun_prop)
  let F : C(AddCircle (2 * Real.pi), ℂ) := ⟨_, hcont⟩
  have hs : Summable (fourierCoeff F) := by
    change Summable a
    exact hnormsum.of_norm
  refine ⟨hdecay, hnormsum, ?_⟩
  intro θ
  simpa only [smul_eq_mul] using! has_pointwise_sum_fourier_series_of_summable hs θ

end Qatlib.Concepts.LaurentPolys.ProfileFftBound.AnnulusFourierDecay
