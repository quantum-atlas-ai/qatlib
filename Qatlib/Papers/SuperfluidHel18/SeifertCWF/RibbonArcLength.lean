/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.SeifertCWF.RibbonCWF

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Normalized arc length for closed regular ribbons

A smooth regular periodic curve admits an increasing smooth change of
parameter with a smooth inverse. Normalized arc length fixes the ends
of the original parameter interval and gives a constant speed.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SuperfluidHel18.SeifertCWF

open MeasureTheory Set
open scoped Real ContDiff
open Qatlib.Papers.KnottedLight08.HopfField (dot3)

/-- Euclidean speed of a parametrized centerline. -/
def ribbonSpeed (γ : ℝ → Fin 3 → ℝ) (s : ℝ) : ℝ :=
  Real.sqrt (dot3 (deriv γ s) (deriv γ s))

/-- Regularity makes the Euclidean speed strictly positive. -/
theorem ribbonSpeed_pos {γ : ℝ → Fin 3 → ℝ} {s : ℝ} (hreg : deriv γ s ≠ 0) :
    0 < ribbonSpeed γ s := by
  have hj : ∃ j : Fin 3, deriv γ s j ≠ 0 := by
    by_contra! h
    apply hreg
    funext j
    exact h j
  obtain ⟨j, hj⟩ := hj
  apply Real.sqrt_pos.2
  unfold dot3
  fin_cases j
  · change deriv γ s 0 ≠ 0 at hj
    nlinarith [sq_pos_of_ne_zero hj, sq_nonneg (deriv γ s 1), sq_nonneg (deriv γ s 2)]
  · change deriv γ s 1 ≠ 0 at hj
    nlinarith [sq_pos_of_ne_zero hj, sq_nonneg (deriv γ s 0), sq_nonneg (deriv γ s 2)]
  · change deriv γ s 2 ≠ 0 at hj
    nlinarith [sq_pos_of_ne_zero hj, sq_nonneg (deriv γ s 0), sq_nonneg (deriv γ s 1)]

/-- Squaring the Euclidean speed recovers the squared Cartesian tangent. -/
theorem ribbonSpeed_sq (γ : ℝ → Fin 3 → ℝ) (s : ℝ) :
    ribbonSpeed γ s ^ 2 = dot3 (deriv γ s) (deriv γ s) := by
  unfold ribbonSpeed
  apply Real.sq_sqrt
  simp only [dot3, ← pow_two]
  positivity

/-- The speed of a regular C³ curve is C². -/
theorem contDiff_ribbonSpeed {γ : ℝ → Fin 3 → ℝ} (hγ : ContDiff ℝ 3 γ)
    (hreg : ∀ s, deriv γ s ≠ 0) : ContDiff ℝ 2 (ribbonSpeed γ) := by
  have hd : ContDiff ℝ 2 (deriv γ) := hγ.deriv'
  have h : ContDiff ℝ 2 (fun s => dot3 (deriv γ s) (deriv γ s)) := by
    simp only [dot3]
    fun_prop
  exact h.sqrt (fun s => by
    rw [← ribbonSpeed_sq]
    exact pow_ne_zero _ (ribbonSpeed_pos (hreg s)).ne')

/-- The tangent of a differentiable periodic curve is periodic. -/
private theorem periodic_ribbonTangent {γ : ℝ → Fin 3 → ℝ}
    (hγ : Differentiable ℝ γ) {P : ℝ} (hp : Function.Periodic γ P) :
    Function.Periodic (deriv γ) P := by
  intro x
  have ht := ((hγ (x + P)).hasDerivAt.scomp x ((hasDerivAt_id x).add_const P)).deriv
  change deriv (fun s => γ (s + P)) x = _ at ht
  simp only [one_smul] at ht
  rw [show (fun s => γ (s + P)) = γ from funext hp] at ht
  exact ht.symm

/-- The Euclidean speed inherits the original parameter period. -/
theorem periodic_ribbonSpeed {γ : ℝ → Fin 3 → ℝ}
    (hγ : Differentiable ℝ γ) {P : ℝ} (hp : Function.Periodic γ P) :
    Function.Periodic (ribbonSpeed γ) P := by
  intro x
  simp only [ribbonSpeed, periodic_ribbonTangent hγ hp x]

/-- Shift-equivariance forces an increasing continuous parameter
change to cover the whole line once it fixes zero. -/
private theorem surjective_of_period_shift {f : ℝ → ℝ} (hc : Continuous f)
    {P : ℝ} (hP : 0 < P) (hzero : f 0 = 0) (hshift : ∀ x, f (x + P) = f x + P) :
    Function.Surjective f := by
  have hp : Function.Periodic (fun x => f x - x) P := by
    intro x
    simp only [hshift]
    ring
  have hmul (n : ℤ) : f (n • P) = n • P := by
    have h := hp.zsmul n 0
    simp only [zero_add, hzero, sub_zero] at h
    exact sub_eq_zero.mp h
  intro y
  obtain ⟨m, hm'⟩ := exists_int_lt (y / P)
  obtain ⟨n, hn'⟩ := exists_int_gt (y / P)
  have hm₁ : m • P < y := by
    rw [zsmul_eq_mul]
    exact (lt_div_iff₀ hP).1 hm'
  have hn₁ : y < n • P := by
    rw [zsmul_eq_mul]
    exact (div_lt_iff₀ hP).1 hn'
  have hy : y ∈ Icc (f (m • P)) (f (n • P)) := by
    rw [hmul, hmul]
    exact ⟨hm₁.le, hn₁.le⟩
  obtain ⟨x, _, hx⟩ := intermediate_value_Icc (hm₁.trans hn₁).le hc.continuousOn hy
  exact ⟨x, hx⟩

/-- A positive periodic speed gives a smooth increasing normalized
arc-length coordinate whose inverse is smooth and has reciprocal speed. -/
theorem exists_normalized_arcLength {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hpos : ∀ s, 0 < v s)
    {P : ℝ} (hP : 0 < P) (hper : Function.Periodic v P) :
    ∃ c : ℝ, 0 < c ∧ ∃ f : ℝ ≃ₜ ℝ,
      StrictMono f ∧ StrictMono f.symm ∧
      ContDiff ℝ 3 f ∧ ContDiff ℝ 3 f.symm ∧
      f 0 = 0 ∧ f.symm 0 = 0 ∧
      (∀ x, f (x + P) = f x + P) ∧ (∀ x, f.symm (x + P) = f.symm x + P) ∧
      (∀ x, HasDerivAt f (c * v x) x) ∧
      (∀ x, HasDerivAt f.symm (1 / (c * v (f.symm x))) x) := by
  let arc (x : ℝ) := ∫ s in 0..x, v s
  have ha (x : ℝ) : HasDerivAt arc (v x) x := by
    exact intervalIntegral.integral_hasDerivAt_right (hv.continuous.intervalIntegrable _ _)
      hv.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hv.continuous.continuousAt
  have ha0 : arc 0 = 0 := intervalIntegral.integral_same
  have hmono : StrictMono arc := strictMono_of_deriv_pos (fun x => (ha x).deriv.symm ▸ hpos x)
  have hL : 0 < arc P := ha0 ▸ hmono hP
  let c := P / arc P
  have hc : 0 < c := div_pos hP hL
  let φ (x : ℝ) := c * arc x
  have hφ (x : ℝ) : HasDerivAt φ (c * v x) x := (ha x).const_mul c
  have hφd : Differentiable ℝ φ := fun x => (hφ x).differentiableAt
  have hφc : ContDiff ℝ 3 φ := by
    change ContDiff ℝ ((2 : ℕ∞ω) + 1) φ
    refine contDiff_succ_iff_deriv.2 ⟨hφd, fun h => ?_, ?_⟩
    · norm_num at h
    · rw [show deriv φ = fun x => c * v x from funext (fun x => (hφ x).deriv)]
      exact contDiff_const.mul hv
  have hφ0 : φ 0 = 0 := by simp [φ, ha0]
  have hφP : c * arc P = P := div_mul_cancel₀ _ hL.ne'
  have hφshift (x : ℝ) : φ (x + P) = φ x + P := by
    have h := hper.intervalIntegral_add_eq_add 0 x (fun a b => hv.continuous.intervalIntegrable a b)
    simp only [zero_add] at h
    change arc (x + P) = arc x + arc P at h
    change c * arc (x + P) = c * arc x + P
    rw [h, mul_add, hφP]
  have hφmono : StrictMono φ := fun _ _ h => mul_lt_mul_of_pos_left (hmono h) hc
  let e := hφmono.orderIsoOfSurjective φ
    (surjective_of_period_shift hφd.continuous hP hφ0 hφshift)
  let f : ℝ ≃ₜ ℝ := e.toHomeomorph
  have hfc : ContDiff ℝ 3 f := hφc
  have hfd (x : ℝ) : HasDerivAt f (c * v x) x := hφ x
  have hfs := f.contDiff_symm_deriv (fun x => (mul_pos hc (hpos x)).ne') hfd hfc
  have hf0 : f 0 = 0 := hφ0
  have hfs0 : f.symm 0 = 0 := f.injective (by rw [f.apply_symm_apply, hf0])
  have hfshift (x : ℝ) : f (x + P) = f x + P := hφshift x
  have hfsshift (x : ℝ) : f.symm (x + P) = f.symm x + P := by
    apply f.injective
    rw [f.apply_symm_apply, hfshift, f.apply_symm_apply]
  refine ⟨c, hc, f, hφmono, e.symm.strictMono, hfc, hfs, hf0, hfs0, hfshift, hfsshift, hfd, ?_⟩
  intro x
  have hd := (hfs.differentiable (by norm_num) x).hasDerivAt
  have hcomp := ((hfd (f.symm x)).scomp x hd).deriv
  have hid : (f : ℝ → ℝ) ∘ f.symm = id := funext f.apply_symm_apply
  rw [hid, deriv_id, smul_eq_mul] at hcomp
  have hrecip := (eq_div_iff (mul_pos hc (hpos (f.symm x))).ne').2 hcomp.symm
  exact hd.congr_deriv hrecip

end Qatlib.Papers.SuperfluidHel18.SeifertCWF
