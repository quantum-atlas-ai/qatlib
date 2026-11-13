/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.PoissonMesh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Sampling estimates for analytic strip functions

This module obtains normal convergence of mesh translates from integrability of a function and
its derivative. For holomorphic strip functions, bounded horizontal norm integrals provide
derivative integrability and hence the sampling hypotheses needed for the quadrature estimates
of [AftabAnTrivisa2026].

## Main statements

* `normal_convergence_of_strip`: normal convergence from strip mass bounds.
* `analytic_strip_mesh_error_of_norm_decay`: the exponential mesh error estimate with norm
  decay.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.StripSampling

open Complex Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology BigOperators FourierTransform

variable {E : Type*} [NormedAddCommGroup E]

section Real

variable [NormedSpace ℝ E]

/-- The sum of the integrals of `‖g‖` and `‖deriv g‖` over the integer cell `[n, n + 1]`. -/
def cellMass (g : ℝ → E) (n : ℤ) : ℝ :=
  (∫ t : ℝ in (n : ℝ)..(n : ℝ) + 1, ‖g t‖) +
    ∫ t : ℝ in (n : ℝ)..(n : ℝ) + 1, ‖deriv g t‖

/-- The oscillation of a differentiable function between two points in an interval is bounded by
the integral of its derivative norm over that interval. -/
theorem norm_sub_le_cell_deriv (g : ℝ → E) (hg : Differentiable ℝ g)
    (hdi : Integrable (deriv g)) (a b x y : ℝ) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    ‖g x - g y‖ ≤ ∫ t : ℝ in a..b, ‖deriv g t‖ := by
  have hd (u v : ℝ) (huv : u ≤ v) (hu : a ≤ u) (hv : v ≤ b) :
      ‖g v - g u‖ ≤ ∫ t : ℝ in a..b, ‖deriv g t‖ := by
    refine (norm_sub_le_integral_of_norm_deriv_le_of_le huv hg.continuous.continuousOn
      hg.differentiableOn (Eventually.of_forall (fun _ _ => le_rfl))
      hdi.norm.intervalIntegrable).trans ?_
    exact intervalIntegral.integral_mono_interval hu huv hv
      (Eventually.of_forall (fun t => norm_nonneg _)) hdi.norm.intervalIntegrable
  by_cases hxy : y ≤ x
  · exact hd y x hxy hy.1 hx.2
  · rw [norm_sub_rev]
    exact hd x y (le_of_not_ge hxy) hx.1 hy.2

/-- The norm of a differentiable function at any point of an integer cell is bounded by
`cellMass`, assuming integrability of the function and its derivative. -/
theorem norm_le_cellMass (g : ℝ → E) (hg : Differentiable ℝ g) (hi : Integrable g)
    (hdi : Integrable (deriv g)) (n : ℤ) (x : ℝ) (hx : x ∈ Icc (n : ℝ) ((n : ℝ) + 1)) :
    ‖g x‖ ≤ cellMass g n := by
  let D := ∫ t : ℝ in (n : ℝ)..(n : ℝ) + 1, ‖deriv g t‖
  have hp (y : ℝ) (hy : y ∈ Icc (n : ℝ) ((n : ℝ) + 1)) : ‖g x‖ ≤ ‖g y‖ + D := by
    calc
      _ ≤ ‖g x - g y‖ + ‖g y‖ := norm_le_norm_sub_add _ _
      _ ≤ D + ‖g y‖ := add_le_add (norm_sub_le_cell_deriv g hg hdi _ _ x y hx hy) le_rfl
      _ = _ := add_comm _ _
  have h := intervalIntegral.integral_mono_on (show (n : ℝ) ≤ (n : ℝ) + 1 by linarith)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ‖g x‖) volume _ _)
    (hi.norm.intervalIntegrable.add intervalIntegrable_const) hp
  rw [intervalIntegral.integral_add hi.norm.intervalIntegrable intervalIntegrable_const] at h
  simpa [cellMass, D] using h

/-- The mass of every integer cell is nonnegative. -/
theorem cellMass_nonneg (g : ℝ → E) (n : ℤ) : 0 ≤ cellMass g n := by
  apply add_nonneg <;> apply intervalIntegral.integral_nonneg (by linarith) <;>
    intro t _ <;> exact norm_nonneg _

/-- Integrability of a function and its derivative implies summability of the integer cell
masses. -/
theorem summable_cellMass (g : ℝ → E) (hi : Integrable g) (hdi : Integrable (deriv g)) :
    Summable (cellMass g) := by
  simpa only [cellMass, zero_add] using!
    (hi.norm.hasSum_intervalIntegral 0).summable.add (hdi.norm.hasSum_intervalIntegral 0).summable

/-- A differentiable continuous function with integrable function and derivative has normally
convergent integer translates on every compact set. -/
theorem normal_convergence_of_integrable_deriv (g : C(ℝ, E)) (hg : Differentiable ℝ (g : ℝ → E))
    (hi : Integrable (g : ℝ → E)) (hdi : Integrable (deriv (g : ℝ → E))) :
    ∀ K : Compacts ℝ,
      Summable (fun n : ℤ => ‖(g.comp (ContinuousMap.addRight n)).restrict K‖) := by
  intro K
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨N, hN⟩ := exists_nat_gt R
  let S : Finset ℤ := Finset.Icc (-(N : ℤ)) N
  have hs : Summable (fun n : ℤ => ∑ j ∈ S, cellMass (g : ℝ → E) (n + j)) := by
    apply summable_sum
    intro j _
    exact (summable_cellMass (g : ℝ → E) hi hdi).comp_injective (add_left_injective j)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hs
  intro n
  apply (ContinuousMap.norm_le _ (Finset.sum_nonneg (fun j _ => cellMass_nonneg _ _))).mpr
  intro x
  have hxR : |(x : ℝ)| ≤ R := by simpa [Real.dist_eq] using hR x.2
  let j : ℤ := ⌊(x : ℝ)⌋
  have hj : j ∈ S := by
    apply Finset.mem_Icc.mpr
    constructor
    · apply Int.le_floor.mpr
      have hxlow := (abs_le.mp hxR).1
      have hl : -(N : ℝ) ≤ (x : ℝ) := by linarith
      simpa only [Int.cast_neg, Int.cast_natCast] using hl
    · apply Int.floor_le_iff.mpr
      change (x : ℝ) < (N : ℝ) + 1
      linarith [(abs_le.mp hxR).2]
  have hxcell : (x : ℝ) + (n : ℝ) ∈ Icc ((n + j : ℤ) : ℝ) (((n + j : ℤ) : ℝ) + 1) := by
    push_cast
    constructor
    · linarith [Int.floor_le (x : ℝ)]
    · linarith [Int.lt_floor_add_one (x : ℝ)]
  exact (norm_le_cellMass (g : ℝ → E) hg hi hdi (n + j) _ hxcell).trans
    (Finset.single_le_sum (fun k _ => cellMass_nonneg _ _) hj)

end Real

section Complex

variable [NormedSpace ℂ E] [CompleteSpace E]

/-- A holomorphic function on a positive-width strip with uniformly bounded integrable interior
slices has an integrable complex derivative along the real axis. -/
theorem integrable_complex_deriv (f : ℂ → E) (ρ M : ℝ) (hρ : 0 < ρ)
    (hf : DifferentiableOn ℂ f {z : ℂ | -ρ ≤ z.im ∧ z.im ≤ ρ})
    (hi : ∀ y ∈ Ioo (-ρ) ρ, Integrable (fun x : ℝ => f ((x : ℂ) + y * I)))
    (hm : ∀ y ∈ Ioo (-ρ) ρ, (∫ x : ℝ, ‖f ((x : ℂ) + y * I)‖) ≤ M) :
    Integrable (fun x : ℝ => deriv f (x : ℂ)) := by
  let r := ρ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrρ : r < ρ := by dsimp [r]; linarith
  let ν := volume.restrict (Icc (0 : ℝ) (2 * Real.pi))
  let F : ℝ × ℝ → E := fun p => f ((p.1 : ℂ) + circleMap 0 r p.2)
  have hymem (θ : ℝ) : (circleMap 0 r θ).im ∈ Ioo (-ρ) ρ := by
    have hh : |(circleMap 0 r θ).im| ≤ r := by
      simpa only [norm_circleMap_zero, abs_of_pos hr] using abs_im_le_norm (circleMap 0 r θ)
    exact ⟨by linarith [(abs_le.mp hh).1], by linarith [(abs_le.mp hh).2]⟩
  have hc : Continuous F := by
    apply hf.continuousOn.comp_continuous
    · fun_prop
    · intro p
      have h := hymem p.2
      simpa only [add_im, ofReal_im, zero_add, mem_setOf_eq] using
        (show -ρ ≤ (circleMap 0 r p.2).im ∧ (circleMap 0 r p.2).im ≤ ρ from ⟨h.1.le, h.2.le⟩)
  have hsplit (x : ℝ) (w : ℂ) : (x : ℂ) + w = ((x + w.re : ℝ) : ℂ) + w.im * I := by
    rw [ofReal_add, add_assoc, re_add_im]
  have hrow (θ : ℝ) : Integrable (fun x : ℝ => F (x, θ)) ∧
      (∫ x : ℝ, ‖F (x, θ)‖) ≤ M := by
    dsimp [F]
    simp_rw [hsplit (w := circleMap 0 r θ)]
    exact ⟨(hi _ (hymem θ)).comp_add_right _,
      (integral_add_right_eq_self (fun x : ℝ => ‖f ((x : ℂ) + (circleMap 0 r θ).im * I)‖)
        (circleMap 0 r θ).re).le.trans (hm _ (hymem θ))⟩
  have hrowi : Integrable (fun θ : ℝ => ∫ x : ℝ, ‖F (x, θ)‖) ν := by
    apply (show Integrable (fun _ : ℝ => M) ν from continuous_const.integrableOn_Icc).mono'
    · exact hc.norm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
    · exact Eventually.of_forall (fun θ => by
        rw [Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg _))]
        exact (hrow θ).2)
  have hFi : Integrable F (volume.prod ν) :=
    (integrable_prod_iff' hc.aestronglyMeasurable).mpr
      ⟨Eventually.of_forall (fun θ => (hrow θ).1), hrowi⟩
  let q : ℝ × ℝ → ℂ := fun p => I / circleMap 0 r p.2
  have hqc : Continuous q := by
    apply continuous_const.div (by fun_prop)
    intro p
    simpa using (circleMap_ne_center (c := (0 : ℂ)) hr.ne' (θ := p.2))
  have hqi : Integrable (fun p : ℝ × ℝ => q p • F p) (volume.prod ν) := by
    apply hFi.bdd_smul r⁻¹ hqc.aestronglyMeasurable
    exact Eventually.of_forall (fun p => by
      simp [q, norm_circleMap_zero, abs_of_pos hr])
  have hCauchy (x : ℝ) : (∫ θ : ℝ, q (x, θ) • F (x, θ) ∂ν) =
      (2 * Real.pi * I) • deriv f (x : ℂ) := by
    have hdisc : DifferentiableOn ℂ f (closedBall (x : ℂ) r) := by
      apply hf.mono
      intro z hz
      have hn : ‖z - (x : ℂ)‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hz
      have him : |z.im| ≤ r := by
        simpa only [sub_im, ofReal_im, sub_zero] using (abs_im_le_norm (z - (x : ℂ))).trans hn
      exact ⟨by linarith [(abs_le.mp him).1], by linarith [(abs_le.mp him).2]⟩
    rw [← hdisc.deriv_eq_smul_circleIntegral hr, circleIntegral_def_Icc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro θ _
    simp only [q, F, deriv_circleMap, circleMap_sub_center, smul_smul]
    rw [show (x : ℂ) + circleMap 0 r θ = circleMap (x : ℂ) r θ by simp [circleMap]]
    congr 1
    have hw : circleMap 0 r θ ≠ 0 := by
      simpa using (circleMap_ne_center (c := (0 : ℂ)) hr.ne' (θ := θ))
    field_simp
  have hpartial : Integrable (fun x : ℝ => (2 * Real.pi * I) • deriv f (x : ℂ)) :=
    hqi.integral_prod_left.congr (Eventually.of_forall hCauchy)
  exact (integrable_fun_smul_iff two_pi_I_ne_zero _).mp hpartial

omit [CompleteSpace E] in

/-- The derivative of the real-axis restriction equals the complex derivative at each real point
for a function holomorphic on a positive-width strip. -/
theorem real_axis_hasDerivAt (f : ℂ → E) (ρ : ℝ) (hρ : 0 < ρ)
    (hf : DifferentiableOn ℂ f {z : ℂ | -ρ ≤ z.im ∧ z.im ≤ ρ}) (x : ℝ) :
    HasDerivAt (fun t : ℝ => f (t : ℂ)) (deriv f (x : ℂ)) x := by
  have ht : Tendsto Complex.im (𝓝 (x : ℂ)) (𝓝 (0 : ℝ)) := by
    simpa using continuous_im.tendsto (x : ℂ)
  have hd := (hf.differentiableAt (ht (Icc_mem_nhds (by linarith) hρ))).hasDerivAt
  simpa using! hd.scomp x (Complex.ofRealCLM.hasDerivAt (x := x))

/-- Uniformly bounded integrable horizontal slices of a holomorphic strip function imply normal
convergence of its mesh translates on compact sets. -/
theorem normal_convergence_of_strip (f : ℂ → E) (ρ M h : ℝ) (hρ : 0 < ρ) (hh : 0 < h)
    (hf : DifferentiableOn ℂ f {z : ℂ | -ρ ≤ z.im ∧ z.im ≤ ρ})
    (hi : ∀ y ∈ Ioo (-ρ) ρ, Integrable (fun x : ℝ => f ((x : ℂ) + y * I)))
    (hm : ∀ y ∈ Ioo (-ρ) ρ, (∫ x : ℝ, ‖f ((x : ℂ) + y * I)‖) ≤ M) :
    ∀ K : Compacts ℝ, Summable (fun n : ℤ =>
      ⨆ x : K, ‖f ((h * ((x : ℝ) + (n : ℝ)) : ℝ) : ℂ)‖) := by
  have hd (x : ℝ) : HasDerivAt (fun t : ℝ => f ((h * t : ℝ) : ℂ))
      (h • deriv f ((h * x : ℝ) : ℂ)) x := by
    simpa only [Function.comp_def, mul_one] using
      (real_axis_hasDerivAt f ρ hρ hf (h * x)).scomp x ((hasDerivAt_id x).const_mul h)
  let g : C(ℝ, E) := ⟨fun x : ℝ => f ((h * x : ℝ) : ℂ),
    continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)⟩
  have hgi : Integrable (g : ℝ → E) := by
    have hi0 : Integrable (fun x : ℝ => f (x : ℂ)) := by
      simpa using hi 0 ⟨by linarith, hρ⟩
    exact hi0.comp_mul_left' hh.ne'
  have hgd : Integrable (deriv (g : ℝ → E)) := by
    apply (((integrable_complex_deriv f ρ M hρ hf hi hm).comp_mul_left' hh.ne').smul h).congr
    exact Eventually.of_forall (fun x => (hd x).deriv.symm)
  intro K
  convert normal_convergence_of_integrable_deriv g (fun x => (hd x).differentiableAt) hgi hgd K using 1
  funext n
  rw [ContinuousMap.norm_eq_iSup_norm]
  rfl

/-- A holomorphic strip function with uniform decay and bounded integrable interior slices has
mesh error at most `2M / (exp (2πρ / h) - 1)`. -/
theorem strip_mesh_error (f : ℂ → E) (ρ M h : ℝ) (hρ : 0 < ρ) (hh : 0 < h)
    (hf : DifferentiableOn ℂ f {z : ℂ | -ρ ≤ z.im ∧ z.im ≤ ρ})
    (hd : StripContour.UniformDecay f (-ρ) ρ)
    (hi : ∀ y ∈ Ioo (-ρ) ρ, Integrable (fun x : ℝ => f ((x : ℂ) + y * I)))
    (hm : ∀ y ∈ Ioo (-ρ) ρ, (∫ x : ℝ, ‖f ((x : ℂ) + y * I)‖) ≤ M) :
    ‖(∫ x : ℝ, f (x : ℂ)) - h • (∑' n : ℤ, f ((h * (n : ℝ) : ℝ) : ℂ))‖ ≤
      2 * M / (Real.exp (2 * Real.pi * ρ / h) - 1) :=
  PoissonMesh.strip_mesh_error f ρ M h hρ hh hf hd hi hm
    (normal_convergence_of_strip f ρ M h hρ hh hf hi hm)

/-- Analyticity near the closed strip, uniform decay, and bounded integrable interior slices
give mesh error at most `2M / (exp (2πρ / h) - 1)`. -/
theorem analytic_strip_mesh_error (f : ℂ → E) (ρ M h : ℝ) (hρ : 0 < ρ) (hh : 0 < h)
    (hf : AnalyticOnNhd ℂ f {z : ℂ | |z.im| ≤ ρ})
    (hd : StripContour.UniformDecay f (-ρ) ρ)
    (hi : ∀ y ∈ Ioo (-ρ) ρ, Integrable (fun x : ℝ => f ((x : ℂ) + y * I)))
    (hm : ∀ y ∈ Ioo (-ρ) ρ, (∫ x : ℝ, ‖f ((x : ℂ) + y * I)‖) ≤ M) :
    ‖(∫ x : ℝ, f (x : ℂ)) - h • (∑' n : ℤ, f ((h * (n : ℝ) : ℝ) : ℂ))‖ ≤
      2 * M / (Real.exp (2 * Real.pi * ρ / h) - 1) :=
  strip_mesh_error f ρ M h hρ hh (by simpa only [abs_le] using hf.differentiableOn) hd hi hm

/-- Analyticity near the closed strip, uniform decay with respect to the complex norm, and
bounded integrable interior slices give the exponential mesh error bound of [Aftab et al.,
Lemma 4.13][AftabAnTrivisa2026]. -/
theorem analytic_strip_mesh_error_of_norm_decay (f : ℂ → E) (ρ M h : ℝ)
    (hρ : 0 < ρ) (hh : 0 < h)
    (hf : AnalyticOnNhd ℂ f {z : ℂ | |z.im| ≤ ρ})
    (hd : ∀ ε > 0, ∃ R : ℝ, ∀ z : ℂ, |z.im| ≤ ρ → R ≤ ‖z‖ → ‖f z‖ ≤ ε)
    (hi : ∀ y ∈ Ioo (-ρ) ρ, Integrable (fun x : ℝ => f ((x : ℂ) + y * I)))
    (hm : ∀ y ∈ Ioo (-ρ) ρ, (∫ x : ℝ, ‖f ((x : ℂ) + y * I)‖) ≤ M) :
    ‖(∫ x : ℝ, f (x : ℂ)) - h • (∑' n : ℤ, f ((h * (n : ℝ) : ℝ) : ℂ))‖ ≤
      2 * M / (Real.exp (2 * Real.pi * ρ / h) - 1) := by
  apply analytic_strip_mesh_error f ρ M h hρ hh hf _ hi hm
  intro ε hε
  obtain ⟨R, hR⟩ := hd ε hε
  refine ⟨R, fun x hx y hy => hR ((x : ℂ) + y * I) ?_ (hx.trans ?_)⟩
  · simpa using abs_le.mpr hy
  · simpa using abs_re_le_norm ((x : ℂ) + y * I)

end Complex

end Qatlib.Papers.CommutLCHS26.MainResults.StripSampling
