/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.RestartLaw.Section3OptimalAngleSubgoalTigh
import Qatlib.Concepts.SearchStopping.RestartLaw.Section3OptimalConstantsSubgoalTigh
import Qatlib.Concepts.SearchStopping.RestartLaw.Section3RestartStationaritySubgoalTigh
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Sparse-limit asymptotics for search restarts

This module constructs stationary restart roots near a specified solution of tan(z/2) = z and
transports their limits to success probabilities and restart-cost coefficients. It also relates
the small-angle and sparse-density scalings and proves eventual coefficient bounds between 0.87
and 0.88 times π/4.

The source paper is [BoyerEtAl1998].

## Main statements

* `exists_stationary_root_close`: For a root z₀ of tan(z₀/2) = z₀ in the stated rational
  interval and 0 < θ < 1/10, there is a root of tan(z/2 + θ) = z strictly between z₀ − 4θ and
  z₀.
* `sparseScaledExpected_tendsto`: Under the interval and root-family convergence hypotheses, the
  restart coefficient transported by θ = arcsin(√x) and multiplied by √x/arcsin(√x) tends to
  z₀/(4 sin²(z₀/2)) as x decreases to zero.
* `exists_root_family_scaled_window`: For a root z₀ in the stated rational interval, there
  exists a family of stationary roots for 0 < θ < 1/10 converging to z₀ whose scaled
  coefficients eventually lie between 0.87(π/4) and 0.88(π/4).

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option autoImplicit false
open scoped Topology
open Filter

namespace Qatlib.Papers.QSearchBoyer98.MainResults

open Qatlib.Concepts.SearchStopping.RestartLaw

noncomputable section

/-- For 1.06 < a ≤ π, cos a < 1/2. -/
private theorem cos_lt_half_of_ge {a : ℝ} (ha : (1.06 : ℝ) < a) (haπ : a ≤ Real.pi) :
    Real.cos a < 1 / 2 := by
  have h1 : Real.cos a < Real.cos (1.06 : ℝ) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num) haπ ha
  have h2 : Real.cos (1.06 : ℝ) ≤ 1 / 2 := by
    have hπ : Real.pi / 3 ≤ 1.06 := by linarith [Real.pi_lt_d2]
    have hle := Real.cos_le_cos_of_nonneg_of_le_pi (x := Real.pi / 3) (y := 1.06)
      (by positivity) (by linarith [Real.pi_lt_d2]) hπ
    rwa [Real.cos_pi_div_three] at hle
  linarith

/-- For a root z₀ of tan(z₀/2) = z₀ in the stated rational interval and 0 < θ < 1/10, there is a
root of tan(z/2 + θ) = z strictly between z₀ − 4θ and z₀ [BoyerEtAl1998]. -/
theorem exists_stationary_root_close {z₀ : ℝ}
    (hz₀ : Real.tan (z₀ / 2) = z₀)
    (hlo : 233112 / 100000 < z₀) (hhi : z₀ < 233113 / 100000) :
    ∀ θ : ℝ, 0 < θ → θ < 1 / 10 →
      ∃ z : ℝ, z₀ - 4 * θ < z ∧ z < z₀ ∧ Real.tan (z / 2 + θ) = z := by
  intro θ hθ hθ10
  have hz1 : (2.33112 : ℝ) < z₀ := by norm_num at hlo ⊢; linarith
  have hz2 : z₀ < (2.33113 : ℝ) := by norm_num at hhi ⊢; linarith
  have hz0pos : 0 < z₀ := by linarith
  have hhalf_lt : z₀ / 2 + θ < Real.pi / 2 := by
    have hπ : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
    nlinarith
  have hlower_pos : 0 < z₀ / 2 - θ := by linarith

  have hgz0 : 0 < Real.tan (z₀ / 2 + θ) - z₀ := by
    have hlt : Real.tan (z₀ / 2) < Real.tan (z₀ / 2 + θ) :=
      Real.tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith [Real.pi_pos]) hhalf_lt
        (by linarith)
    rw [hz₀] at hlt
    linarith

  have hga : Real.tan ((z₀ - 4 * θ) / 2 + θ) - (z₀ - 4 * θ) < 0 := by
    have hdrop : Real.tan (z₀ / 2 - θ) < z₀ - 4 * θ := by
      have hdiff : DifferentiableOn ℝ Real.tan (Set.Ioo (z₀ / 2 - θ) (z₀ / 2)) := by
        intro x hx
        have hcos : Real.cos x ≠ 0 :=
          (Real.cos_pos_of_mem_Ioo
            ⟨by linarith [hx.1, hlower_pos], by linarith [hx.2, hhalf_lt]⟩).ne'
        exact (Real.hasDerivAt_tan hcos).differentiableAt.differentiableWithinAt
      have hcont : ContinuousOn Real.tan (Set.Icc (z₀ / 2 - θ) (z₀ / 2)) := by
        apply Real.continuousOn_tan_Ioo.mono
        intro x hx
        exact ⟨by linarith [hx.1, hlower_pos], by linarith [hx.2, hhalf_lt]⟩
      obtain ⟨c, hc, hcder⟩ :=
        exists_deriv_eq_slope Real.tan (by linarith : z₀ / 2 - θ < z₀ / 2) hcont hdiff
      have hcpos : 0 < Real.cos c :=
        Real.cos_pos_of_mem_Ioo
          ⟨by linarith [hc.1, hlower_pos], by linarith [hc.2, hhalf_lt]⟩
      have hcc : Real.cos c < 1 / 2 :=
        cos_lt_half_of_ge (by linarith [hc.1, hz1])
          (by linarith [hc.2, hz2, Real.pi_lt_d2])
      have hcos2 : Real.cos c ^ 2 < 1 / 4 := by
        have h1 : 0 < 1 / 2 - Real.cos c := by linarith
        have h2 : 0 < 1 / 2 + Real.cos c := by linarith
        nlinarith [mul_pos h1 h2]
      have hgt4 : 4 < 1 / Real.cos c ^ 2 := by
        rw [lt_div_iff₀ (by positivity : (0 : ℝ) < Real.cos c ^ 2)]
        nlinarith
      rw [Real.deriv_tan] at hcder
      have hden : z₀ / 2 - (z₀ / 2 - θ) = θ := by ring
      rw [hden] at hcder
      rw [hcder] at hgt4
      rw [hz₀] at hgt4
      have h4θ : 4 * θ < z₀ - Real.tan (z₀ / 2 - θ) := by
        have := (lt_div_iff₀ hθ).mp hgt4
        linarith
      linarith
    have harg : (z₀ - 4 * θ) / 2 + θ = z₀ / 2 - θ := by ring
    rw [harg]
    linarith

  have hgcont : ContinuousOn (fun z : ℝ => Real.tan (z / 2 + θ) - z)
      (Set.Icc (z₀ - 4 * θ) z₀) := by
    have haff : Set.MapsTo (fun z : ℝ => z / 2 + θ) (Set.Icc (z₀ - 4 * θ) z₀)
        (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
      intro z hz
      exact ⟨by linarith [hz.1, hlower_pos, Real.pi_pos],
        by linarith [hz.2, hhalf_lt]⟩
    have hcont : ContinuousOn (fun z : ℝ => z / 2 + θ) (Set.Icc (z₀ - 4 * θ) z₀) := by
      fun_prop
    have htan : ContinuousOn (Real.tan ∘ (fun z : ℝ => z / 2 + θ))
        (Set.Icc (z₀ - 4 * θ) z₀) :=
      Real.continuousOn_tan_Ioo.comp hcont haff
    simpa [Function.comp_def] using! htan.sub continuousOn_id
  obtain ⟨z, hz, hgz⟩ := intermediate_value_Ioo (by linarith : z₀ - 4 * θ ≤ z₀) hgcont
    (show (0 : ℝ) ∈ Set.Ioo (Real.tan ((z₀ - 4 * θ) / 2 + θ) - (z₀ - 4 * θ))
        (Real.tan (z₀ / 2 + θ) - z₀) from ⟨hga, hgz0⟩)
  exact ⟨z, hz.1, hz.2, by linarith [hgz]⟩

/-- Any family lying strictly between z₀ − 4θ and z₀ for sufficiently small positive θ converges
to z₀ as θ decreases to zero [BoyerEtAl1998]. -/
theorem stationaryRoot_tendsto {z : ℝ → ℝ} {z₀ : ℝ}
    (hloc : ∀ θ : ℝ, 0 < θ → θ < 1 / 10 →
      z₀ - 4 * θ < z θ ∧ z θ < z₀) :
    Tendsto z (𝓝[>] (0 : ℝ)) (𝓝 z₀) := by
  have hid : Tendsto (fun θ : ℝ => θ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have hconst : Tendsto (fun _ : ℝ => z₀) (𝓝[>] (0 : ℝ)) (𝓝 z₀) := tendsto_const_nhds
  have hlow : Tendsto (fun θ : ℝ => z₀ - 4 * θ) (𝓝[>] (0 : ℝ)) (𝓝 z₀) := by
    simpa using! hconst.sub (hid.const_mul 4)
  have hsmall : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ < 1 / 10 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (gt_mem_nhds (show (0 : ℝ) < 1 / 10 by norm_num))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hconst ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, hsmall] with θ hθ hθ10
    exact (hloc θ hθ hθ10).1.le
  · filter_upwards [self_mem_nhdsWithin, hsmall] with θ hθ hθ10
    exact (hloc θ hθ hθ10).2.le

/-- If z(θ) tends to z₀ as θ decreases to zero, sin²(z(θ)/2 + θ) tends to sin²(z₀/2). -/
theorem restartSuccess_tendsto {z : ℝ → ℝ} {z₀ : ℝ}
    (hzt : Tendsto z (𝓝[>] (0 : ℝ)) (𝓝 z₀)) :
    Tendsto (fun θ : ℝ => Real.sin (z θ / 2 + θ) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sin (z₀ / 2) ^ 2)) := by
  have hid : Tendsto (fun θ : ℝ => θ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have harg : Tendsto (fun θ : ℝ => z θ / 2 + θ) (𝓝[>] (0 : ℝ)) (𝓝 (z₀ / 2 + 0)) :=
    (hzt.div_const 2).add hid
  have hsin : Tendsto (fun θ : ℝ => Real.sin (z θ / 2 + θ))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sin (z₀ / 2))) := by
    simpa using! (Real.continuous_sin.continuousAt.tendsto.comp harg)
  simpa [Pi.pow_apply] using! hsin.pow 2

/-- For z₀ in the stated rational interval and the stated convergence hypotheses, z(θ)/(4
sin²(z(θ)/2 + θ)) tends to z₀/(4 sin²(z₀/2)). -/
theorem restartCoefficient_tendsto {z : ℝ → ℝ} {z₀ : ℝ}
    (hlo : 233112 / 100000 < z₀) (hhi : z₀ < 233113 / 100000)
    (hzt : Tendsto z (𝓝[>] (0 : ℝ)) (𝓝 z₀))
    (hsucc : Tendsto (fun θ : ℝ => Real.sin (z θ / 2 + θ) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sin (z₀ / 2) ^ 2))) :
    Tendsto (fun θ : ℝ => z θ / (4 * Real.sin (z θ / 2 + θ) ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (z₀ / (4 * Real.sin (z₀ / 2) ^ 2))) := by
  have hz0 : (2.33 : ℝ) < z₀ := by norm_num at hlo ⊢; linarith
  have hzup : z₀ < (2.33113 : ℝ) := by norm_num at hhi ⊢; linarith
  have hsin_pos : 0 < Real.sin (z₀ / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith [Real.pi_gt_d2]
  have hden : Tendsto (fun θ : ℝ => 4 * Real.sin (z θ / 2 + θ) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (4 * Real.sin (z₀ / 2) ^ 2)) := by
    simpa using! hsucc.const_mul 4
  have hne : (4 * Real.sin (z₀ / 2) ^ 2) ≠ 0 := by
    have : 0 < 4 * Real.sin (z₀ / 2) ^ 2 := by nlinarith [hsin_pos]
    exact this.ne'
  exact hzt.div hden hne

/-- Under the root, interval, and convergence hypotheses, the scaled restart coefficient
eventually lies strictly between 0.87(π/4) and 0.88(π/4) as θ decreases to zero
[BoyerEtAl1998]. -/
theorem restart_scaled_window {z : ℝ → ℝ} {z₀ : ℝ}
    (hz₀ : Real.tan (z₀ / 2) = z₀)
    (hlo : 233112 / 100000 < z₀) (hhi : z₀ < 233113 / 100000)
    (hzt : Tendsto z (𝓝[>] (0 : ℝ)) (𝓝 z₀))
    (hsucc : Tendsto (fun θ : ℝ => Real.sin (z θ / 2 + θ) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sin (z₀ / 2) ^ 2))) :
    ∀ᶠ θ in 𝓝[>] (0 : ℝ),
      87 / 100 * (Real.pi / 4) < z θ / (4 * Real.sin (z θ / 2 + θ) ^ 2) ∧
        z θ / (4 * Real.sin (z θ / 2 + θ) ^ 2) < 22 / 25 * (Real.pi / 4) := by
  have hcoef := restartCoefficient_tendsto hlo hhi hzt hsucc
  have hconst := section3OptimalConstantsSubgoal z₀ hz₀ hlo hhi
  have hlow : 87 / 100 * (Real.pi / 4) < z₀ / (4 * Real.sin (z₀ / 2) ^ 2) :=
    hconst.2.2.2.2.2.2.1
  have hhigh : z₀ / (4 * Real.sin (z₀ / 2) ^ 2) < 22 / 25 * (Real.pi / 4) :=
    hconst.2.2.2.2.2.2.2
  have e1 : ∀ᶠ θ in 𝓝[>] (0 : ℝ),
      87 / 100 * (Real.pi / 4) < z θ / (4 * Real.sin (z θ / 2 + θ) ^ 2) :=
    (tendsto_order.1 hcoef).1 _ hlow
  have e2 : ∀ᶠ θ in 𝓝[>] (0 : ℝ),
      z θ / (4 * Real.sin (z θ / 2 + θ) ^ 2) < 22 / 25 * (Real.pi / 4) :=
    (tendsto_order.1 hcoef).2 _ hhigh
  filter_upwards [e1, e2] with θ h1 h2
  exact ⟨h1, h2⟩

/-- Under the interval and convergence hypotheses, (z(θ)/4 + θ)/sin²(z(θ)/2 + θ) tends to z₀/(4
sin²(z₀/2)) as θ decreases to zero [BoyerEtAl1998]. -/
theorem actualPaidCoefficient_tendsto {z : ℝ → ℝ} {z₀ : ℝ}
    (hlo : 233112 / 100000 < z₀) (hhi : z₀ < 233113 / 100000)
    (hzt : Tendsto z (𝓝[>] (0 : ℝ)) (𝓝 z₀))
    (hsucc : Tendsto (fun θ : ℝ => Real.sin (z θ / 2 + θ) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sin (z₀ / 2) ^ 2))) :
    Tendsto (fun θ : ℝ => (z θ / 4 + θ) / Real.sin (z θ / 2 + θ) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (z₀ / (4 * Real.sin (z₀ / 2) ^ 2))) := by
  have hz0 : (2.33 : ℝ) < z₀ := by norm_num at hlo ⊢; linarith
  have hzup : z₀ < (2.33113 : ℝ) := by norm_num at hhi ⊢; linarith
  have hsin_pos : 0 < Real.sin (z₀ / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith [Real.pi_gt_d2]
  have hid : Tendsto (fun θ : ℝ => θ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have hnum : Tendsto (fun θ : ℝ => z θ / 4 + θ) (𝓝[>] (0 : ℝ)) (𝓝 (z₀ / 4)) := by
    have := (hzt.div_const 4).add hid
    simpa using! this
  have hden : Tendsto (fun θ : ℝ => Real.sin (z θ / 2 + θ) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sin (z₀ / 2) ^ 2)) := hsucc
  have hne : Real.sin (z₀ / 2) ^ 2 ≠ 0 := by
    have : 0 < Real.sin (z₀ / 2) ^ 2 := by nlinarith [hsin_pos]
    exact this.ne'
  have hq := hnum.div hden hne
  have hval : (z₀ / 4) / Real.sin (z₀ / 2) ^ 2 = z₀ / (4 * Real.sin (z₀ / 2) ^ 2) := by
    field_simp
  rwa [hval] at hq

/-- For nonzero θ, multiplying the restart expectation at iteration parameter z/(4θ) by θ gives
z/(4 sin²(z/2 + θ)) [BoyerEtAl1998]. -/
theorem theta_mul_restartExpected_scaled (θ z : ℝ) (hθ : θ ≠ 0) :
    θ * restartExpectedIterations θ (z / (4 * θ)) =
      z / (4 * Real.sin (z / 2 + θ) ^ 2) := by
  have harg : (2 * (z / (4 * θ)) + 1) * θ = z / 2 + θ := by
    field_simp
    ring
  unfold restartExpectedIterations
  rw [harg]
  field_simp [hθ]

/-- The ratio arcsin t/t tends to one as t decreases to zero through positive values. -/
theorem tendsto_arcsin_div_self :
    Tendsto (fun t : ℝ => Real.arcsin t / t) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have h := (Real.hasDerivAt_arcsin (x := 0) (by norm_num) (by norm_num)).tendsto_slope_zero_right
  have hlim : (1 / Real.sqrt (1 - (0 : ℝ) ^ 2)) = 1 := by norm_num
  rw [hlim] at h
  simpa [Real.arcsin_zero, div_eq_inv_mul] using! h

/-- The function arcsin(√x) tends to zero through positive values as x decreases to zero through
positive values. -/
theorem tendsto_arcsin_sqrt :
    Tendsto (fun x : ℝ => Real.arcsin (Real.sqrt x)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have hs : Tendsto (fun x : ℝ => Real.sqrt x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using! (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa [Real.arcsin_zero] using! (Real.continuous_arcsin.tendsto 0).comp hs
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact Real.arcsin_pos.mpr (Real.sqrt_pos.mpr hx)

/-- The ratio √x/arcsin(√x) tends to one as x decreases to zero through positive values. -/
theorem tendsto_sqrt_div_arcsin_sqrt :
    Tendsto (fun x : ℝ => Real.sqrt x / Real.arcsin (Real.sqrt x)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hs : Tendsto (fun x : ℝ => Real.sqrt x) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · simpa using! (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact Real.sqrt_pos.mpr hx
  have hdiv : Tendsto (fun x : ℝ => Real.arcsin (Real.sqrt x) / Real.sqrt x)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := tendsto_arcsin_div_self.comp hs
  simpa [inv_div] using! hdiv.inv₀ (by norm_num : (1 : ℝ) ≠ 0)

/-- Under the interval and root-family convergence hypotheses, the restart coefficient
transported by θ = arcsin(√x) and multiplied by √x/arcsin(√x) tends to z₀/(4 sin²(z₀/2)) as
x decreases to zero [BoyerEtAl1998]. -/
theorem sparseScaledExpected_tendsto {z : ℝ → ℝ} {z₀ : ℝ}
    (hlo : 233112 / 100000 < z₀)
    (hhi : z₀ < 233113 / 100000)
    (hzt : Tendsto z (𝓝[>] (0 : ℝ)) (𝓝 z₀))
    (hsucc : Tendsto (fun θ : ℝ => Real.sin (z θ / 2 + θ) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.sin (z₀ / 2) ^ 2))) :
    Tendsto (fun x : ℝ =>
        Real.sqrt x / Real.arcsin (Real.sqrt x) *
          (z (Real.arcsin (Real.sqrt x)) /
            (4 * Real.sin (z (Real.arcsin (Real.sqrt x)) / 2 +
              Real.arcsin (Real.sqrt x)) ^ 2)))
      (𝓝[>] (0 : ℝ)) (𝓝 (z₀ / (4 * Real.sin (z₀ / 2) ^ 2))) := by
  have hcoef : Tendsto (fun x : ℝ =>
        z (Real.arcsin (Real.sqrt x)) /
          (4 * Real.sin (z (Real.arcsin (Real.sqrt x)) / 2 +
            Real.arcsin (Real.sqrt x)) ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (z₀ / (4 * Real.sin (z₀ / 2) ^ 2))) :=
    (restartCoefficient_tendsto hlo hhi hzt hsucc).comp tendsto_arcsin_sqrt
  have h := tendsto_sqrt_div_arcsin_sqrt.mul hcoef
  simpa using! h

/-- For a root z₀ in the stated rational interval, there exists a family of stationary roots for
0 < θ < 1/10 converging to z₀ whose scaled coefficients eventually lie between 0.87(π/4) and
0.88(π/4) [BoyerEtAl1998]. -/
theorem exists_root_family_scaled_window {z₀ : ℝ}
    (hz₀ : Real.tan (z₀ / 2) = z₀)
    (hlo : 233112 / 100000 < z₀) (hhi : z₀ < 233113 / 100000) :
    ∃ zstar : ℝ → ℝ,
      (∀ θ : ℝ, 0 < θ → θ < 1 / 10 → Real.tan (zstar θ / 2 + θ) = zstar θ) ∧
      Tendsto zstar (𝓝[>] (0 : ℝ)) (𝓝 z₀) ∧
      ∀ᶠ θ in 𝓝[>] (0 : ℝ),
        87 / 100 * (Real.pi / 4) < zstar θ / (4 * Real.sin (zstar θ / 2 + θ) ^ 2) ∧
          zstar θ / (4 * Real.sin (zstar θ / 2 + θ) ^ 2) < 22 / 25 * (Real.pi / 4) := by
  have hex : ∀ θ : ℝ, ∃ z : ℝ,
      (0 < θ ∧ θ < 1 / 10) → (z₀ - 4 * θ < z ∧ z < z₀ ∧ Real.tan (z / 2 + θ) = z) := by
    intro θ
    by_cases h : 0 < θ ∧ θ < 1 / 10
    · obtain ⟨z, h1, h2, h3⟩ := exists_stationary_root_close hz₀ hlo hhi θ h.1 h.2
      exact ⟨z, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨z₀, fun hh => absurd hh h⟩
  let zstar : ℝ → ℝ := fun θ => Classical.choose (hex θ)
  have hspec : ∀ θ : ℝ, (0 < θ ∧ θ < 1 / 10) →
      z₀ - 4 * θ < zstar θ ∧ zstar θ < z₀ ∧ Real.tan (zstar θ / 2 + θ) = zstar θ := by
    intro θ h
    exact Classical.choose_spec (hex θ) h
  have hloc : ∀ θ : ℝ, 0 < θ → θ < 1 / 10 → z₀ - 4 * θ < zstar θ ∧ zstar θ < z₀ := by
    intro θ hθ hθ10
    exact ⟨(hspec θ ⟨hθ, hθ10⟩).1, (hspec θ ⟨hθ, hθ10⟩).2.1⟩
  have htan : ∀ θ : ℝ, 0 < θ → θ < 1 / 10 → Real.tan (zstar θ / 2 + θ) = zstar θ := by
    intro θ hθ hθ10
    exact (hspec θ ⟨hθ, hθ10⟩).2.2
  have hzt : Tendsto zstar (𝓝[>] (0 : ℝ)) (𝓝 z₀) := stationaryRoot_tendsto hloc
  have hsucc := restartSuccess_tendsto hzt
  exact ⟨zstar, htan, hzt, restart_scaled_window hz₀ hlo hhi hzt hsucc⟩

end

end Qatlib.Papers.QSearchBoyer98.MainResults
