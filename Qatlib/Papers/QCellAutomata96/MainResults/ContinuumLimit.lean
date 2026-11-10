/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QCellAutomata96.MainResults.ConfluentSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Complex Filter
open scoped Topology

namespace Qatlib.Papers.QCellAutomata96.MainResults

theorem continuousOn_zeroFone1 (R : ℝ) (hR : 0 ≤ R) :
    ContinuousOn zeroFone1 (Metric.closedBall (0 : ℂ) R) := by
  have hu : Summable (fun n : ℕ =>
      R ^ n / ((Nat.factorial n : ℝ) * (Nat.factorial n : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      (Real.summable_pow_div_factorial R)
    · positivity
    · have hfac : (1 : ℝ) ≤ (Nat.factorial n : ℝ) := by
        exact_mod_cast Nat.factorial_pos n
      have hpos : (0 : ℝ) < (Nat.factorial n : ℝ) := by positivity
      have hmul : (Nat.factorial n : ℝ) * 1 ≤
          (Nat.factorial n : ℝ) * (Nat.factorial n : ℝ) :=
        mul_le_mul_of_nonneg_left hfac (le_of_lt hpos)
      calc R ^ n / ((Nat.factorial n : ℝ) * (Nat.factorial n : ℝ))
          ≤ R ^ n / (Nat.factorial n : ℝ) := by
            apply div_le_div_of_nonneg_left (pow_nonneg hR n) hpos
            simpa using hmul
        _ = R ^ n / (Nat.factorial n : ℝ) := rfl
  refine continuousOn_tsum (fun n => ?_) hu (fun n z hz => ?_)
  · exact (continuous_pow n).continuousOn.div_const _
  · have hzn : ‖z‖ ≤ R := by simpa using hz
    simp only [norm_div, norm_pow, norm_mul, Complex.norm_natCast]
    apply div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg z) hzn n)
    positivity

theorem continuousAt_zeroFone1 (z : ℂ) : ContinuousAt zeroFone1 z := by
  have hzmem : z ∈ Metric.ball (0 : ℂ) (‖z‖ + 1) := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hball : Metric.ball (0 : ℂ) (‖z‖ + 1) ∈ 𝓝 z :=
    Metric.isOpen_ball.mem_nhds hzmem
  have hclosed : Metric.closedBall (0 : ℂ) (‖z‖ + 1) ∈ 𝓝 z :=
    mem_of_superset hball Metric.ball_subset_closedBall
  exact (continuousOn_zeroFone1 (‖z‖ + 1) (by positivity)).continuousAt hclosed

theorem continuousOn_zeroFone2 (R : ℝ) (hR : 0 ≤ R) :
    ContinuousOn zeroFone2 (Metric.closedBall (0 : ℂ) R) := by
  have hu : Summable (fun n : ℕ =>
      R ^ n / ((Nat.factorial n : ℝ) * (Nat.factorial n : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      (Real.summable_pow_div_factorial R)
    · positivity
    · have hfac : (1 : ℝ) ≤ (Nat.factorial n : ℝ) := by
        exact_mod_cast Nat.factorial_pos n
      have hpos : (0 : ℝ) < (Nat.factorial n : ℝ) := by positivity
      have hmul : (Nat.factorial n : ℝ) * 1 ≤
          (Nat.factorial n : ℝ) * (Nat.factorial n : ℝ) :=
        mul_le_mul_of_nonneg_left hfac (le_of_lt hpos)
      calc R ^ n / ((Nat.factorial n : ℝ) * (Nat.factorial n : ℝ))
          ≤ R ^ n / (Nat.factorial n : ℝ) := by
            apply div_le_div_of_nonneg_left (pow_nonneg hR n) hpos
            simpa using hmul
        _ = R ^ n / (Nat.factorial n : ℝ) := rfl
  refine continuousOn_tsum (fun n => ?_) hu (fun n z hz => ?_)
  · exact (continuous_pow n).continuousOn.div_const _
  · have hzn : ‖z‖ ≤ R := by simpa using hz
    rw [norm_div, norm_pow, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    calc ‖z‖ ^ n /
          ((Nat.factorial (n + 1) : ℝ) * (Nat.factorial n : ℝ))
        ≤ R ^ n / ((Nat.factorial (n + 1) : ℝ) * (Nat.factorial n : ℝ)) := by
          apply div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg z) hzn n)
          positivity
      _ ≤ R ^ n / ((Nat.factorial n : ℝ) * (Nat.factorial n : ℝ)) := by
          apply div_le_div_of_nonneg_left (pow_nonneg hR n) (by positivity)
          have hfac : (Nat.factorial n : ℝ) ≤ (Nat.factorial (n + 1) : ℝ) := by
            exact_mod_cast Nat.factorial_le (Nat.le_succ n)
          have hpos : (0 : ℝ) < (Nat.factorial n : ℝ) := by positivity
          nlinarith [hfac, hpos]

theorem continuousAt_zeroFone2 (z : ℂ) : ContinuousAt zeroFone2 z := by
  have hzmem : z ∈ Metric.ball (0 : ℂ) (‖z‖ + 1) := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hball : Metric.ball (0 : ℂ) (‖z‖ + 1) ∈ 𝓝 z :=
    Metric.isOpen_ball.mem_nhds hzmem
  have hclosed : Metric.closedBall (0 : ℂ) (‖z‖ + 1) ∈ 𝓝 z :=
    mem_of_superset hball Metric.ball_subset_closedBall
  exact (continuousOn_zeroFone2 (‖z‖ + 1) (by positivity)).continuousAt hclosed

theorem tendsto_tan_mul_div (θ : ℝ) :
    Tendsto (fun ε : ℝ => Real.tan (ε * θ) / ε) (𝓝[≠] 0) (𝓝 θ) := by
  have hderiv : HasDerivAt (fun ε : ℝ => Real.tan (ε * θ)) θ 0 := by
    have h1 : HasDerivAt (fun ε : ℝ => ε * θ) θ 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const θ
    have h2 : HasDerivAt Real.tan 1 0 := by
      have := Real.hasDerivAt_tan (x := 0) (by simp)
      simpa using this
    have h2' : HasDerivAt Real.tan 1 (0 * θ) := by simpa using h2
    have h3 : HasDerivAt (Real.tan ∘ fun ε : ℝ => ε * θ) (1 * θ) 0 := h2'.comp 0 h1
    simpa using! h3
  have := hderiv.tendsto_slope_zero
  simpa [div_eq_inv_mul, mul_comm] using this

def confArg (θ u v ε : ℝ) : ℝ := -((u * v) * (Real.tan (ε * θ) / ε) ^ 2)

theorem confArg_eq (θ u v ε : ℝ) (hε : ε ≠ 0) :
    -((u * v) / ε ^ 2 * Real.tan (ε * θ) ^ 2) = confArg θ u v ε := by
  unfold confArg
  field_simp

theorem tendsto_confArg (θ u v : ℝ) :
    Tendsto (fun ε : ℝ => confArg θ u v ε) (𝓝[≠] 0) (𝓝 (-((u * v) * θ ^ 2))) := by
  have h := tendsto_tan_mul_div θ
  have hsq : Tendsto (fun ε : ℝ => (Real.tan (ε * θ) / ε) ^ 2) (𝓝[≠] 0) (𝓝 (θ ^ 2)) := by
    have := h.mul h
    simpa [pow_two] using this
  have := (hsq.const_mul (u * v)).neg
  simpa [confArg] using this

theorem confluentOddAmp_div (θ u v ε : ℝ) (hε : ε ≠ 0) :
    confluentOddAmp θ u v ε / ε =
      (I * Complex.ofReal (Real.tan (ε * θ) / ε)) *
        zeroFone1 (Complex.ofReal (-((u * v) / ε ^ 2 * Real.tan (ε * θ) ^ 2))) := by
  have hεC : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  unfold confluentOddAmp
  rw [Complex.ofReal_div]
  field_simp [hεC]

theorem confluentEvenAmp_div (θ u v ε : ℝ) (hε : ε ≠ 0) :
    confluentEvenAmp θ u v ε / ε =
      (-(Complex.ofReal (u * (Real.tan (ε * θ) / ε) ^ 2))) *
        zeroFone2 (Complex.ofReal (-((u * v) / ε ^ 2 * Real.tan (ε * θ) ^ 2))) := by
  have hεC : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  unfold confluentEvenAmp
  push_cast
  field_simp [hεC]

theorem tendsto_confluentOddAmp_scaled (θ u v : ℝ) :
    Tendsto (fun ε : ℝ => confluentOddAmp θ u v ε / ε) (𝓝[≠] 0)
      (𝓝 (I * (θ : ℂ) * zeroFone1 (Complex.ofReal (-((u * v) * θ ^ 2))))) := by
  have hg : Tendsto (fun ε : ℝ => Complex.ofReal (Real.tan (ε * θ) / ε))
      (𝓝[≠] 0) (𝓝 (θ : ℂ)) := by
    have := (Complex.continuous_ofReal.tendsto (θ : ℝ)).comp (tendsto_tan_mul_div θ)
    simpa [Function.comp_def, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_tan] using this
  have harg : Tendsto
      (fun ε : ℝ => Complex.ofReal (-((u * v) / ε ^ 2 * Real.tan (ε * θ) ^ 2)))
      (𝓝[≠] 0) (𝓝 (Complex.ofReal (-((u * v) * θ ^ 2)))) := by
    have := (Complex.continuous_ofReal.tendsto (-((u * v) * θ ^ 2))).comp
      (tendsto_confArg θ u v)
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    show (Complex.ofReal ∘ fun ε => confArg θ u v ε) ε =
      Complex.ofReal (-((u * v) / ε ^ 2 * Real.tan (ε * θ) ^ 2))
    simp only [Function.comp_apply]
    rw [confArg_eq θ u v ε (by simpa using hε)]
  have hz : Tendsto (fun z : ℂ => zeroFone1 z)
      (𝓝 (Complex.ofReal (-((u * v) * θ ^ 2))))
      (𝓝 (zeroFone1 (Complex.ofReal (-((u * v) * θ ^ 2))))) :=
    (continuousAt_zeroFone1 _).tendsto
  have hprod : Tendsto
      (fun ε : ℝ => (I * Complex.ofReal (Real.tan (ε * θ) / ε)) *
        zeroFone1 (Complex.ofReal (-((u * v) / ε ^ 2 * Real.tan (ε * θ) ^ 2))))
      (𝓝[≠] 0)
      (𝓝 (I * (θ : ℂ) * zeroFone1 (Complex.ofReal (-((u * v) * θ ^ 2))))) := by
    have hI : Tendsto (fun ε : ℝ => (I : ℂ) * Complex.ofReal (Real.tan (ε * θ) / ε))
        (𝓝[≠] 0) (𝓝 (I * (θ : ℂ))) := tendsto_const_nhds.mul hg
    have := hI.mul (hz.comp harg)
    simpa [mul_assoc] using this
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (confluentOddAmp_div θ u v ε hε).symm

theorem tendsto_confluentEvenAmp_scaled (θ u v : ℝ) :
    Tendsto (fun ε : ℝ => confluentEvenAmp θ u v ε / ε) (𝓝[≠] 0)
      (𝓝 (-((u : ℂ) * (θ : ℂ) ^ 2) *
        zeroFone2 (Complex.ofReal (-((u * v) * θ ^ 2))))) := by
  have hsq : Tendsto (fun ε : ℝ => (Real.tan (ε * θ) / ε) ^ 2) (𝓝[≠] 0) (𝓝 (θ ^ 2)) := by
    have := (tendsto_tan_mul_div θ).mul (tendsto_tan_mul_div θ)
    simpa [pow_two] using this
  have hcoefR : Tendsto (fun ε : ℝ => u * (Real.tan (ε * θ) / ε) ^ 2)
      (𝓝[≠] 0) (𝓝 (u * θ ^ 2)) := hsq.const_mul u
  have hcoef : Tendsto (fun ε : ℝ => -Complex.ofReal (u * (Real.tan (ε * θ) / ε) ^ 2))
      (𝓝[≠] 0) (𝓝 (-((u : ℂ) * (θ : ℂ) ^ 2))) := by
    have := ((Complex.continuous_ofReal.tendsto (u * θ ^ 2)).comp hcoefR).neg
    simpa using this
  have harg : Tendsto
      (fun ε : ℝ => Complex.ofReal (-((u * v) / ε ^ 2 * Real.tan (ε * θ) ^ 2)))
      (𝓝[≠] 0) (𝓝 (Complex.ofReal (-((u * v) * θ ^ 2)))) := by
    have := (Complex.continuous_ofReal.tendsto (-((u * v) * θ ^ 2))).comp
      (tendsto_confArg θ u v)
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    show (Complex.ofReal ∘ fun ε => confArg θ u v ε) ε =
      Complex.ofReal (-((u * v) / ε ^ 2 * Real.tan (ε * θ) ^ 2))
    simp only [Function.comp_apply]
    rw [confArg_eq θ u v ε (by simpa using hε)]
  have hz : Tendsto (fun z : ℂ => zeroFone2 z)
      (𝓝 (Complex.ofReal (-((u * v) * θ ^ 2))))
      (𝓝 (zeroFone2 (Complex.ofReal (-((u * v) * θ ^ 2))))) :=
    (continuousAt_zeroFone2 _).tendsto
  have hprod : Tendsto
      (fun ε : ℝ => (-(Complex.ofReal (u * (Real.tan (ε * θ) / ε) ^ 2))) *
        zeroFone2 (Complex.ofReal (-((u * v) / ε ^ 2 * Real.tan (ε * θ) ^ 2))))
      (𝓝[≠] 0)
      (𝓝 (-((u : ℂ) * (θ : ℂ) ^ 2) *
        zeroFone2 (Complex.ofReal (-((u * v) * θ ^ 2))))) := by
    have := hcoef.mul (hz.comp harg)
    simpa using this
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (confluentEvenAmp_div θ u v ε hε).symm

theorem tendsto_confluentOddAmp_bessel (θ u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    Tendsto (fun ε : ℝ => confluentOddAmp θ u v ε / ε) (𝓝[≠] 0)
      (𝓝 (I * (θ : ℂ) * besselJ0 (Complex.ofReal (tau u v * θ)))) := by
  have h := tendsto_confluentOddAmp_scaled θ u v
  have hz : zeroFone1 (Complex.ofReal (-((u * v) * θ ^ 2))) =
      besselJ0 (Complex.ofReal (tau u v * θ)) := by
    have harg2 : Complex.ofReal (tau u v * θ) =
        2 * Complex.ofReal (Real.sqrt (u * v) * θ) := by
      unfold tau
      push_cast
      ring
    have harg3 : (Complex.ofReal (-((u * v) * θ ^ 2))) =
        -((Complex.ofReal (Real.sqrt (u * v) * θ)) ^ 2) := by
      rw [show -((u * v) * θ ^ 2) = -((Real.sqrt (u * v) * θ) ^ 2) by
        rw [mul_pow, Real.sq_sqrt (le_of_lt (mul_pos hu hv))]]
      push_cast
      ring
    rw [harg2, harg3, ← besselJ0_zeroFone (z := Complex.ofReal (Real.sqrt (u * v) * θ))]
  rw [hz] at h
  exact h

end Qatlib.Papers.QCellAutomata96.MainResults
