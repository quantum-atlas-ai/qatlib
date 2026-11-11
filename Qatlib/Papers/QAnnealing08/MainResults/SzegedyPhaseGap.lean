/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Spectral.SzegedySpectral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Spectral gaps and Szegedy rotation

This module compares the classical spectral gap `1 - lambda1` with the angle `arccos lambda1`
and bounds the associated reciprocal-angle step scale. The resulting scalar inequalities exhibit
inverse-square-root gap dependence in the setting of [SommaEtAl2008].

The theorem `szegedyWalk_rotation_bridge` separately realizes a normalized discriminant
eigenvector as an orthonormal two-dimensional walk subspace with rotation angle `2θ`.

## Main statements

* `main_result_qsa_quadratic_speedup`: the gap positivity and reciprocal-angle comparisons.
* `szegedyWalk_rotation_bridge`: an explicit two-dimensional rotation for the Szegedy walk.

## References

* [Somma et al., 2008][SommaEtAl2008]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.WalkSearch.TwoLevelLower
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.QAnnealing08.MainResults.SzegedyPhaseGap

/-- The scalar classical spectral gap `1 - lambda1`. -/
def classicalSpectralGap (lambda1 : ℝ) : ℝ := 1 - lambda1

/-- The angle `Real.arccos lambda1` associated with the spectral parameter. -/
noncomputable def phaseGap (lambda1 : ℝ) : ℝ := Real.arccos lambda1

/-- The reciprocal-gap scalar step scale. -/
noncomputable def classicalAnnealingSteps (delta : ℝ) : ℝ := 1 / delta

/-- The reciprocal of the angle `phaseGap lambda1`. -/
noncomputable def qsaWalkSteps (lambda1 : ℝ) : ℝ := 1 / phaseGap lambda1

/-- For `lambda1` in `[-1, 1]`, the classical gap is at most half the square of its arccosine
angle [SommaEtAl2008]. -/
theorem spectralGap_le_half_phaseGap_sq (lambda1 : ℝ)
    (h1 : -1 ≤ lambda1) (h2 : lambda1 ≤ 1) :
    classicalSpectralGap lambda1 ≤ (phaseGap lambda1) ^ 2 / 2 := by
  unfold classicalSpectralGap phaseGap
  have hcos : Real.cos (Real.arccos lambda1) = lambda1 := Real.cos_arccos h1 h2
  have hbound : 1 - (Real.arccos lambda1) ^ 2 / 2 ≤ Real.cos (Real.arccos lambda1) :=
    Real.one_sub_sq_div_two_le_cos (x := Real.arccos lambda1)
  nlinarith [hcos, hbound]

/-- For `lambda1` in `[-1, 1]`, the phase-gap angle is at least the square root of twice the
classical gap. -/
theorem phaseGap_ge_sqrt_two_delta (lambda1 : ℝ)
    (h1 : -1 ≤ lambda1) (h2 : lambda1 ≤ 1) :
    Real.sqrt (2 * classicalSpectralGap lambda1) ≤ phaseGap lambda1 := by
  have hφ0 : 0 ≤ phaseGap lambda1 := Real.arccos_nonneg lambda1
  rw [Real.sqrt_le_left hφ0]
  have hle := spectralGap_le_half_phaseGap_sq lambda1 h1 h2
  linarith

/-- For `0 ≤ lambda1 < 1`, the phase-gap angle lies between the square root of twice the
classical gap and `π / 2` [SommaEtAl2008]. -/
theorem phaseGap_mem_window (lambda1 : ℝ) (h0 : 0 ≤ lambda1) (h1 : lambda1 < 1) :
    Real.sqrt (2 * classicalSpectralGap lambda1) ≤ phaseGap lambda1 ∧
    phaseGap lambda1 ≤ Real.pi / 2 := by
  have hle1 : lambda1 ≤ 1 := le_of_lt h1
  refine ⟨phaseGap_ge_sqrt_two_delta lambda1 (by linarith) hle1, ?_⟩
  unfold phaseGap
  exact Real.arccos_le_pi_div_two.2 h0

/-- For `-1 ≤ lambda1 < 1`, the reciprocal-angle step scale is at most the reciprocal square
root of twice the classical gap [SommaEtAl2008]. -/
theorem qsa_step_bound (lambda1 : ℝ) (h1 : -1 ≤ lambda1) (h2lt : lambda1 < 1) :
    qsaWalkSteps lambda1 ≤ 1 / Real.sqrt (2 * classicalSpectralGap lambda1) := by
  have hδ : 0 < classicalSpectralGap lambda1 := by
    unfold classicalSpectralGap; linarith
  have hpos : 0 < Real.sqrt (2 * classicalSpectralGap lambda1) := by
    apply Real.sqrt_pos.mpr; linarith
  have hge := phaseGap_ge_sqrt_two_delta lambda1 h1 (le_of_lt h2lt)
  unfold qsaWalkSteps
  exact one_div_le_one_div_of_le hpos hge

/-- For `-1 ≤ lambda1 < 1`, the square of the reciprocal-angle step scale is at most half the
classical reciprocal-gap scale [SommaEtAl2008]. -/
theorem qsa_quadratic_improvement (lambda1 : ℝ) (h1 : -1 ≤ lambda1) (h2lt : lambda1 < 1) :
    (qsaWalkSteps lambda1) ^ 2 ≤
      classicalAnnealingSteps (classicalSpectralGap lambda1) / 2 := by
  have hδ : 0 < classicalSpectralGap lambda1 := by
    unfold classicalSpectralGap; linarith
  have hstep := qsa_step_bound lambda1 h1 h2lt
  have hqsa0 : 0 ≤ qsaWalkSteps lambda1 := by
    unfold qsaWalkSteps phaseGap
    exact div_nonneg zero_le_one (Real.arccos_nonneg lambda1)
  have hsq := pow_le_pow_left₀ hqsa0 hstep 2
  have hsqrt_sq : (1 / Real.sqrt (2 * classicalSpectralGap lambda1)) ^ 2
      = 1 / (2 * classicalSpectralGap lambda1) := by
    rw [div_pow, one_pow, Real.sq_sqrt (by linarith)]
  rw [hsqrt_sq] at hsq
  refine hsq.trans_eq ?_
  unfold classicalAnnealingSteps
  have hne : classicalSpectralGap lambda1 ≠ 0 := ne_of_gt hδ
  field_simp

/-- For `-1 ≤ lambda1 < 1`, the classical gap is positive, and the reciprocal-angle step scale
obeys both the inverse-square-root bound and the stated squared-scale comparison
[SommaEtAl2008]. -/
theorem main_result_qsa_quadratic_speedup (lambda1 : ℝ) (h1 : -1 ≤ lambda1)
    (h2lt : lambda1 < 1) :
    0 < classicalSpectralGap lambda1 ∧
    qsaWalkSteps lambda1 ≤ 1 / Real.sqrt (2 * classicalSpectralGap lambda1) ∧
    (qsaWalkSteps lambda1) ^ 2 ≤
      classicalAnnealingSteps (classicalSpectralGap lambda1) / 2 := by
  refine ⟨?_, qsa_step_bound lambda1 h1 h2lt, qsa_quadratic_improvement lambda1 h1 h2lt⟩
  unfold classicalSpectralGap
  linarith

/-- A normalized discriminant eigenvector with eigenvalue `cos θ` and nonzero `sin θ` yields two
normalized orthogonal states on which the Szegedy walk acts by the displayed rotation
through `2θ` [SommaEtAl2008]. -/
theorem szegedyWalk_rotation_bridge
    {I : Type*} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (hP : IsTransitionMatrix P)
    (v : I → ℝ) (hv : ∑ i, v i ^ 2 = 1)
    (θ : ℝ) (hs : Real.sin θ ≠ 0)
    (hvD : SzegedyDiscriminant P *ᵥ v = (Real.cos θ) • v) :
    ∃ (w₀ w₁ : QState (I × I)), Normalized w₀ ∧ Normalized w₁ ∧ Inner w₀ w₁ = 0 ∧
      SzegedyWalk P *ᵥ w₀
        = (((Real.cos (2 * θ) : ℝ)) : ℂ) • w₀ + (((Real.sin (2 * θ) : ℝ)) : ℂ) • w₁ ∧
      SzegedyWalk P *ᵥ w₁
        = (-(((Real.sin (2 * θ) : ℝ)) : ℂ)) • w₀ + (((Real.cos (2 * θ) : ℝ)) : ℂ) • w₁ :=
  Qatlib.Concepts.WalkSearch.Spectral.szegedy_spectral_map
    P hP v hv θ hs hvD

end Qatlib.Papers.QAnnealing08.MainResults.SzegedyPhaseGap
