/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.SearchCoreDefs
import Qatlib.Concepts.CoherentSim.CoherentOAA.QueryCircuit
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FunProp
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Moments.Variance

/-!
# Continuity limits for zero tests and clipping bounds

This module proves that finite query circuits, including words with adjoint queries, depend
continuously on a continuous oracle family. Consequently, a fixed finite circuit cannot have
event probability at least `2/3` at parameter zero and at most `1/3` at every positive parameter
up to one. This distinguishes finite zero tests from the growing search schedules used with
amplitude amplification [BrassardEtAl2002].

The module also bounds symmetric clipping and its integral bias for square-integrable random
variables. The centered estimate expresses the bias bound through variance and the squared error
of the chosen center, quantities relevant to quantum mean estimation [Montanaro2015].

## Main statements

* `fixed_budget_zero_test_impossible`: exclude a fixed-circuit zero test for the small-rotation
  family.
* `finite_adjoint_zero_test_impossible`: extend the continuity obstruction to finite
  adjoint-query words.
* `centeredClip_integral_bias`: bound centered clipping bias by a second-moment expression.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
* [Montanaro, 2015][Montanaro2015]
-/

set_option warningAsError false
open Qatlib.Concepts.PhaseGeometry.Phase

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Matrix Filter
open Qatlib.Concepts.PhaseGeometry.Phase
open MeasureTheory ProbabilityTheory
open scoped Topology

/-- Applying a continuously varying matrix to a continuously varying finite quantum state gives
a continuous state family. -/
theorem continuous_applyGate {X I : Type*} [TopologicalSpace X] [Fintype I] [DecidableEq I]
    (U : X → Matrix I I ℂ) (ψ : X → QState I) (hU : Continuous U) (hψ : Continuous ψ) :
    Continuous (fun x => ApplyGate (U x) (ψ x)) := by
  apply continuous_pi
  intro i
  simp only [ApplyGate, Matrix.mulVec, dotProduct]
  fun_prop

/-- Executing a fixed finite query circuit depends continuously on a continuous oracle family
and a continuous input-state family. -/
theorem continuous_run {X I : Type*} [TopologicalSpace X] [Fintype I] [DecidableEq I]
    (U : X → Matrix I I ℂ) (hU : Continuous U) (C : Circuit I)
    (ψ : X → QState I) (hψ : Continuous ψ) : Continuous (fun x => Run (U x) C (ψ x)) := by
  induction C generalizing ψ with
  | nil => exact hψ
  | cons s C ih =>
    cases s with
    | gate V =>
      exact ih (fun x => ApplyGate V (ψ x)) (continuous_applyGate _ _ continuous_const hψ)
    | query => exact ih (fun x => ApplyGate (U x) (ψ x)) (continuous_applyGate U ψ hU hψ)

/-- For a fixed circuit, state, and measurement event, the output event mass is continuous in a
continuously varying oracle. -/
theorem continuous_output_mass {X I : Type*} [TopologicalSpace X] [Fintype I] [DecidableEq I]
    (U : X → Matrix I I ℂ) (hU : Continuous U) (C : Circuit I)
    (ψ : QState I) (S : Finset I) : Continuous (fun x => MeasureProb (Run (U x) C ψ) S) := by
  have h := continuous_run U hU C (fun _ => ψ) continuous_const
  simp only [MeasureProb, BornProb]
  fun_prop

/-- The matrix evaluated by a fixed finite adjoint-query word is continuous in a continuous
oracle family. -/
theorem continuous_evaluate {X I : Type*} [TopologicalSpace X] [Fintype I] [DecidableEq I]
    (U : X → Matrix I I ℂ) (hU : Continuous U) (cs : List (AdjointStep I)) :
    Continuous (fun x => evaluate (U x) cs) := by
  induction cs with
  | nil => exact continuous_const
  | cons c cs ih =>
    cases c <;> simp only [evaluate, instructionMatrix] <;> fun_prop

/-- The two-dimensional small-rotation matrix depends continuously on its real angle. -/
theorem continuous_smallRotation : Continuous smallRotation := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> dsimp [smallRotation] <;> fun_prop

/-- The small-rotation matrix is unitary for every real angle. -/
theorem smallRotation_unitary (θ : ℝ) : smallRotation θ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hs : (Real.cos θ : ℂ)^2 + (Real.sin θ : ℂ)^2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [smallRotation, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  all_goals simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.conj_ofReal]
  all_goals first | linear_combination hs | ring

/-- The small rotation at angle zero is the identity matrix. -/
theorem smallRotation_zero : smallRotation 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [smallRotation, Matrix.one_apply]

/-- Applying the small rotation to `Ket 0` gives measurement probability `sin² θ` at label one. -/
theorem smallRotation_success (θ : ℝ) :
    MeasureProb (ApplyGate (smallRotation θ) (Ket 0)) {1} = (Real.sin θ)^2 := by
  simp [MeasureProb, BornProb, ApplyGate, Matrix.mulVec, dotProduct,
    Qatlib.Foundations.PureStateMath.Ket, smallRotation]
  simp only [← Complex.ofReal_sin, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- For `0 < θ ≤ 1`, the small-rotation output from `Ket 0` has strictly positive probability at
label one. -/
theorem smallRotation_success_pos (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    0 < MeasureProb (ApplyGate (smallRotation θ) (Ket 0)) {1} := by
  rw [smallRotation_success]
  exact sq_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.two_le_pi]))

/-- No continuous real function can be at least `2/3` at zero and at most `1/3` throughout `(0,
1]`. -/
theorem continuous_zero_test_boundary (f : ℝ → ℝ) (hf : Continuous f)
    (hzero : 2/3 ≤ f 0)
    (hpositive : ∀ θ : ℝ, 0 < θ → θ ≤ 1 → f θ ≤ 1/3) : False := by
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hu (n : ℕ) : f (1 / ((n : ℝ) + 1)) ≤ 1/3 := by
    apply hpositive
    · positivity
    · apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
  have hb : f 0 ≤ 1/3 := le_of_tendsto' (hf.continuousAt.tendsto.comp ht) hu
  linarith

/-- No fixed finite circuit using the small-rotation oracle can have event probability at least
`2/3` at zero and at most `1/3` at every angle in `(0, 1]`. -/
theorem fixed_budget_zero_test_impossible (C : Circuit (Fin 2)) (ψ : QState (Fin 2))
    (S : Finset (Fin 2))
    (hzero : 2/3 ≤ MeasureProb (Run (smallRotation 0) C ψ) S)
    (hpositive : ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      MeasureProb (Run (smallRotation θ) C ψ) S ≤ 1/3) : False :=
  continuous_zero_test_boundary _
    (continuous_output_mass _ continuous_smallRotation C ψ S) hzero hpositive

/-- For a continuous oracle family, no fixed finite adjoint-query word can have event
probability at least `2/3` at zero and at most `1/3` at every parameter in `(0, 1]`. -/
theorem finite_adjoint_zero_test_impossible {I : Type*} [Fintype I] [DecidableEq I]
    (U : ℝ → Matrix I I ℂ) (hU : Continuous U) (cs : List (AdjointStep I))
    (ψ : QState I) (S : Finset I)
    (hzero : 2/3 ≤ MeasureProb (ApplyGate (evaluate (U 0) cs) ψ) S)
    (hpositive : ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      MeasureProb (ApplyGate (evaluate (U θ) cs) ψ) S ≤ 1/3) : False := by
  have he := continuous_evaluate U hU cs
  have hv := continuous_applyGate (fun θ => evaluate (U θ) cs) (fun _ => ψ) he continuous_const
  apply continuous_zero_test_boundary _ ?_ hzero hpositive
  simp only [MeasureProb, BornProb]
  fun_prop

/-- For nonnegative threshold `τ`, symmetric clipping has absolute value at most `τ`. -/
theorem boundedClip_bound (τ x : ℝ) (hτ : 0 ≤ τ) : |boundedClip τ x| ≤ τ := by
  apply abs_le.mpr
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

/-- For positive threshold `τ`, the pointwise clipping error is at most `x² / (4τ)`. -/
theorem boundedClip_error (τ x : ℝ) (hτ : 0 < τ) :
    |x - boundedClip τ x| ≤ x^2 / (4*τ) := by
  unfold boundedClip
  by_cases hl : x ≤ -τ
  · rw [min_eq_right (by linarith), max_eq_left hl, abs_of_nonpos (by linarith)]
    apply (le_div_iff₀ (by positivity : 0 < 4*τ)).mpr
    nlinarith [sq_nonneg (x+2*τ)]
  · by_cases hu : τ ≤ x
    · rw [min_eq_left hu, max_eq_right (by linarith), abs_of_nonneg (by linarith)]
      apply (le_div_iff₀ (by positivity : 0 < 4*τ)).mpr
      nlinarith [sq_nonneg (x-2*τ)]
    · rw [min_eq_right (by linarith), max_eq_right (by linarith), sub_self, abs_zero]
      positivity

/-- For a square-integrable real random variable and `τ > 0`, clipping changes its mean by at
most its second moment divided by `4τ`. -/
theorem boundedClip_integral_bias {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : MemLp X 2 μ)
    (τ : ℝ) (hτ : 0 < τ) :
    |(∫ ω, X ω ∂μ) - ∫ ω, boundedClip τ (X ω) ∂μ| ≤
      (∫ ω, (X ω)^2 ∂μ) / (4*τ) := by
  have hXi : Integrable X μ := hX.integrable (by norm_num)
  have hc : Continuous (boundedClip τ) := by unfold boundedClip; fun_prop
  have hclip : Integrable (fun ω => boundedClip τ (X ω)) μ :=
    (integrable_const τ).mono' (hc.comp_aestronglyMeasurable hX.aestronglyMeasurable)
      (ae_of_all _ (fun ω => by
        simpa only [Real.norm_eq_abs] using boundedClip_bound τ (X ω) hτ.le))
  rw [← integral_sub hXi hclip]
  calc
    _ ≤ ∫ ω, |X ω - boundedClip τ (X ω)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (X ω)^2 / (4*τ) ∂μ :=
      integral_mono (hXi.sub hclip).abs (hX.integrable_sq.div_const _)
        (fun ω => boundedClip_error τ (X ω) hτ)
    _ = _ := integral_div _ _

/-- For a square-integrable real random variable and `τ > 0`, clipping around center `c` changes
the mean by at most variance plus squared mean-center error, divided by `4τ`. -/
theorem centeredClip_integral_bias {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : MemLp X 2 μ)
    (c τ : ℝ) (hτ : 0 < τ) :
    |(∫ ω, X ω ∂μ) - (c + ∫ ω, boundedClip τ (X ω - c) ∂μ)| ≤
      (variance X μ + ((∫ ω, X ω ∂μ) - c)^2) / (4*τ) := by
  have hZ : MemLp (fun ω => X ω - c) 2 μ := hX.sub (memLp_const c)
  have hmean : (∫ ω, X ω - c ∂μ) = (∫ ω, X ω ∂μ) - c := by
    rw [integral_sub (hX.integrable (by norm_num)) (integrable_const c)]
    simp
  have hv := variance_eq_sub hZ
  rw [variance_sub_const hX.aestronglyMeasurable, hmean] at hv
  simp only [Pi.pow_apply] at hv
  have hsecond : (∫ ω, (X ω - c)^2 ∂μ) =
      variance X μ + ((∫ ω, X ω ∂μ) - c)^2 := by linarith only [hv]
  have hb := boundedClip_integral_bias μ (fun ω => X ω - c) hZ τ hτ
  rw [hmean, hsecond] at hb
  calc
    _ = |((∫ ω, X ω ∂μ) - c) - ∫ ω, boundedClip τ (X ω - c) ∂μ| := by
      congr 1
      ring
    _ ≤ _ := hb

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
