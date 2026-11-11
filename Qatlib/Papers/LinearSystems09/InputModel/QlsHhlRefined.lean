/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LinearSystems09.InputModel.QlsHhlRefinedDefs

/-!
# Refined HHL preparation and error bounds

This module refines the HHL input-model estimates from [HarrowHassidimLloyd2009] using explicit
resource ledgers, half-grid preparation errors, and rectangular solution extraction. It also
records signed-filter identities and error-budget conditions, including the obstruction caused
by zero least-squares overlap.

## Main statements

* `clause53_endpoint`: Collects preparation resource counts and dyadic approximation bounds.
* `clause55_endpoint`: Packages dilation resources and least-squares extraction properties.
* `clause60_endpoint`: Collects signed-filter mass, phase, and error-budget facts.

## References

* [Harrow et al., 2009][HarrowHassidimLloyd2009]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.HhlAlgorithms.Postselection
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlErrorBridge.FilterStability
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.QsvtCore.QsVtStability
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Papers.LinearSystems09.InputModel

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.LinearSystems09.InputModel.QlsHhlRefined

open scoped BigOperators
open Matrix
open Qatlib

/-- The access ledger records `m * d` oracle calls and controlled synthesis steps, and preserves
the supplied bit-time and workspace counts. -/
theorem thresholdGoal_access_ledger_counts (m d bitTime workspace : ℕ) :
    (hhlAccessLedger m d bitTime workspace).oracleCalls = m * d ∧
      (hhlAccessLedger m d bitTime workspace).controlledSynthesis = m * d ∧
      (hhlAccessLedger m d bitTime workspace).integerBitTime = bitTime ∧
      (hhlAccessLedger m d bitTime workspace).peakWorkspace = workspace := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The oracle-call count in the access ledger is monotone in the round and phase-step counts. -/
theorem thresholdGoal_access_ledger_mono (m m' d d' : ℕ) (hm : m ≤ m') (hd : d ≤ d') :
    (hhlAccessLedger m d 0 0).oracleCalls ≤ (hhlAccessLedger m' d' 0 0).oracleCalls := by
  simp only [hhlAccessLedger]
  exact Nat.mul_le_mul hm hd

/-- Collects the exact oracle and synthesis counts and monotonicity of the oracle count for the
access ledger. -/
theorem thresholdGoal_endpoint :
    (∀ m d bitTime workspace : ℕ,
      (hhlAccessLedger m d bitTime workspace).oracleCalls = m * d ∧
        (hhlAccessLedger m d bitTime workspace).controlledSynthesis = m * d) ∧
      (∀ m m' d d' : ℕ, m ≤ m' → d ≤ d' →
        (hhlAccessLedger m d 0 0).oracleCalls ≤ (hhlAccessLedger m' d' 0 0).oracleCalls) := by
  refine ⟨fun m d bitTime workspace => ⟨rfl, rfl⟩, fun m m' d d' hm hd => ?_⟩
  exact thresholdGoal_access_ledger_mono m m' d d' hm hd

/-- For positive `n`, the logarithm of the Simon-reduction runtime is `α * log (36 * n) + (3 * α
+ 4 * β) * n * log 2` [HarrowHassidimLloyd2009]. -/
theorem clause11_simon_runtime_exponent (α β : ℝ) (n : ℕ) (hn : 0 < n) :
    Real.log (simonReductionRuntime α β n)
      = α * Real.log (36 * (n : ℝ)) + (3 * α + 4 * β) * (n : ℝ) * Real.log 2 := by
  have hnpos : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hne36 : 36 * (n : ℝ) ≠ 0 := by positivity
  have hne2 : (2 : ℝ) ≠ 0 := by norm_num
  have h2pos : (0:ℝ) < (2:ℝ) := by norm_num
  have hinst : (0:ℝ) < simonInstanceSize n := by
    unfold simonInstanceSize
    positivity
  have hneinst : simonInstanceSize n ≠ 0 := ne_of_gt hinst
  have hlogsize : Real.log (simonInstanceSize n)
      = Real.log (36 * (n : ℝ)) + 3 * (n : ℝ) * Real.log 2 := by
    have h1 : Real.log (36 * (n : ℝ) * (2 : ℝ) ^ (3 * (n : ℝ)))
        = Real.log (36 * (n : ℝ)) + Real.log ((2 : ℝ) ^ (3 * (n : ℝ))) :=
      Real.log_mul hne36 (by positivity)
    have h2 : Real.log ((2 : ℝ) ^ (3 * (n : ℝ))) = 3 * (n : ℝ) * Real.log 2 :=
      Real.log_rpow h2pos _
    show Real.log (36 * (n : ℝ) * (2 : ℝ) ^ (3 * (n : ℝ)))
      = Real.log (36 * (n : ℝ)) + 3 * (n : ℝ) * Real.log 2
    rw [h1, h2]
  have hlogpow : Real.log (simonInstanceSize n ^ α) = α * Real.log (simonInstanceSize n) :=
    Real.log_rpow hinst α
  have hlogtwo : Real.log ((2 : ℝ) ^ (β * simonConditionNumber n))
      = β * simonConditionNumber n * Real.log 2 := Real.log_rpow h2pos _
  have hmul : Real.log (simonInstanceSize n ^ α * (2 : ℝ) ^ (β * simonConditionNumber n))
      = Real.log (simonInstanceSize n ^ α)
        + Real.log ((2 : ℝ) ^ (β * simonConditionNumber n)) :=
    Real.log_mul (by positivity) (by positivity)
  calc
    Real.log (simonReductionRuntime α β n)
      = Real.log (simonInstanceSize n ^ α * (2 : ℝ) ^ (β * simonConditionNumber n)) := rfl
    _ = Real.log (simonInstanceSize n ^ α)
        + Real.log ((2 : ℝ) ^ (β * simonConditionNumber n)) := hmul
    _ = (α * Real.log (simonInstanceSize n))
        + (β * simonConditionNumber n * Real.log 2) := by rw [hlogpow, hlogtwo]
    _ = α * Real.log (36 * (n : ℝ)) + (3 * α + 4 * β) * (n : ℝ) * Real.log 2 := by
      rw [hlogsize]
      simp only [simonConditionNumber]
      ring

/-- Packages the explicit logarithmic Simon-reduction runtime formula for all positive `n`. -/
theorem clause11_endpoint :
    ∀ α β : ℝ, ∀ n : ℕ, 0 < n →
      Real.log (simonReductionRuntime α β n)
        = α * Real.log (36 * (n : ℝ)) + (3 * α + 4 * β) * (n : ℝ) * Real.log 2 :=
  fun α β n hn => clause11_simon_runtime_exponent α β n hn

/-- The controlled-synthesis count equals the oracle-call count in the access ledger. -/
theorem clause13_controlled_synthesis_eq_oracle (m d bitTime workspace : ℕ) :
    (hhlAccessLedger m d bitTime workspace).controlledSynthesis =
      (hhlAccessLedger m d bitTime workspace).oracleCalls := by
  rfl

/-- Collects equality of synthesis and oracle counts and monotonicity of the synthesis count in
rounds and phase steps. -/
theorem clause13_endpoint :
    (∀ m d bitTime workspace : ℕ,
      (hhlAccessLedger m d bitTime workspace).controlledSynthesis =
        (hhlAccessLedger m d bitTime workspace).oracleCalls) ∧
      (∀ m m' d d' : ℕ, m ≤ m' → d ≤ d' →
        (hhlAccessLedger m d 0 0).controlledSynthesis ≤
          (hhlAccessLedger m' d' 0 0).controlledSynthesis) := by
  refine ⟨fun m d bitTime workspace => clause13_controlled_synthesis_eq_oracle m d bitTime workspace,
    fun m m' d d' hm hd => ?_⟩
  simp only [hhlAccessLedger]
  exact Nat.mul_le_mul hm hd

/-- For nonnegative per-step error, cumulative quantization error is monotone in the number of
steps. -/
theorem walkGoal_cumulative_quantization_error (n n' : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (hn : n ≤ n') :
    cumulativeQuantizationError n ε ≤ cumulativeQuantizationError n' ε := by
  simp only [cumulativeQuantizationError]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hε

/-- Packages monotonicity of cumulative quantization error for nonnegative per-step error. -/
theorem walkGoal_endpoint :
    ∀ n n' : ℕ, ∀ ε : ℝ, 0 ≤ ε → n ≤ n' →
      cumulativeQuantizationError n ε ≤ cumulativeQuantizationError n' ε :=
  fun n n' ε hε hn => walkGoal_cumulative_quantization_error n n' ε hε hn

section Clause12

/-- For positive `M`, reflection of a half-grid index sends its angle to `π` minus the original
angle. -/
theorem clause12_halfGridAngle_mirror (M : ℕ) (hM : 0 < M) (τ : Fin M) :
    halfGridAngle M (halfGridMirrorIndex M τ) = Real.pi - halfGridAngle M τ := by
  have hcast : ((M - 1 - τ.val : ℕ) : ℝ) = (M : ℝ) - 1 - (τ.val : ℝ) := by
    have h1 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have h2 : ((M - 1 - τ.val : ℕ) : ℝ) = ((M - 1 : ℕ) : ℝ) - (τ.val : ℝ) := by
      rw [Nat.cast_sub (by omega)]
    rw [h2, h1]
  have hne : (2 * (M : ℝ)) ≠ 0 := by positivity
  have hval : (halfGridMirrorIndex M τ).val = M - 1 - τ.val := rfl
  unfold halfGridAngle
  rw [hval, hcast]
  apply (div_eq_iff hne).2
  rw [sub_mul]
  field_simp
  ring

/-- The dyadic half-grid angle differs from the exact angle by at most `π / 2^k`. -/
theorem clause12_halfGridAngle_dyadic_bound (M k : ℕ) (hM : 0 < M) (τ : Fin M) :
    |halfGridAngleDyadic M k τ - halfGridAngle M τ| ≤ Real.pi / 2 ^ k := by
  let X : ℝ := ((2 * (τ.val : ℝ) + 1) / (2 * (M : ℝ))) * 2 ^ k
  have hXpos : 0 ≤ X := by positivity
  have h1 : ((halfGridParam M k τ : ℕ) : ℝ) ≤ X := by
    simpa [X] using! (Nat.floor_le hXpos)
  have h2 : X < ((halfGridParam M k τ : ℕ) : ℝ) + 1 := by
    simpa [X] using! (Nat.lt_floor_add_one X)
  have hdiff : |((halfGridParam M k τ : ℕ) : ℝ) - X| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hXdiv : X / 2 ^ k = (2 * (τ.val : ℝ) + 1) / (2 * (M : ℝ)) := by
    simp only [X]
    field_simp
  have hne2 : (2 ^ k : ℝ) ≠ 0 := by positivity
  have hform : ((halfGridParam M k τ : ℕ) : ℝ) / 2 ^ k
      - (2 * (τ.val : ℝ) + 1) / (2 * (M : ℝ))
      = (((halfGridParam M k τ : ℕ) : ℝ) - X) / 2 ^ k := by
    rw [← hXdiv]
    ring
  have hq : |((halfGridParam M k τ : ℕ) : ℝ) / 2 ^ k
      - (2 * (τ.val : ℝ) + 1) / (2 * (M : ℝ))| ≤ 1 / 2 ^ k := by
    rw [hform, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ k)]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ k)]
    have hone : ((1 : ℝ) / 2 ^ k) * 2 ^ k = 1 := by
      calc ((1 : ℝ) / 2 ^ k) * 2 ^ k = ((2 ^ k : ℝ)⁻¹) * (2 ^ k : ℝ) := by rw [one_div]
        _ = 1 := inv_mul_cancel₀ hne2
    rw [hone]
    exact hdiff
  have hmain : |Real.pi * (((halfGridParam M k τ : ℕ) : ℝ) / 2 ^ k
      - (2 * (τ.val : ℝ) + 1) / (2 * (M : ℝ)))| ≤ Real.pi * (1 / 2 ^ k) := by
    rw [abs_mul, abs_of_nonneg (Real.pi_pos.le)]
    exact mul_le_mul_of_nonneg_left hq (Real.pi_pos.le)
  have hmain' : |Real.pi * (((halfGridParam M k τ : ℕ) : ℝ) / 2 ^ k
      - (2 * (τ.val : ℝ) + 1) / (2 * (M : ℝ)))| ≤ Real.pi / 2 ^ k := by
    simpa using! hmain
  unfold halfGridAngleDyadic
  have hsplit : Real.pi * (((halfGridParam M k τ : ℕ) : ℝ) / 2 ^ k)
      - halfGridAngle M τ
      = Real.pi * (((halfGridParam M k τ : ℕ) : ℝ) / 2 ^ k
        - (2 * (τ.val : ℝ) + 1) / (2 * (M : ℝ))) := by
    unfold halfGridAngle
    ring
  rw [hsplit, abs_mul, abs_of_nonneg (Real.pi_pos.le)]
  calc Real.pi * |((halfGridParam M k τ : ℕ) : ℝ) / 2 ^ k
        - (2 * (τ.val : ℝ) + 1) / (2 * (M : ℝ))|
      ≤ Real.pi * (1 / 2 ^ k) := mul_le_mul_of_nonneg_left hq (Real.pi_pos.le)
    _ = Real.pi / 2 ^ k := by ring

/-- The sum of squared cosine and sine errors for a dyadic angle is at most `2 * (π / 2^k)^2`. -/
theorem clause12_prep_amplitude_error (M k : ℕ) (hM : 0 < M) (τ : Fin M) :
    (Real.cos (halfGridAngleDyadic M k τ) - Real.cos (halfGridAngle M τ)) ^ 2 +
      (Real.sin (halfGridAngleDyadic M k τ) - Real.sin (halfGridAngle M τ)) ^ 2
        ≤ 2 * (Real.pi / 2 ^ k) ^ 2 := by
  have hangle : |halfGridAngleDyadic M k τ - halfGridAngle M τ| ≤ Real.pi / 2 ^ k :=
    clause12_halfGridAngle_dyadic_bound M k hM τ
  have hcos : |Real.cos (halfGridAngleDyadic M k τ) - Real.cos (halfGridAngle M τ)|
      ≤ Real.pi / 2 ^ k := (Real.abs_cos_sub_cos_le _ _).trans hangle
  have hsin : |Real.sin (halfGridAngleDyadic M k τ) - Real.sin (halfGridAngle M τ)|
      ≤ Real.pi / 2 ^ k := (Real.abs_sin_sub_sin_le _ _).trans hangle
  have h1 : (Real.cos (halfGridAngleDyadic M k τ) - Real.cos (halfGridAngle M τ)) ^ 2
      ≤ (Real.pi / 2 ^ k) ^ 2 := by
    calc (Real.cos (halfGridAngleDyadic M k τ) - Real.cos (halfGridAngle M τ)) ^ 2
        = |Real.cos (halfGridAngleDyadic M k τ) - Real.cos (halfGridAngle M τ)| ^ 2 :=
          (sq_abs _).symm
      _ = |Real.cos (halfGridAngleDyadic M k τ) - Real.cos (halfGridAngle M τ)| *
          |Real.cos (halfGridAngleDyadic M k τ) - Real.cos (halfGridAngle M τ)| := (pow_two _)
      _ ≤ (Real.pi / 2 ^ k) * (Real.pi / 2 ^ k) :=
          mul_self_le_mul_self (abs_nonneg _) hcos
      _ = (Real.pi / 2 ^ k) ^ 2 := (pow_two _).symm
  have h2 : (Real.sin (halfGridAngleDyadic M k τ) - Real.sin (halfGridAngle M τ)) ^ 2
      ≤ (Real.pi / 2 ^ k) ^ 2 := by
    calc (Real.sin (halfGridAngleDyadic M k τ) - Real.sin (halfGridAngle M τ)) ^ 2
        = |Real.sin (halfGridAngleDyadic M k τ) - Real.sin (halfGridAngle M τ)| ^ 2 :=
          (sq_abs _).symm
      _ = |Real.sin (halfGridAngleDyadic M k τ) - Real.sin (halfGridAngle M τ)| *
          |Real.sin (halfGridAngleDyadic M k τ) - Real.sin (halfGridAngle M τ)| := (pow_two _)
      _ ≤ (Real.pi / 2 ^ k) * (Real.pi / 2 ^ k) :=
          mul_self_le_mul_self (abs_nonneg _) hsin
      _ = (Real.pi / 2 ^ k) ^ 2 := (pow_two _).symm
  nlinarith [h1, h2]

/-- For positive `M`, the average squared trigonometric preparation error is at most `(2 * π /
2^k)^2`. -/
theorem clause12_prep_l2_error (M k : ℕ) (hM : 0 < M) :
    (∑ τ : Fin M,
      ((Real.cos (halfGridAngleDyadic M k τ) - Real.cos (halfGridAngle M τ)) ^ 2 +
        (Real.sin (halfGridAngleDyadic M k τ) - Real.sin (halfGridAngle M τ)) ^ 2)) / (M : ℝ)
      ≤ (2 * Real.pi / 2 ^ k) ^ 2 := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hsq : (∑ τ : Fin M,
        ((Real.cos (halfGridAngleDyadic M k τ) - Real.cos (halfGridAngle M τ)) ^ 2 +
          (Real.sin (halfGridAngleDyadic M k τ) - Real.sin (halfGridAngle M τ)) ^ 2))
      ≤ ∑ _τ : Fin M, 2 * (Real.pi / 2 ^ k) ^ 2 := by
    refine Finset.sum_le_sum fun τ _ => ?_
    exact clause12_prep_amplitude_error M k hM τ
  calc (∑ τ : Fin M,
        ((Real.cos (halfGridAngleDyadic M k τ) - Real.cos (halfGridAngle M τ)) ^ 2 +
          (Real.sin (halfGridAngleDyadic M k τ) - Real.sin (halfGridAngle M τ)) ^ 2)) / (M : ℝ)
      ≤ (∑ _τ : Fin M, 2 * (Real.pi / 2 ^ k) ^ 2) / (M : ℝ) := by
        exact div_le_div_of_nonneg_right hsq (by positivity)
    _ = 2 * (Real.pi / 2 ^ k) ^ 2 := by
        simp [Finset.sum_const, nsmul_eq_mul]
        field_simp
    _ ≤ (2 * Real.pi / 2 ^ k) ^ 2 := by
        have hnonneg : 0 ≤ (Real.pi / 2 ^ k) ^ 2 := sq_nonneg _
        have hstep : 2 * (Real.pi / 2 ^ k) ^ 2 ≤ 4 * (Real.pi / 2 ^ k) ^ 2 := by linarith
        calc 2 * (Real.pi / 2 ^ k) ^ 2 ≤ 4 * (Real.pi / 2 ^ k) ^ 2 := hstep
          _ = (2 * Real.pi / 2 ^ k) ^ 2 := by ring

/-- The symmetrized half-grid chirp equals `I` times the uniform amplitude times the sine of the
half-grid angle. -/
theorem clause12_symmetrized_scaled (M : ℕ) (hM : 0 < M) (τ : Fin M) :
    halfGridSymmetrized M τ
      = Complex.I * halfGridAmplitude M * (Real.sin (halfGridAngle M τ) : ℂ) := by
  have hm : halfGridAngle M (halfGridMirrorIndex M τ) = Real.pi - halfGridAngle M τ :=
    clause12_halfGridAngle_mirror M hM τ
  have hcos : Real.cos (halfGridAngle M (halfGridMirrorIndex M τ))
      = -Real.cos (halfGridAngle M τ) := by rw [hm, Real.cos_pi_sub]
  have hsin : Real.sin (halfGridAngle M (halfGridMirrorIndex M τ))
      = Real.sin (halfGridAngle M τ) := by rw [hm, Real.sin_pi_sub]
  have hsum : halfGridChirp M τ + halfGridChirp M (halfGridMirrorIndex M τ)
      = 2 * Complex.I * halfGridAmplitude M * (Real.sin (halfGridAngle M τ) : ℂ) := by
    unfold halfGridChirp halfGridAmplitude
    rw [hcos, hsin]
    push_cast
    ring
  unfold halfGridSymmetrized
  rw [hsum]
  push_cast
  ring

/-- The sine-envelope state equals `sqrt 2` times the uniform half-grid amplitude times the sine
of the half-grid angle. -/
theorem clause12_sinEnvelope_scaled (M : ℕ) (hM : 0 < M) (τ : Fin M) :
    Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL.sinEnvelopeState M τ
      = (Real.sqrt 2 : ℂ) * halfGridAmplitude M * (Real.sin (halfGridAngle M τ) : ℂ) := by
  have hθ : Real.pi * ((τ.val : ℝ) + 1 / 2) / (M : ℝ) = halfGridAngle M τ := by
    unfold halfGridAngle
    field_simp
  have hsqrt2 : Real.sqrt (2 / (M : ℝ)) = Real.sqrt 2 / Real.sqrt (M : ℝ) := by
    have hsq : (Real.sqrt (2 / (M : ℝ))) ^ 2
        = (Real.sqrt 2 / Real.sqrt (M : ℝ)) ^ 2 := by
      rw [Real.sq_sqrt (by positivity), div_pow, Real.sq_sqrt (by norm_num),
        Real.sq_sqrt (by positivity)]
    have h1 : 0 ≤ Real.sqrt (2 / (M : ℝ)) := Real.sqrt_nonneg _
    have h2 : 0 ≤ Real.sqrt 2 / Real.sqrt (M : ℝ) := by positivity
    nlinarith
  have hcast : ((Real.sqrt (2 / (M : ℝ)) : ℝ) : ℂ)
      = (Real.sqrt 2 : ℂ) * (Real.sqrt (M : ℝ) : ℂ)⁻¹ := by
    rw [hsqrt2]
    push_cast
    field_simp
  rw [Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL.sinEnvelopeState, hθ, hcast]
  unfold halfGridAmplitude
  push_cast
  field_simp

/-- The symmetrized half-grid state is `I / sqrt 2` times the sine-envelope state. -/
theorem clause12_symmetrized_eq_sinEnvelope (M : ℕ) (hM : 0 < M) :
    ∀ τ : Fin M, halfGridSymmetrized M τ
      = (Complex.I / (Real.sqrt 2 : ℂ)) * Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL.sinEnvelopeState M τ := by
  intro τ
  rw [clause12_symmetrized_scaled M hM τ, clause12_sinEnvelope_scaled M hM τ]
  field_simp

/-- Collects preparation gate, workspace, and parameter-bit counts, their stated monotonicity
properties, dyadic approximation bounds, mirror symmetry, and the sine-envelope identity. -/
theorem clause53_endpoint :

    (∀ M k : ℕ, prepGateCount M k = 3 * M) ∧
    (∀ M k M' k' : ℕ, M ≤ M' → k ≤ k' → prepGateCount M k ≤ prepGateCount M' k') ∧
    (∀ M : ℕ, prepWorkspace M = M) ∧
    (∀ M k : ℕ, prepParamBits M k = M * k) ∧
    (∀ M k M' k' : ℕ, M ≤ M' → k ≤ k' → prepParamBits M k ≤ prepParamBits M' k') ∧

    (∀ (M k : ℕ) (τ : Fin M), 0 < M →
      |halfGridAngleDyadic M k τ - halfGridAngle M τ| ≤ Real.pi / 2 ^ k) ∧

    (∀ M k : ℕ, 0 < M →
      (∑ τ : Fin M,
        ((Real.cos (halfGridAngleDyadic M k τ) - Real.cos (halfGridAngle M τ)) ^ 2 +
          (Real.sin (halfGridAngleDyadic M k τ) - Real.sin (halfGridAngle M τ)) ^ 2)) / (M : ℝ)
        ≤ (2 * Real.pi / 2 ^ k) ^ 2) ∧

    (∀ (M : ℕ) (τ : Fin M), 0 < M →
      halfGridAngle M (halfGridMirrorIndex M τ) = Real.pi - halfGridAngle M τ) ∧

    (∀ (M : ℕ) (τ : Fin M), 0 < M →
      halfGridSymmetrized M τ
        = (Complex.I / (Real.sqrt 2 : ℂ)) * Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL.sinEnvelopeState M τ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M k
    rfl
  · intro M k M' k' hM hk
    simp only [prepGateCount]
    exact Nat.mul_le_mul_left 3 hM
  · intro M
    rfl
  · intro M k
    rfl
  · intro M k M' k' hM hk
    simp only [prepParamBits]
    exact Nat.mul_le_mul hM hk
  · intro M k τ hM
    exact clause12_halfGridAngle_dyadic_bound M k hM τ
  · intro M k hM
    exact clause12_prep_l2_error M k hM
  · intro M τ hM
    exact clause12_halfGridAngle_mirror M hM τ
  · intro M τ hM
    exact clause12_symmetrized_eq_sinEnvelope M hM τ

end Clause12

section Clause14

/-- Extracting the solution block after applying the dilation pseudoinverse to the embedded
input yields the least-squares vector [HarrowHassidimLloyd2009]. -/
theorem clause14_solution_block_roundtrip {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (b : QState O) :
    dilationSolutionBlock (matrixPseudoinverse (Qatlib.Concepts.QlsReadoutSpec.RectDilation.hermitianDilation A) *ᵥ Qatlib.Concepts.QlsReadoutSpec.RectDilation.dilationInput b)
      = leastSquaresVector A b := by
  obtain ⟨R, hRA, hRb, hR⟩ :=
      Qatlib.Concepts.QlsReadoutSpec.RectDilation.rectangular_dilation_reduction O I A b
  have hred : leastSquaresVector A b = fun i =>
      (matrixPseudoinverse (Qatlib.Concepts.QlsReadoutSpec.RectDilation.hermitianDilation A) *ᵥ Qatlib.Concepts.QlsReadoutSpec.RectDilation.dilationInput b) (Sum.inr i) := by
    simpa [hRA, hRb] using! hR.2
  unfold dilationSolutionBlock
  exact hred.symm

/-- The squared mass of the extracted solution block is at most the sum of the squared masses of
both dilation blocks. -/
theorem clause14_extraction_contraction {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (x : QState (O ⊕ I)) :
    (∑ i : I, ‖(dilationSolutionBlock x) i‖ ^ 2)
      ≤ (∑ i : I, ‖x (Sum.inr i)‖ ^ 2) + (∑ o : O, ‖x (Sum.inl o)‖ ^ 2) := by
  simp only [dilationSolutionBlock]
  have hnonneg : 0 ≤ (∑ o : O, ‖x (Sum.inl o)‖ ^ 2) := by positivity
  nlinarith

/-- The squared norm of the right-hand side splits into squared least-squares overlap and
squared residual norm. -/
theorem clause14_residual_budget {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (b : QState O) :
    ‖stateVector b‖ ^ 2 = (leastSquaresOverlap A b) ^ 2 +
      ‖stateVector (A *ᵥ leastSquaresVector A b - b)‖ ^ 2 :=
  (leastSquares_overlap_and_zero A b).2.2.2

/-- The least-squares overlap vanishes exactly when the least-squares vector is zero. -/
theorem clause14_zero_overlap_iff {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (b : QState O) :
    leastSquaresOverlap A b = 0 ↔ leastSquaresVector A b = 0 :=
  (leastSquares_overlap_and_zero A b).2.1

/-- The least-squares direction is `none` when the least-squares vector vanishes. -/
theorem clause14_zero_overlap_direction {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (b : QState O)
    (h : leastSquaresVector A b = 0) : leastSquaresDirection A b = none := by
  unfold leastSquaresDirection
  rw [if_pos h]

/-- When the least-squares overlap is zero, the residual norm equals the norm of the right-hand
side. -/
theorem clause14_zero_overlap_residual {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (b : QState O)
    (h : leastSquaresOverlap A b = 0) :
    ‖stateVector (A *ᵥ leastSquaresVector A b - b)‖ = ‖stateVector b‖ := by
  have hres := clause14_residual_budget A b
  rw [h] at hres
  have hn1 : 0 ≤ ‖stateVector (A *ᵥ leastSquaresVector A b - b)‖ := norm_nonneg _
  have hn2 : 0 ≤ ‖stateVector b‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖stateVector (A *ᵥ leastSquaresVector A b - b)‖
    - ‖stateVector b‖)]

/-- The dilation route ledger records the supplied preparation cost, `m + n` Hamiltonian levels,
`n` extraction levels, and their total. -/
theorem clause14_route_ledger (m n prepareGates : ℕ) :
    (dilationRouteLedger m n prepareGates).prepareGates = prepareGates ∧
      (dilationRouteLedger m n prepareGates).hamiltonianLevels = dilationSize m n ∧
      (dilationRouteLedger m n prepareGates).extractionLevels = n ∧
      (dilationRouteLedger m n prepareGates).totalGates
        = prepareGates + dilationSize m n + n := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

/-- The total dilation route count is monotone in both dimensions and the preparation count. -/
theorem clause14_route_ledger_mono (m m' n n' p p' : ℕ) (hm : m ≤ m') (hn : n ≤ n') (hp : p ≤ p') :
    (dilationRouteLedger m n p).totalGates ≤ (dilationRouteLedger m' n' p').totalGates := by
  simp only [dilationRouteLedger, dilationSize]
  omega

/-- Collects dilation size and resource counts, monotonicity, solution-block extraction, the
residual decomposition, and zero-overlap properties [HarrowHassidimLloyd2009]. -/
theorem clause55_endpoint :

    (∀ m n : ℕ, dilationSize m n = m + n) ∧
    (∀ m n p : ℕ,
      (dilationRouteLedger m n p).prepareGates = p ∧
        (dilationRouteLedger m n p).hamiltonianLevels = dilationSize m n ∧
        (dilationRouteLedger m n p).extractionLevels = n ∧
        (dilationRouteLedger m n p).totalGates = p + dilationSize m n + n) ∧
    (∀ m m' n n' p p' : ℕ, m ≤ m' → n ≤ n' → p ≤ p' →
      (dilationRouteLedger m n p).totalGates ≤ (dilationRouteLedger m' n' p').totalGates) ∧

    (∀ (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
      (A : Matrix O I ℂ) (b : QState O),
      dilationSolutionBlock (matrixPseudoinverse (Qatlib.Concepts.QlsReadoutSpec.RectDilation.hermitianDilation A) *ᵥ Qatlib.Concepts.QlsReadoutSpec.RectDilation.dilationInput b)
        = leastSquaresVector A b) ∧

    (∀ (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
      (x : QState (O ⊕ I)),
      (∑ i : I, ‖(dilationSolutionBlock x) i‖ ^ 2)
        ≤ (∑ i : I, ‖x (Sum.inr i)‖ ^ 2) + (∑ o : O, ‖x (Sum.inl o)‖ ^ 2)) ∧

    (∀ (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
      (A : Matrix O I ℂ) (b : QState O),
      ‖stateVector b‖ ^ 2 = (leastSquaresOverlap A b) ^ 2 +
        ‖stateVector (A *ᵥ leastSquaresVector A b - b)‖ ^ 2) ∧

    (∀ (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
      (A : Matrix O I ℂ) (b : QState O),
      (leastSquaresOverlap A b = 0 ↔ leastSquaresVector A b = 0) ∧
        (leastSquaresVector A b = 0 → leastSquaresDirection A b = none) ∧
        (leastSquaresOverlap A b = 0 →
          ‖stateVector (A *ᵥ leastSquaresVector A b - b)‖ = ‖stateVector b‖)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m n
    rfl
  · intro m n p
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl
  · intro m m' n n' p p' hm hn hp
    exact clause14_route_ledger_mono m m' n n' p p' hm hn hp
  · intro O I _ _ _ _ A b
    exact clause14_solution_block_roundtrip A b
  · intro O I _ _ _ _ x
    exact clause14_extraction_contraction x
  · intro O I _ _ _ _ A b
    exact clause14_residual_budget A b
  · intro O I _ _ _ _ A b
    exact ⟨clause14_zero_overlap_iff A b, fun h => clause14_zero_overlap_direction A b h,
      fun h => clause14_zero_overlap_residual A b h⟩

end Clause14

section Clause16

/-- The canonical signed filter has the same squared flag mass as the unsigned filter evaluated
at the absolute spectral parameter. -/
theorem clause16_signed_flag_mass_eq_unsigned (d θ : ℝ) :
    canonicalSignedFilter.filterF d θ ^ 2 + canonicalSignedFilter.filterG d θ ^ 2
      = sinEnvelopeFilterF d |θ| ^ 2 + sinEnvelopeFilterG d |θ| ^ 2 := by
  have hf : canonicalSignedFilter.filterF d θ
      = (if θ < 0 then -1 else 1) * sinEnvelopeFilterF d |θ| := by
    simp [canonicalSignedFilter]
  have hg : canonicalSignedFilter.filterG d θ = sinEnvelopeFilterG d |θ| := by
    simp [canonicalSignedFilter]
  rw [hf, hg]
  by_cases hθ : θ < 0 <;> simp [hθ] <;> ring

/-- The squared flag mass of the canonical signed filter is even in the spectral parameter. -/
theorem clause16_signed_kernel_even (d θ : ℝ) :
    canonicalSignedFilter.filterF d θ ^ 2 + canonicalSignedFilter.filterG d θ ^ 2
      = canonicalSignedFilter.filterF d (-θ) ^ 2 + canonicalSignedFilter.filterG d (-θ) ^ 2 := by
  have hf : ∀ x : ℝ, canonicalSignedFilter.filterF d x
      = (if x < 0 then -1 else 1) * sinEnvelopeFilterF d |x| := by
    intro x
    simp [canonicalSignedFilter]
  have hg : ∀ x : ℝ, canonicalSignedFilter.filterG d x = sinEnvelopeFilterG d |x| := by
    intro x
    simp [canonicalSignedFilter]
  rw [hf, hg, hf, hg, abs_neg]
  by_cases hθ : θ < 0
  · by_cases hneg : -θ < 0
    · rw [if_pos hθ, if_pos hneg]
    · rw [if_pos hθ, if_neg hneg]
      ring
  · by_cases hneg : -θ < 0
    · rw [if_neg hθ, if_pos hneg]
      ring
    · rw [if_neg hθ, if_neg hneg]

/-- Each diagonal entry of the signed well-phase matrix has complex norm one. -/
theorem clause16_sign_phase_columns (θ : ℝ) (i : Fin 3) : ‖signedWellPhase θ i i‖ = 1 := by
  by_cases h : i = 1 ∧ θ < 0
  · simp [signedWellPhase, h]
  · simp [signedWellPhase, h]

/-- The first-order signed-filter budget is `C / (d * M)`. -/
theorem clause16_first_order_budget (C d M : ℝ) :
    signedFirstOrderBudget C d M = C / (d * M) := rfl

/-- The first-order signed-filter budget is positive when `C`, `d`, and `M` are positive. -/
theorem clause16_first_order_budget_pos (C d M : ℝ) (hC : 0 < C) (hd : 0 < d) (hM : 0 < M) :
    0 < signedFirstOrderBudget C d M := by
  unfold signedFirstOrderBudget
  positivity

/-- For positive parameters, increasing `d` decreases the first-order signed-filter budget. -/
theorem clause16_first_order_budget_mono (C d d' M : ℝ) (hC : 0 < C) (hd : 0 < d) (hd' : 0 < d')
    (h : d ≤ d') (hM : 0 < M) :
    signedFirstOrderBudget C d' M ≤ signedFirstOrderBudget C d M := by
  have h1 : (1 : ℝ) / d' ≤ 1 / d := by
    rw [one_div, one_div]
    exact (inv_le_inv₀ hd' hd).2 h
  have hcM : 0 ≤ C / M := by positivity
  have h2 : C / (d' * M) ≤ C / (d * M) := by
    have h2a : C / (d' * M) = (C / M) * (1 / d') := by field_simp
    have h2b : C / (d * M) = (C / M) * (1 / d) := by field_simp
    rw [h2a, h2b]
    exact mul_le_mul_of_nonneg_left h1 hcM
  unfold signedFirstOrderBudget
  exact h2

/-- The signed error budget is the sum of the first-order term, `32 / 2^k`, and `2 * (M - 1) *
δ`. -/
theorem clause16_error_budget_sum (C d M : ℝ) (k : ℕ) (δ : ℝ) :
    signedErrorBudget C d M k δ
      = signedFirstOrderBudget C d M + 32 / 2 ^ k + 2 * (M - 1) * δ := rfl

/-- Zero least-squares overlap prevents a nonnegative signed error budget from being strictly
less than `d` times that overlap. -/
theorem clause16_zero_overlap_blocks_success {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (b : QState O) (C d M : ℝ) (k : ℕ) (δ : ℝ)
    (hτ : leastSquaresOverlap A b = 0) (hE : 0 ≤ signedErrorBudget C d M k δ) :
    ¬ (signedErrorBudget C d M k δ < d * leastSquaresOverlap A b) := by
  rw [hτ, mul_zero]
  linarith

/-- Post-measurement conditioning on an event of positive measurement probability yields a
normalized state. -/
theorem clause16_normalized_well_target {I : Type} [Fintype I] [DecidableEq I]
    (ψ : QState I) (S : Finset I) (h : 0 < MeasureProb ψ S) : Normalized (PostMeasure ψ S) :=
  normalized_postMeasure h

/-- Collects signed-filter mass symmetry, unit phase norms, first-order and total budget
properties, the zero-overlap obstruction, and normalization after positive-probability
conditioning. -/
theorem clause60_endpoint :

    (∀ d θ : ℝ,
      canonicalSignedFilter.filterF d θ ^ 2 + canonicalSignedFilter.filterG d θ ^ 2
        = sinEnvelopeFilterF d |θ| ^ 2 + sinEnvelopeFilterG d |θ| ^ 2) ∧
    (∀ d θ : ℝ,
      canonicalSignedFilter.filterF d θ ^ 2 + canonicalSignedFilter.filterG d θ ^ 2
        = canonicalSignedFilter.filterF d (-θ) ^ 2 + canonicalSignedFilter.filterG d (-θ) ^ 2) ∧

    (∀ θ : ℝ, ∀ i : Fin 3, ‖signedWellPhase θ i i‖ = 1) ∧

    (∀ C d M : ℝ, signedFirstOrderBudget C d M = C / (d * M)) ∧
    (∀ C d M : ℝ, 0 < C → 0 < d → 0 < M → 0 < signedFirstOrderBudget C d M) ∧
    (∀ C d d' M : ℝ, 0 < C → 0 < d → 0 < d' → d ≤ d' → 0 < M →
      signedFirstOrderBudget C d' M ≤ signedFirstOrderBudget C d M) ∧
    (∀ C d M : ℝ, ∀ k : ℕ, ∀ δ : ℝ,
      signedErrorBudget C d M k δ
        = signedFirstOrderBudget C d M + 32 / 2 ^ k + 2 * (M - 1) * δ) ∧

    (∀ (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
      (A : Matrix O I ℂ) (b : QState O) (C d M : ℝ) (k : ℕ) (δ : ℝ),
      leastSquaresOverlap A b = 0 → 0 ≤ signedErrorBudget C d M k δ →
        ¬ (signedErrorBudget C d M k δ < d * leastSquaresOverlap A b)) ∧

    (∀ (I : Type) [Fintype I] [DecidableEq I] (ψ : QState I) (S : Finset I),
      0 < MeasureProb ψ S → Normalized (PostMeasure ψ S)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d θ
    exact clause16_signed_flag_mass_eq_unsigned d θ
  · intro d θ
    exact clause16_signed_kernel_even d θ
  · intro θ i
    exact clause16_sign_phase_columns θ i
  · intro C d M
    exact clause16_first_order_budget C d M
  · intro C d M hC hd hM
    exact clause16_first_order_budget_pos C d M hC hd hM
  · intro C d d' M hC hd hd' h hM
    exact clause16_first_order_budget_mono C d d' M hC hd hd' h hM
  · intro C d M k δ
    exact clause16_error_budget_sum C d M k δ
  · intro O I _ _ _ _ A b C d M k δ hτ hE
    exact clause16_zero_overlap_blocks_success A b C d M k δ hτ hE
  · intro I _ _ ψ S h
    exact clause16_normalized_well_target ψ S h

end Clause16

end Qatlib.Papers.LinearSystems09.InputModel.QlsHhlRefined
