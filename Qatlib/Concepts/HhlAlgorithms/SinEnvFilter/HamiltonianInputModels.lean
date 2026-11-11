/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.PureToMixedConditional
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.HamiltonianInputModelsDefs
import Qatlib.Concepts.QlsReadoutSpec.RectDilation
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef

/-!
# HHL input-model and budget witnesses

The `clause20` results construct records satisfying the stated three-state filter,
kernel-budget, and dyadic-quantization specifications, and verify the explicit backend and
uniform-grid formulas. `clause21` packages pure-to-mixed transport, successor budget records,
instrument-access accounting, and a normalized-vector perturbation bound for the HHL setting of
[HarrowHassidimLloyd2009].

## Main statements

* `clause20_qpeKernel`: a kernel record satisfies the defined accuracy and query-budget
  conditions.
* `clause20_realInputQuantization`: signed dyadic rounding gives the requested precision.
* `clause21`: transport, budget, access, and normalization guarantees.

## References

* [Harrow et al., 2009][HarrowHassidimLloyd2009]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL
open Qatlib.Concepts.HhlErrorBridge.FilterStability
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.HhlAlgorithms.Postselection
open Qatlib.Concepts.HhlAlgorithms.UniformHHL
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.BlockEncoding.Postselection

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter

open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical Matrix.Norms.L2Operator ComplexOrder

/-- Packages pure-to-mixed branch guarantees, positivity of the reduced success gap, existence
of successor budget records, instrument-access counts, and the normalization perturbation
estimate. -/
theorem clause21 :

  (∀ (O : Type) [Fintype O] (D E : ℕ) (J K : Instrument O D E)
      (S : Finset O) (e g : ℝ),
    PureUniformBranchBound J K S e g → 2 * e < g →
    ∃ G : MixedChannelGuarantee D E,
      G = transportPureToMixed e g ∧
        G.successGap = g - e ∧
        G.directionError = 2 * e / (g - e) ∧
        G.Holds J K S) ∧

  (∀ (e g : ℝ), 0 ≤ e → 0 < g → 2 * e < g →
    0 < g - e ∧ 0 ≤ 2 * e / (g - e) ∧ 2 * e / (g - e) < 2 ∧ (g - e) + e = g) ∧

  (∀ (d θ : ℚ) (calls bits k : ℕ),
    0 < d → 0 < θ → (d : ℝ) ≤ 1 / 4 → (θ : ℝ) ≤ 1 →
    ∃ B : SuccessorProgramBudget,
      B.Realizes calls bits k ∧
        B.successGap = successorSuccessGap d θ ∧
        B.tightParam = (successorTightParam d θ k : ℝ)) ∧

  (∀ (calls : ℕ),
    (instrumentAccessBudget calls).measurementAccesses = calls ∧
      (instrumentAccessBudget calls).preparationAccesses = calls + 1 ∧
      (instrumentAccessBudget calls).inverseAccesses = calls) ∧

  (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (x y : E) (η : ℝ),
    ‖y - x‖ ≤ η → η < ‖x‖ →
      y ≠ 0 ∧ ‖NormedSpace.normalize y - NormedSpace.normalize x‖ ≤ 2 * η / ‖x‖)
 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro O _ D E J K S e g hb h2
    exact ⟨transportPureToMixed e g, rfl, rfl, rfl, pureToMixed_holds J K S e g hb h2⟩
  · intro e g he hg h2
    have hg0 : 0 < g - e := by linarith
    have hdiv : 0 ≤ 2 * e / (g - e) := by
      apply div_nonneg <;> linarith
    have hlt : 2 * e / (g - e) < 2 := by
      have hge : 0 < g - e := by linarith
      rw [div_lt_iff₀ hge]
      linarith
    exact ⟨hg0, hdiv, hlt, by linarith⟩
  · intro d θ calls bits k hd hθ hdle hθle
    have hd0 : 0 < (d : ℝ) := by exact_mod_cast hd
    have hθ0 : 0 < (θ : ℝ) := by exact_mod_cast hθ
    have hbase : 0 < (d : ℝ) * (θ : ℝ) / 2 := by
      apply div_pos
      · exact mul_pos hd0 hθ0
      · norm_num
    have hgap : 0 < successorSuccessGap (d : ℝ) (θ : ℝ) := by
      show 0 < (((d : ℝ) * (θ : ℝ)) / 2) ^ 2
      exact pow_pos hbase 2
    have hprod : (d : ℝ) * (θ : ℝ) ≤ 1 / 4 := by
      have h := mul_le_mul hdle hθle (le_of_lt hθ0) (by norm_num : (0 : ℝ) ≤ 1 / 4)
      simpa using! h
    have hg1 : successorSuccessGap (d : ℝ) (θ : ℝ) ≤ 1 := by
      show (((d : ℝ) * (θ : ℝ)) / 2) ^ 2 ≤ 1
      have hx : (d : ℝ) * (θ : ℝ) / 2 ≤ 1 / 2 := by
        have h1 : (d : ℝ) * (θ : ℝ) ≤ 1 := by
          have := mul_le_mul hdle hθle (le_of_lt hθ0) (by norm_num : (0 : ℝ) ≤ 1 / 4)
          have h14 : ((1 / 4 : ℝ) * 1) = 1 / 4 := by norm_num
          rw [h14] at this
          have h41 : (1 / 4 : ℝ) ≤ 1 := by norm_num
          exact le_trans this h41
        have h2 := div_le_div_of_nonneg_right h1 (by norm_num : (0 : ℝ) ≤ 2)
        simpa using! h2
      have hx0 : 0 ≤ (d : ℝ) * (θ : ℝ) / 2 := le_of_lt hbase
      have hsq : (((d : ℝ) * (θ : ℝ)) / 2) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
        pow_le_pow_left₀ hx0 hx 2
      have hhalf : ((1 / 2 : ℝ) ^ 2) = 1 / 4 := by norm_num
      rw [hhalf] at hsq
      have h41 : (1 / 4 : ℝ) ≤ 1 := by norm_num
      exact le_trans hsq h41
    have htight : 0 < (successorTightParam d θ k : ℝ) := by
      have hq : 0 < successorTightParam d θ k := by
        show 0 < min 1 (d * θ * (1 / 2) ^ k / 8)
        refine lt_min (by norm_num) ?_
        apply div_pos
        · apply mul_pos
          · exact mul_pos hd hθ
          · exact pow_pos (by norm_num : (0 : ℚ) < 1 / 2) k
        · norm_num
      exact_mod_cast hq
    refine ⟨⟨successorSuccessGap (d : ℝ) (θ : ℝ), (successorTightParam d θ k : ℝ),
        instrumentAccessBudget calls, 0, 0⟩, ?_, rfl, rfl⟩
    show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
    exact ⟨hgap, hg1, htight, le_refl _, le_refl _, le_refl _,
      Nat.zero_le _, Nat.zero_le _⟩
  · intro calls
    exact ⟨rfl, rfl, rfl⟩
  · intro E _ _ x y η h1 h2
    exact Qatlib.Concepts.BlockEncoding.Postselection.normalize_error_of_gap h1 h2

/-- For valid gap and error parameters, there exists a `ThreeStateFilterRun` recording them, the
direction bound `2 * e / x`, and the stated mass and budget conditions. -/
theorem clause20_threeStateFilterRun :
  (∀ (d θ e x : ℝ) (bits k : ℕ),
    0 < d → 0 ≤ e → 0 < x → e < x →
    ∃ run : ThreeStateFilterRun,
      run.gap = d ∧ run.phase = θ ∧ run.filterError = e ∧ run.targetNorm = x ∧
        run.directionError = threeStateDirectionBound e x ∧
        run.Realizes bits k) := by
  intro d θ e x bits k hd he hx hex
  refine ⟨⟨d, θ, e, x, threeStateDirectionBound e x, 0, 0⟩,
    rfl, rfl, rfl, rfl, rfl, ?_⟩
  show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  refine ⟨hd, he, hx, hex, ?_, rfl, Nat.zero_le _, Nat.zero_le _⟩
  show threeStateSelectedMass d θ = threeStateWellMass d θ + threeStateIllMass d θ
  simp [threeStateSelectedMass, threeStateWellMass, threeStateIllMass,
    sinEnvelopeFlagMass]

/-- Under the positive gap and precision assumptions, the accuracy and query formulas hold and
there exists a `QpeKernelProgram` satisfying `SolvesAt` with exactly those values. -/
theorem clause20_qpeKernel :
  (∀ (d : ℝ) (k : ℕ),
    0 < d → d ≤ 1 / 4 → 1 ≤ k →
    uniformHHLAccuracy d k = min (d / 2) ((1 / 2 : ℝ) ^ k) ∧
      nearOptimalKernelQueries d k = (Nat.ceil (1 / d)) * (8 * k + 16) ∧
      0 < nearOptimalKernelQueries d k ∧
      ∃ K : QpeKernelProgram, K.SolvesAt d k ∧
        K.queryBudget = nearOptimalKernelQueries d k ∧
        K.accuracy = uniformHHLAccuracy d k) := by
  intro d k hd hdk hk
  have hceil : 0 < Nat.ceil (1 / d) := by
    refine Nat.ceil_pos.2 ?_
    exact one_div_pos.2 hd
  have hcoef : 0 < 8 * k + 16 := by omega
  have hacc : 0 < uniformHHLAccuracy d k := by
    show 0 < min (d / 2) ((1 / 2 : ℝ) ^ k)
    exact lt_min (div_pos hd two_pos) (pow_pos (by norm_num) k)
  refine ⟨rfl, rfl, Nat.mul_pos hceil hcoef, ?_⟩
  refine ⟨⟨2, nearOptimalKernelQueries d k, uniformHHLAccuracy d k⟩, ?_, rfl, rfl⟩
  show _ ∧ _ ∧ _ ∧ _
  exact ⟨le_refl 2, hacc, le_refl _, le_refl _⟩

/-- For `0 < d ≤ 1 / 4` and `k ≥ 1`, the defined near-optimal kernel query budget is strictly
smaller than the uniform HHL grid size. -/
theorem clause20_nearOptimalBelowUniformGrid :
  (∀ (d : ℝ) (k : ℕ),
    0 < d → d ≤ 1 / 4 → 1 ≤ k →
    nearOptimalKernelQueries d k < uniformHHLGrid d k) := by
  intro d k hd hdk hk
  have haccE : uniformHHLAccuracy d k = min (d / 2) ((1 / 2 : ℝ) ^ k) := rfl
  have hacc0 : 0 < uniformHHLAccuracy d k := by
    rw [haccE]
    exact lt_min (div_pos hd two_pos) (pow_pos (by norm_num) k)
  have hacc_le : uniformHHLAccuracy d k ≤ (1 / 2 : ℝ) ^ k := by
    rw [haccE]
    exact min_le_right _ _
  have h1d : 0 < 1 / d := one_div_pos.2 hd
  have h1d_le : 1 ≤ 1 / d := (one_le_div hd).mpr (by linarith)
  have hceil : (Nat.ceil (1 / d) : ℝ) < 2 / d := by
    have h1 : (Nat.ceil (1 / d) : ℝ) < 1 / d + 1 := Nat.ceil_lt_add_one (le_of_lt h1d)
    have h2 : (1 / d : ℝ) + 1 ≤ 1 / d + 1 / d := by nlinarith [h1d_le]
    have h3 : (1 / d : ℝ) + 1 / d = 2 / d := by ring
    linarith
  have hcoef : (8 * (k : ℝ) + 16) ≤ 24 * k := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hmain : ((nearOptimalKernelQueries d k : ℕ) : ℝ) < 48 * k / d := by
    change ((Nat.ceil (1 / d) * (8 * k + 16) : ℕ) : ℝ) < _
    push_cast
    have h8 : 0 < (8 * (k : ℝ) + 16) := by nlinarith
    calc (Nat.ceil (1 / d) : ℝ) * (8 * k + 16)
        < (2 / d) * (8 * k + 16) := mul_lt_mul_of_pos_right hceil h8
      _ ≤ (2 / d) * (24 * k) := mul_le_mul_of_nonneg_left hcoef
        (le_of_lt (div_pos two_pos hd))
      _ = 48 * k / d := by field_simp; ring
  have hk2 : (k : ℝ) ≤ 2 ^ k := by
    exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
  have hd1 : (d : ℝ) ≤ 1 := by linarith
  have hacc4 : uniformHHLAccuracy d k ^ 4 ≤ ((1 / 2 : ℝ) ^ k) ^ 4 :=
    pow_le_pow_left₀ (le_of_lt hacc0) hacc_le 4
  have hbase : (2 : ℝ) ^ k * (((1 / 2 : ℝ) ^ k) ^ 4) = (1 / 8) ^ k := by
    have h4 : (((1 / 2 : ℝ) ^ k) ^ 4) = ((1 / 2 : ℝ) ^ 4) ^ k := by
      rw [← pow_mul, mul_comm, pow_mul]
    rw [h4, ← mul_pow]
    norm_num
  have hkpow : (k : ℝ) * d * uniformHHLAccuracy d k ^ 4 ≤ 1 / 8 := by
    have hkd : (k : ℝ) * d ≤ 2 ^ k * 1 := by nlinarith [hk2, hd1]
    have hmul : (k : ℝ) * d * uniformHHLAccuracy d k ^ 4 ≤
        2 ^ k * (((1 / 2 : ℝ) ^ k) ^ 4) := by
      have h1 : (k : ℝ) * d ≤ 2 ^ k := by nlinarith [hkd]
      exact mul_le_mul h1 hacc4 (le_of_lt (pow_pos hacc0 4)) (by positivity)
    have hmono : ((1 / 8 : ℝ) ^ k) ≤ (1 / 8) ^ 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega : (1 : ℕ) ≤ k)
    calc (k : ℝ) * d * uniformHHLAccuracy d k ^ 4
        ≤ 2 ^ k * (((1 / 2 : ℝ) ^ k) ^ 4) := hmul
      _ = (1 / 8) ^ k := hbase
      _ ≤ (1 / 8) ^ 1 := hmono
      _ = 1 / 8 := by norm_num
  have hkey : (48 * (k : ℝ) / d) < 4096 / (d ^ 2 * uniformHHLAccuracy d k ^ 4) := by
    have hpow : 0 < (d : ℝ) ^ 2 * uniformHHLAccuracy d k ^ 4 :=
      mul_pos (pow_pos hd 2) (pow_pos hacc0 4)
    refine (div_lt_div_iff₀ hd hpow).mpr ?_
    calc 48 * (k : ℝ) * (d ^ 2 * uniformHHLAccuracy d k ^ 4)
        = 48 * (k * d * uniformHHLAccuracy d k ^ 4) * d := by ring
      _ ≤ 48 * (1 / 8) * d := by nlinarith [hkpow, le_refl (0 : ℝ)]
      _ = 6 * d := by ring
      _ < 4096 * d := by nlinarith [hd]
  have hreal : ((nearOptimalKernelQueries d k : ℕ) : ℝ) < (uniformHHLGrid d k : ℝ) :=
    lt_of_lt_of_le (lt_of_lt_of_le hmain (le_of_lt hkey)) (uniformHHLGrid_budget d k)
  exact_mod_cast hreal

/-- For positive precision `k`, there exists a dyadic quantizer with `k` digits whose rounded
output is within `(1 / 2)^k` of the input. -/
theorem clause20_realInputQuantization :
  (∀ (x : ℝ) (k : ℕ),
    0 < k →
    ∃ (Q : RealInputQuantizer) (y : ℝ),
      Q.digits = k ∧ Q.QuantizesAt x y ∧ |y - x| ≤ (1 / 2 : ℝ) ^ k) := by
  intro x k hk
  refine ⟨⟨k⟩, dyadicRound x k, rfl, ?_, ?_⟩
  · show dyadicRound x k = dyadicRound x k ∧ 0 < k
    exact ⟨rfl, hk⟩
  · show |dyadicRound x k - x| ≤ (1 / 2 : ℝ) ^ k
    unfold dyadicRound
    have hpow : (0 : ℝ) < 2 ^ k := pow_pos two_pos k
    have hstep : ((Int.floor (2 ^ k * x) : ℝ) / 2 ^ k) - x =
        ((Int.floor (2 ^ k * x) : ℝ) - 2 ^ k * x) / 2 ^ k := by
      field_simp [ne_of_gt hpow]
    have hle : (Int.floor (2 ^ k * x) : ℝ) ≤ 2 ^ k * x := Int.floor_le _
    have hlt : (2 : ℝ) ^ k * x < (Int.floor (2 ^ k * x) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    have habs : |((Int.floor (2 ^ k * x) : ℝ) / 2 ^ k) - x| =
        |(Int.floor (2 ^ k * x) : ℝ) - 2 ^ k * x| / 2 ^ k := by
      rw [hstep, abs_div, abs_of_pos hpow]
    have hzabs : |(Int.floor (2 ^ k * x) : ℝ) - 2 ^ k * x| ≤ 1 := by
      have : |(Int.floor (2 ^ k * x) : ℝ) - 2 ^ k * x| =
          2 ^ k * x - (Int.floor (2 ^ k * x) : ℝ) := by
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      rw [this]
      linarith
    have hbound : |(Int.floor (2 ^ k * x) : ℝ) - 2 ^ k * x| / 2 ^ k ≤ 1 / 2 ^ k :=
      div_le_div_of_nonneg_right hzabs (le_of_lt hpow)
    have hpow2 : ((1 / 2 : ℝ) ^ k) = 1 / 2 ^ k := by
      rw [div_pow, one_pow]
    rw [habs, hpow2]
    exact hbound

/-- The explicit HHL backend budget has the stated gate, integer-bit, and peak-space formulas,
and all three counts are positive. -/
theorem clause20_backendLedger :
  (∀ (wires bits k : ℕ),
    (hhlBackendBudget wires bits k).elementaryGates
        = 256 * (wires + 1) ^ 2 * 4 ^ wires * (bits + k + 2) ^ 8 ∧
      (hhlBackendBudget wires bits k).integerBits = (wires + 2) * (bits + k + 4) ∧
      (hhlBackendBudget wires bits k).peakSpaceBits = (wires + 2) * (bits + k + 4) ∧
      0 < (hhlBackendBudget wires bits k).elementaryGates ∧
      0 < (hhlBackendBudget wires bits k).integerBits ∧
      0 < (hhlBackendBudget wires bits k).peakSpaceBits) := by
  intro wires bits k
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
  · show 0 < 256 * (wires + 1) ^ 2 * 4 ^ wires * (bits + k + 2) ^ 8
    positivity
  · show 0 < (wires + 2) * (bits + k + 4)
    positivity
  · show 0 < (wires + 2) * (bits + k + 4)
    positivity

/-- The uniform HHL grid has size at least two and meets the bound `4096 / (d^2 *
uniformHHLAccuracy d k^4)`. -/
theorem clause20_uniformGridAccount :
  (∀ (d : ℝ) (k : ℕ),
    2 ≤ uniformHHLGrid d k ∧
      4096 / (d ^ 2 * uniformHHLAccuracy d k ^ 4) ≤ (uniformHHLGrid d k : ℝ)) := by
  intro d k
  exact ⟨uniformHHLGrid_ge_two d k, uniformHHLGrid_budget d k⟩

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
