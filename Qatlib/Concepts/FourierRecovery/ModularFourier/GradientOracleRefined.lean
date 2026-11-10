/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FourierRecovery.ModularFourier.GradientOracle
import Qatlib.Concepts.FourierRecovery.ModularFourier.GradientOracleRefinedDefs
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.HspRecovery.Reduction.GradientOracle
open Qatlib.Concepts.GradientOracle.ValueKickback
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.FourierRecovery.ModularFourier
open Qatlib.Concepts.FourierRecovery.ModularFourier.GradientOracle
open Qatlib.Concepts.FourierRecovery.ModularFourier.GradientSourceContinuation
open Qatlib.Concepts.SignalPrimitive.GridGradient

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.FourierRecovery.ModularFourier.GradientOracleRefined

open Qatlib
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexConjugate
set_option warningAsError false

theorem composed_value_to_gradient_success :
    ∀ (d M Q : ℕ) [NeZero Q] (hM : 0 < M) (hM2 : 2 ≤ M)
      (v : GradientGrid d M → ZMod Q) (φ : GradientGrid d M → ℝ)
      (g : Fin d → ℝ) (c w B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hw : 0 < w)
      (herror : ∀ x, ∃ k : ℤ, |gradientValuePhase Q v x - φ x - k| ≤ δ)
      (hlin : ∀ x, |φ x - (c + ∑ j : Fin d, g j * (x j).val)| ≤ B),
      MeasureProb (gradientReadout d M hM (gradientValuePhase Q v))
          (composedGoodWindow d M g w)
        ≥ 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B - 4 * Real.pi * δ := by
  intro d M Q _ hM hM2 v φ g c w B δ hB hδ hw herror hlin
  have h1 : MeasureProb (gradientReadout d M hM φ) (composedGoodWindow d M g w)
      ≥ 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B := by
    have h := Qatlib.Concepts.FourierRecovery.ModularFourier.GradientOracle.readout_joint_success
      d M hM g c w B φ hM2 hw hB hlin
    simpa only [composedGoodWindow] using! h
  have h2 := Qatlib.Concepts.FourierRecovery.ModularFourier.GradientOracle.value_phase_readout_event_error
    d M Q hM v φ δ hδ herror (composedGoodWindow d M g w)
  have h3 : MeasureProb (gradientReadout d M hM (gradientValuePhase Q v)) (composedGoodWindow d M g w)
      ≥ MeasureProb (gradientReadout d M hM φ) (composedGoodWindow d M g w) - 4 * Real.pi * δ := by
    have habs := abs_le.mp h2
    linarith
  calc MeasureProb (gradientReadout d M hM (gradientValuePhase Q v)) (composedGoodWindow d M g w)
      ≥ MeasureProb (gradientReadout d M hM φ) (composedGoodWindow d M g w) - 4 * Real.pi * δ := h3
    _ ≥ (1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B) - 4 * Real.pi * δ := by
        exact sub_le_sub_right h1 _
    _ = 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B - 4 * Real.pi * δ := by ring

theorem readout_guarantee_vacuous_boundary :
    ∀ (d M : ℕ) (hM : 0 < M) (g : Fin d → ℝ) (c w B : ℝ) (φ : GradientGrid d M → ℝ)
      (hM2 : 2 ≤ M) (hw : 0 < w) (hB : 0 ≤ B)
      (herror : ∀ x, |φ x - (c + ∑ j : Fin d, g j * (x j).val)| ≤ B),
      16 * (d : ℝ) / ((M : ℝ) * w) + 4 * Real.pi * B ≥ 1 →
        1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B ≤ 0 := by
  intro d M hM g c w B φ hM2 hw hB herror hsum
  have hrw : 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B
      = 1 - (16 * (d : ℝ) / ((M : ℝ) * w) + 4 * Real.pi * B) := by ring
  rw [hrw]
  have hle := sub_le_sub_left hsum 1
  simpa only [sub_self] using! hle

theorem composed_guarantee_vacuous_boundary :
    ∀ (d M Q : ℕ) [NeZero Q] (hM : 0 < M) (hM2 : 2 ≤ M)
      (v : GradientGrid d M → ZMod Q) (φ : GradientGrid d M → ℝ)
      (g : Fin d → ℝ) (c w B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hw : 0 < w)
      (herror : ∀ x, ∃ k : ℤ, |gradientValuePhase Q v x - φ x - k| ≤ δ)
      (hlin : ∀ x, |φ x - (c + ∑ j : Fin d, g j * (x j).val)| ≤ B),
      16 * (d : ℝ) / ((M : ℝ) * w) + 4 * Real.pi * B + 4 * Real.pi * δ ≥ 1 →
        1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B - 4 * Real.pi * δ ≤ 0 := by
  intro d M Q _ hM hM2 v φ g c w B δ hB hδ hw herror hlin hsum
  have hrw : 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B - 4 * Real.pi * δ
      = 1 - (16 * (d : ℝ) / ((M : ℝ) * w) + 4 * Real.pi * B + 4 * Real.pi * δ) := by ring
  rw [hrw]
  have hle := sub_le_sub_left hsum 1
  simpa only [sub_self] using! hle

theorem composed_guarantee_positive :
    ∀ (d M Q : ℕ) [NeZero Q] (hM : 0 < M) (hM2 : 2 ≤ M)
      (v : GradientGrid d M → ZMod Q) (φ : GradientGrid d M → ℝ)
      (g : Fin d → ℝ) (c w B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hw : 0 < w)
      (herror : ∀ x, ∃ k : ℤ, |gradientValuePhase Q v x - φ x - k| ≤ δ)
      (hlin : ∀ x, |φ x - (c + ∑ j : Fin d, g j * (x j).val)| ≤ B),
      16 * (d : ℝ) / ((M : ℝ) * w) < 1 - 4 * Real.pi * B - 4 * Real.pi * δ →
        0 < MeasureProb (gradientReadout d M hM (gradientValuePhase Q v))
          (composedGoodWindow d M g w) := by
  intro d M Q _ hM hM2 v φ g c w B δ hB hδ hw herror hlin hwin
  have hmain := composed_value_to_gradient_success d M Q hM hM2 v φ g c w B δ hB hδ hw
    herror hlin
  have hpos : 0 < (1 - 4 * Real.pi * B - 4 * Real.pi * δ)
      - 16 * (d : ℝ) / ((M : ℝ) * w) := by linarith
  calc 0 < (1 - 4 * Real.pi * B - 4 * Real.pi * δ)
        - 16 * (d : ℝ) / ((M : ℝ) * w) := hpos
    _ = 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B - 4 * Real.pi * δ := by ring
    _ ≤ MeasureProb (gradientReadout d M hM (gradientValuePhase Q v))
        (composedGoodWindow d M g w) := hmain

theorem composed_gradient_ledger (d M Q K k : ℕ) [NeZero Q] (hM : 0 < M) :
    adjointQueryCount (valueComputeKickbackUncomputeWord d M Q) = 2 ∧
      adjointGateCount (valueComputeKickbackUncomputeWord d M Q) = 1 ∧
      QueryCount (gradientWord d M) = 1 ∧
      GateCount (gradientWord d M) = 2 * d ∧
      readoutIntegerBits K k = K + k ∧
      readoutSpaceBits d M K k = d * Nat.clog 2 (max 2 M) + K + k := by
  obtain ⟨hW, hq, hg, _⟩ := value_compute_kickback_uncompute_resources d M Q
  obtain ⟨hbits, hspace, hq'', hg''⟩ :=
    Qatlib.Concepts.FourierRecovery.ModularFourier.GradientOracle.readout_backend_ledger d M K k hM
  exact ⟨hq, hg, hq'', hg'', hbits, hspace⟩

def ApproxRealRecord (k : ℕ) (θ : ℝ) : Prop :=
  ∃ n : ℤ, |θ * (2 : ℝ) ^ k - (n : ℝ)| ≤ 1 / 2

noncomputable def realRecordIndex (k : ℕ) (θ : ℝ) : ℤ := round (θ * (2 : ℝ) ^ k)

noncomputable def realRecord (k : ℕ) (θ : ℝ) : ℝ :=
  (realRecordIndex k θ : ℝ) / (2 : ℝ) ^ k

theorem realRecord_satisfies :
    ∀ (k : ℕ) (θ : ℝ), ApproxRealRecord k θ := by
  intro k θ
  exact ⟨realRecordIndex k θ, abs_sub_round _⟩

theorem realRecord_error :
    ∀ (k : ℕ) (θ : ℝ), |θ - realRecord k θ| ≤ (1 : ℝ) / (2 : ℝ) ^ (k + 1) := by
  intro k θ
  have hpow : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hpos : 0 < (2 : ℝ) ^ k := by positivity
  have hid : θ - realRecord k θ
      = (θ * (2 : ℝ) ^ k - (realRecordIndex k θ : ℝ)) / (2 : ℝ) ^ k := by
    simp only [realRecord]
    field_simp [hpow]
  rw [hid, abs_div, abs_of_pos hpos]
  calc
    _ ≤ (1 / 2) / (2 : ℝ) ^ k :=
        div_le_div_of_nonneg_right (abs_sub_round _) (by norm_num)
    _ = (1 : ℝ) / (2 : ℝ) ^ (k + 1) := by
      have hp : (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ k * 2 := by rw [pow_succ]
      rw [hp, div_div, mul_comm]

theorem realRecord_eq_of_exact :
    ∀ (k : ℕ) (θ : ℝ) (n : ℤ), θ = (n : ℝ) / (2 : ℝ) ^ k → realRecord k θ = θ := by
  intro k θ n hθ
  have hpow : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hmul : θ * (2 : ℝ) ^ k = (n : ℝ) := by
    rw [hθ]
    field_simp [hpow]
  have hround : realRecordIndex k θ = n := by
    rw [realRecordIndex, hmul, round_intCast]
  simp only [realRecord, hround]
  rw [hθ]

theorem realRecord_non_dyadic :
    ∀ (k : ℕ), ApproxRealRecord k (1 / 3) ∧ ¬ GeneralRealRecord 0 (1 / 3) := by
  intro k
  exact ⟨realRecord_satisfies k (1 / 3), non_dyadic_one_third.1⟩

theorem general_real_readout_event_error :
    ∀ (d M : ℕ) (hM : 0 < M) (φ θ : GradientGrid d M → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
      (herror : ∀ x, |φ x - θ x| ≤ ε) (S : Finset (GradientGrid d M)),
      |MeasureProb (gradientReadout d M hM φ) S -
        MeasureProb (gradientReadout d M hM θ) S| ≤ 4 * Real.pi * ε :=
  fun d M hM φ θ ε hε herror S =>
    gradient_actual_phase_event_error d M hM φ θ ε hε herror S

theorem general_real_record_readout_guarantee :
    ∀ (d M k : ℕ) (hM : 0 < M) (hM2 : 2 ≤ M) (g : Fin d → ℝ) (c w B : ℝ)
      (θ : GradientGrid d M → ℝ) (hw : 0 < w) (hB : 0 ≤ B)
      (hlin : ∀ x, |θ x - (c + ∑ j : Fin d, g j * (x j).val)| ≤ B),
      MeasureProb (gradientReadout d M hM (fun x => realRecord k (θ x)))
          (composedGoodWindow d M g w)
        ≥ 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B
          - 4 * Real.pi / (2 : ℝ) ^ (k + 1) := by
  intro d M k hM hM2 g c w B θ hw hB hlin
  have herror : ∀ x, |realRecord k (θ x) - θ x| ≤ (1 : ℝ) / (2 : ℝ) ^ (k + 1) :=
    fun x => by simpa only [abs_sub_comm] using! realRecord_error k (θ x)
  have hε : 0 ≤ (1 : ℝ) / (2 : ℝ) ^ (k + 1) := by positivity
  have h1 : MeasureProb (gradientReadout d M hM θ) (composedGoodWindow d M g w)
      ≥ 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B := by
    have h := Qatlib.Concepts.FourierRecovery.ModularFourier.GradientOracle.readout_joint_success
      d M hM g c w B θ hM2 hw hB hlin
    simpa only [composedGoodWindow] using! h
  have h2' : |MeasureProb (gradientReadout d M hM (fun x => realRecord k (θ x)))
        (composedGoodWindow d M g w) -
      MeasureProb (gradientReadout d M hM θ) (composedGoodWindow d M g w)|
      ≤ 4 * Real.pi / (2 : ℝ) ^ (k + 1) := by
    have h2 := gradient_actual_phase_event_error d M hM (fun x => realRecord k (θ x)) θ
      ((1 : ℝ) / (2 : ℝ) ^ (k + 1)) hε herror (composedGoodWindow d M g w)
    have he : 4 * Real.pi * ((1 : ℝ) / (2 : ℝ) ^ (k + 1))
        = 4 * Real.pi / (2 : ℝ) ^ (k + 1) := by
      rw [one_div, div_eq_mul_inv]
    rw [he] at h2
    exact h2
  have h3 : MeasureProb (gradientReadout d M hM (fun x => realRecord k (θ x)))
        (composedGoodWindow d M g w)
      ≥ MeasureProb (gradientReadout d M hM θ) (composedGoodWindow d M g w)
        - 4 * Real.pi / (2 : ℝ) ^ (k + 1) := by
    have habs := abs_le.mp h2'
    linarith
  calc MeasureProb (gradientReadout d M hM (fun x => realRecord k (θ x)))
        (composedGoodWindow d M g w)
      ≥ MeasureProb (gradientReadout d M hM θ) (composedGoodWindow d M g w)
          - 4 * Real.pi / (2 : ℝ) ^ (k + 1) := h3
    _ ≥ (1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B)
          - 4 * Real.pi / (2 : ℝ) ^ (k + 1) := by
        exact sub_le_sub_right h1 _
    _ = 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B
          - 4 * Real.pi / (2 : ℝ) ^ (k + 1) := by ring

section ProbabilityAccess

theorem probability_access_is_readout_phase_operator :
    ∀ (d M : ℕ) (p : GradientGrid d M → ℝ),
      probabilityPhaseOperator p = gradientPhase d M (probabilityReadoutPhase p) :=
  fun d M p => probability_phase_operator_eq_gradient_phase d M p

theorem probability_oracle_rotation_is_readout_phase_operator :
    ∀ {d M : ℕ} (o : ProbabilityOracle d M),
      probabilityOracleRotation o = gradientPhase d M (probabilityOraclePhase o) := by
  intro d M o
  exact probability_access_is_readout_phase_operator d M o.prob

theorem probability_rotation_operator_error :
    ∀ {X : Type} [Fintype X] [DecidableEq X] (p q : X → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
      (herror : ∀ x, |p x - q x| ≤ ε),
      ‖probabilityPhaseOperator p - probabilityPhaseOperator q‖ ≤ ε := by
  intro X _ _ p q ε hε herror
  rw [probabilityPhaseOperator, probabilityPhaseOperator, Matrix.diagonal_sub,
    Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg hε]
  intro z
  have he (t : ℝ) : (Complex.I * (t : ℂ)) = (t : ℂ) * Complex.I := by ring
  rw [he, he]
  calc
    _ ≤ |p z - q z| := norm_exp_mul_I_sub_le _ _
    _ ≤ ε := herror z

theorem probability_access_phase_error :
    ∀ {X : Type} [Fintype X] [DecidableEq X] (p q : X → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
      (herror : ∀ x, |p x - q x| ≤ ε) (x : X),
      |probabilityReadoutPhase p x - probabilityReadoutPhase q x| ≤ ε / (2 * Real.pi) := by
  intro X _ _ p q ε hε herror x
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hid : p x / (2 * Real.pi) - q x / (2 * Real.pi) = (p x - q x) / (2 * Real.pi) := by
    ring
  rw [probabilityReadoutPhase, probabilityReadoutPhase, hid, abs_div, abs_of_pos h2pi]
  have h1 : |p x - q x| / (2 * Real.pi) ≤ ε / (2 * Real.pi) :=
    div_le_div_of_nonneg_right (herror x) (by positivity)
  simpa only [abs_of_pos h2pi] using! h1

theorem probability_access_readout_transport :
    ∀ (d M : ℕ) (hM : 0 < M) (p q : GradientGrid d M → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
      (herror : ∀ x, |p x - q x| ≤ ε) (S : Finset (GradientGrid d M)),
      |MeasureProb (gradientReadout d M hM (probabilityReadoutPhase p)) S
          - MeasureProb (gradientReadout d M hM (probabilityReadoutPhase q)) S| ≤ 2 * ε := by
  intro d M hM p q ε hε herror S
  have hphase (x : GradientGrid d M) :
      |probabilityReadoutPhase p x - probabilityReadoutPhase q x| ≤ ε / (2 * Real.pi) :=
    probability_access_phase_error p q ε hε herror x
  have hB : 0 ≤ ε / (2 * Real.pi) := by positivity
  have h := gradient_actual_phase_event_error d M hM
    (probabilityReadoutPhase p) (probabilityReadoutPhase q) (ε / (2 * Real.pi)) hB hphase S
  have he : 4 * Real.pi * (ε / (2 * Real.pi)) = 2 * ε := by
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    calc 4 * Real.pi * (ε / (2 * Real.pi))
        = (4 * Real.pi * ε) / (2 * Real.pi) := by ring
      _ = 2 * ε := by
        rw [div_eq_iff (ne_of_gt hpi)]
        ring
  rw [he] at h
  exact h

theorem probability_access_composed_guarantee :
    ∀ (d M : ℕ) (hM : 0 < M) (hM2 : 2 ≤ M) (g : Fin d → ℝ) (c w B : ℝ) (hw : 0 < w)
      (hB : 0 ≤ B) (p q : GradientGrid d M → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
      (hlin : ∀ x, |probabilityReadoutPhase p x - (c + ∑ j : Fin d, g j * (x j).val)| ≤ B)
      (herror : ∀ x, |p x - q x| ≤ ε),
      MeasureProb (gradientReadout d M hM (probabilityReadoutPhase q))
          (composedGoodWindow d M g w)
        ≥ 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B - 2 * ε := by
  intro d M hM hM2 g c w B hw hB p q ε hε hlin herror
  have h1 : MeasureProb (gradientReadout d M hM (probabilityReadoutPhase p))
      (composedGoodWindow d M g w)
      ≥ 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B := by
    have h := Qatlib.Concepts.FourierRecovery.ModularFourier.GradientOracle.readout_joint_success
      d M hM g c w B (probabilityReadoutPhase p) hM2 hw hB hlin
    simpa only [composedGoodWindow] using! h
  have h2 := probability_access_readout_transport d M hM p q ε hε herror
    (composedGoodWindow d M g w)
  have h3 : MeasureProb (gradientReadout d M hM (probabilityReadoutPhase q))
      (composedGoodWindow d M g w)
      ≥ MeasureProb (gradientReadout d M hM (probabilityReadoutPhase p))
          (composedGoodWindow d M g w) - 2 * ε := by
    have habs := abs_le.mp h2
    linarith
  calc MeasureProb (gradientReadout d M hM (probabilityReadoutPhase q))
        (composedGoodWindow d M g w)
      ≥ MeasureProb (gradientReadout d M hM (probabilityReadoutPhase p))
          (composedGoodWindow d M g w) - 2 * ε := h3
    _ ≥ (1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B) - 2 * ε := by
        exact sub_le_sub_right h1 _
    _ = 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B - 2 * ε := by ring

theorem probability_access_guarantee_vacuous_boundary :
    ∀ (d M : ℕ) (hM : 0 < M) (hM2 : 2 ≤ M) (g : Fin d → ℝ) (c w B : ℝ) (hw : 0 < w)
      (hB : 0 ≤ B) (p q : GradientGrid d M → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
      (hlin : ∀ x, |probabilityReadoutPhase p x - (c + ∑ j : Fin d, g j * (x j).val)| ≤ B)
      (herror : ∀ x, |p x - q x| ≤ ε),
      16 * (d : ℝ) / ((M : ℝ) * w) + 4 * Real.pi * B + 2 * ε ≥ 1 →
        1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B - 2 * ε ≤ 0 := by
  intro d M hM hM2 g c w B hw hB p q ε hε hlin herror hsum
  have hrw : 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B - 2 * ε
      = 1 - (16 * (d : ℝ) / ((M : ℝ) * w) + 4 * Real.pi * B + 2 * ε) := by ring
  rw [hrw]
  have hle := sub_le_sub_left hsum 1
  simpa only [sub_self] using! hle

theorem probability_access_guarantee_positive :
    ∀ (d M : ℕ) (hM : 0 < M) (hM2 : 2 ≤ M) (g : Fin d → ℝ) (c w B : ℝ) (hw : 0 < w)
      (hB : 0 ≤ B) (p q : GradientGrid d M → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
      (hlin : ∀ x, |probabilityReadoutPhase p x - (c + ∑ j : Fin d, g j * (x j).val)| ≤ B)
      (herror : ∀ x, |p x - q x| ≤ ε),
      16 * (d : ℝ) / ((M : ℝ) * w) < 1 - 4 * Real.pi * B - 2 * ε →
        0 < MeasureProb (gradientReadout d M hM (probabilityReadoutPhase q))
          (composedGoodWindow d M g w) := by
  intro d M hM hM2 g c w B hw hB p q ε hε hlin herror hwin
  have hmain := probability_access_composed_guarantee d M hM hM2 g c w B hw hB p q ε hε
    hlin herror
  have hpos : 0 < (1 - 4 * Real.pi * B - 2 * ε)
      - 16 * (d : ℝ) / ((M : ℝ) * w) := by linarith
  calc 0 < (1 - 4 * Real.pi * B - 2 * ε)
        - 16 * (d : ℝ) / ((M : ℝ) * w) := hpos
    _ = 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B - 2 * ε := by ring
    _ ≤ MeasureProb (gradientReadout d M hM (probabilityReadoutPhase q))
        (composedGoodWindow d M g w) := hmain

theorem probability_access_ledger :
    ∀ (X A : Type) [Fintype X] [Fintype A] [DecidableEq X] [DecidableEq A]
      (U : Matrix (X × A) (X × A) ℂ) (hU : U ∈ Matrix.unitaryGroup (X × A) ℂ)
      (a₀ : A) (good : Finset A)
      (hlabel : ∀ (x y : X) (a : A), x ≠ y → U (x,a) (y,a₀) = 0) (k : ℕ) (d M : ℕ)
      (hM : 0 < M),
      adjointQueryCount (probabilityPhaseWord (X := X) a₀ good k) = 6912 * k + 110646 ∧
        adjointGateCount (probabilityPhaseWord (X := X) a₀ good k) = 6912 * k + 110861 ∧
        QueryCount (gradientWord d M) = 1 ∧
        GateCount (gradientWord d M) = 2 * d := by
  intro X A _ _ _ _ U hU a₀ good hlabel k d M hM
  obtain ⟨hq, hg⟩ := probability_phase_linear_resources U hU a₀ good hlabel k
  obtain ⟨-, hq2, hg2⟩ :=
    Qatlib.Concepts.FourierRecovery.ModularFourier.GradientSourceContinuation.clause3_readout_word_ledger d M hM
  exact ⟨hq, hg, hq2, hg2⟩

theorem probability_pipeline_ledger :
    ∀ (X A : Type) [Fintype X] [Fintype A] [DecidableEq X] [DecidableEq A]
      (U : Matrix (X × A) (X × A) ℂ) (hU : U ∈ Matrix.unitaryGroup (X × A) ℂ)
      (a₀ : A) (good : Finset A)
      (hlabel : ∀ (x y : X) (a : A), x ≠ y → U (x,a) (y,a₀) = 0) (k : ℕ) (d M : ℕ)
      (hM : 0 < M),
      adjointQueryCount (probabilityPhaseWord (X := X) a₀ good k)
          + (QueryCount (gradientWord d M) - 1) = 6912 * k + 110646 ∧
        adjointGateCount (probabilityPhaseWord (X := X) a₀ good k)
          + GateCount (gradientWord d M) = 6912 * k + 110861 + 2 * d := by
  intro X A _ _ _ _ U hU a₀ good hlabel k d M hM
  obtain ⟨hq, hg, hq2, hg2⟩ := probability_access_ledger X A U hU a₀ good hlabel k d M hM
  constructor
  · rw [hq, hq2]
  · rw [hg, hg2]

theorem probability_access_readout_is_program_phase :
    ∀ (d M : ℕ) (hM : 0 < M) (A : Type) [Fintype A] [DecidableEq A]
      (U : Matrix (GradientGrid d M × A) (GradientGrid d M × A) ℂ)
      (hU : U ∈ Matrix.unitaryGroup (GradientGrid d M × A) ℂ)
      (a₀ : A) (good : Finset A)
      (hlabel : ∀ (x y : GradientGrid d M) (a : A), x ≠ y → U (x,a) (y,a₀) = 0) (k : ℕ),
      gradientReadout d M hM (probabilityReadoutPhase (probabilityMass U a₀ good))
        = Run (probabilityPhaseOperator (probabilityMass U a₀ good)) (gradientWord d M)
            (Ket (gradientZero d M hM)) :=
  fun d M hM A _ _ U hU a₀ good hlabel k =>
    Qatlib.Concepts.FourierRecovery.ModularFourier.GradientOracle.probability_phase_readout_coincides
      d M hM (probabilityMass U a₀ good)

theorem probability_access_program_approximation :
    ∀ (X A : Type) [Fintype X] [Fintype A] [DecidableEq X] [DecidableEq A]
      (U : Matrix (X × A) (X × A) ℂ) (hU : U ∈ Matrix.unitaryGroup (X × A) ℂ)
      (a₀ : A) (good : Finset A)
      (hlabel : ∀ (x y : X) (a : A), x ≠ y → U (x,a) (y,a₀) = 0) (k : ℕ) (ψ : QState X),
      ‖toEuclidean_fromVec
          (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k) *ᵥ
              (scaleEightFrame (hamiltonianFrame (cleanFrame (X := X) a₀)) *ᵥ ψ) -
            scaleEightFrame (hamiltonianFrame (cleanFrame (X := X) a₀)) *ᵥ
              (probabilityPhaseOperator (probabilityMass U a₀ good) *ᵥ ψ))‖
        ≤ (1/2 : ℝ)^k * ‖toEuclidean_fromVec ψ‖ := by
  intro X A _ _ _ _ U hU a₀ good hlabel k ψ
  obtain ⟨-, -, -, h⟩ :=
    Qatlib.Concepts.FourierRecovery.ModularFourier.GradientOracle.probability_phase_frame_bound
      X A U hU a₀ good hlabel k
  exact h ψ

end ProbabilityAccess

theorem probability_program_frame_gram :
    ∀ (X A : Type) [Fintype X] [Fintype A] [DecidableEq X] [DecidableEq A] (a₀ : A),
      (probabilityProgramFrame (X := X) a₀)ᴴ * probabilityProgramFrame (X := X) a₀ = 1 := by
  intro X A _ _ _ _ a₀
  have h1 : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (averageFrame (cleanFrame (X := X) a₀)) := by
    exact averageFrame_isIsometry (cleanFrame_isometry a₀)
  have h2 : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry
      (averageFrame (averageFrame (cleanFrame (X := X) a₀))) := by
    exact averageFrame_isIsometry h1
  have h3 : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry
      (scaleEightFrame (hamiltonianFrame (cleanFrame (X := X) a₀))) := by
    exact scaleEightFrame_isometry _ h2
  exact h3

theorem probability_ket_eq_single {X : Type} [DecidableEq X] (x : X) :
    Qatlib.Foundations.PureStateMath.Ket x = Pi.single x 1 := by
  funext j
  by_cases h : j = x
  · subst h
    simp [Qatlib.Foundations.PureStateMath.Ket]
  · simp [Qatlib.Foundations.PureStateMath.Ket, Pi.single_apply, h]

theorem probability_mulVec_ket {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X]
    (F : Matrix Y X ℂ) (x : X) : F *ᵥ Qatlib.Foundations.PureStateMath.Ket x = fun i => F i x := by
  rw [probability_ket_eq_single, Matrix.mulVec_single_one]
  rfl

theorem probability_frame_diag_eq_inner {X Y : Type} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] (F : Matrix Y X ℂ) (M : Matrix Y X ℂ) (x : X) :
    (Fᴴ * M) x x = Qatlib.Foundations.PureStateMath.Inner (F *ᵥ Qatlib.Foundations.PureStateMath.Ket x) (M *ᵥ Qatlib.Foundations.PureStateMath.Ket x) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply]
  rw [inner_apply, probability_mulVec_ket, probability_mulVec_ket]
  simp only [starRingEnd_apply]

theorem probability_frame_diag_error_le {X Y : Type} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] {F : Matrix Y X ℂ} (hF : Fᴴ * F = 1)
    (D : Matrix Y X ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hop : ∀ ψ : QState X, ‖toEuclidean_fromVec (D *ᵥ ψ)‖ ≤ δ * ‖toEuclidean_fromVec ψ‖)
    (x : X) : ‖(Fᴴ * D) x x‖ ≤ δ := by
  have hdiag : (Fᴴ * D) x x = Qatlib.Foundations.PureStateMath.Inner (F *ᵥ Qatlib.Foundations.PureStateMath.Ket x) (D *ᵥ Qatlib.Foundations.PureStateMath.Ket x) :=
    probability_frame_diag_eq_inner F D x
  have hcs : ‖Qatlib.Foundations.PureStateMath.Inner (F *ᵥ Qatlib.Foundations.PureStateMath.Ket x) (D *ᵥ Qatlib.Foundations.PureStateMath.Ket x)‖
      ≤ ‖toEuclidean_fromVec (F *ᵥ Qatlib.Foundations.PureStateMath.Ket x)‖
        * ‖toEuclidean_fromVec (D *ᵥ Qatlib.Foundations.PureStateMath.Ket x)‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) (toEuclidean_fromVec (F *ᵥ Qatlib.Foundations.PureStateMath.Ket x))
      (toEuclidean_fromVec (D *ᵥ Qatlib.Foundations.PureStateMath.Ket x))
    rw [inner_euclidean_fromVec] at h
    simpa using! h
  have hFcol : ‖toEuclidean_fromVec (F *ᵥ Qatlib.Foundations.PureStateMath.Ket x)‖ = 1 := by
    rw [isometry_mulVec_norm hF]
    exact (normalized_iff_norm_toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket x)).mp (normalized_ket x)
  have hDcol : ‖toEuclidean_fromVec (D *ᵥ Qatlib.Foundations.PureStateMath.Ket x)‖ ≤ δ := by
    have h := hop (Qatlib.Foundations.PureStateMath.Ket x)
    have hk : ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket x)‖ = 1 :=
      (normalized_iff_norm_toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket x)).mp (normalized_ket x)
    rw [hk] at h
    simpa using! h
  rw [hdiag]
  calc ‖Qatlib.Foundations.PureStateMath.Inner (F *ᵥ Qatlib.Foundations.PureStateMath.Ket x) (D *ᵥ Qatlib.Foundations.PureStateMath.Ket x)‖
      ≤ ‖toEuclidean_fromVec (F *ᵥ Qatlib.Foundations.PureStateMath.Ket x)‖
          * ‖toEuclidean_fromVec (D *ᵥ Qatlib.Foundations.PureStateMath.Ket x)‖ := hcs
    _ = 1 * ‖toEuclidean_fromVec (D *ᵥ Qatlib.Foundations.PureStateMath.Ket x)‖ := by rw [hFcol]
    _ ≤ 1 * δ := mul_le_mul_of_nonneg_left hDcol (by norm_num)
    _ = δ := by ring

theorem probability_frame_error_identity {X Y : Type} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] {F : Matrix Y X ℂ} (hF : Fᴴ * F = 1)
    (A : Matrix Y Y ℂ) (B : Matrix X X ℂ) :
    Fᴴ * (A * F - F * B) = Fᴴ * A * F - B := by
  calc Fᴴ * (A * F - F * B) = Fᴴ * (A * F) - Fᴴ * (F * B) :=
        Matrix.mul_sub Fᴴ (A * F) (F * B)
    _ = (Fᴴ * A) * F - Fᴴ * (F * B) := by rw [Matrix.mul_assoc]
    _ = (Fᴴ * A) * F - (Fᴴ * F) * B := by rw [← Matrix.mul_assoc]
    _ = (Fᴴ * A) * F - B := by rw [hF, Matrix.one_mul]

theorem probability_realized_phase_pointwise :
    ∀ (X A : Type) [Fintype X] [Fintype A] [DecidableEq X] [DecidableEq A]
      (U : Matrix (X × A) (X × A) ℂ) (hU : U ∈ Matrix.unitaryGroup (X × A) ℂ)
      (a₀ : A) (good : Finset A)
      (hlabel : ∀ (x y : X) (a : A), x ≠ y → U (x,a) (y,a₀) = 0) (k : ℕ) (x : X),
      ‖probabilityRealizedPhase (X := X) a₀
          (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x
        - Complex.exp (Complex.I * (probabilityMass U a₀ good x : ℂ))‖
      ≤ (1/2 : ℝ)^k := by
  intro X A _ _ _ _ U hU a₀ good hlabel k x
  have hgram : (probabilityProgramFrame (X := X) a₀)ᴴ
      * probabilityProgramFrame (X := X) a₀ = 1 :=
    probability_program_frame_gram X A a₀
  have hbound :=
    (Qatlib.Concepts.FourierRecovery.ModularFourier.GradientOracle.probability_phase_frame_bound
      X A U hU a₀ good hlabel k).2.2.2
  have hmul (ψ : QState X) :
      (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)
          * probabilityProgramFrame (X := X) a₀
          - probabilityProgramFrame (X := X) a₀
            * probabilityPhaseOperator (probabilityMass U a₀ good)) *ᵥ ψ
        = evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)
            *ᵥ (probabilityProgramFrame (X := X) a₀ *ᵥ ψ)
          - probabilityProgramFrame (X := X) a₀
            *ᵥ (probabilityPhaseOperator (probabilityMass U a₀ good) *ᵥ ψ) := by
    rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hop : ∀ ψ : QState X,
      ‖toEuclidean_fromVec
          ((evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)
              * probabilityProgramFrame (X := X) a₀
            - probabilityProgramFrame (X := X) a₀
              * probabilityPhaseOperator (probabilityMass U a₀ good)) *ᵥ ψ)‖
        ≤ (1/2 : ℝ)^k * ‖toEuclidean_fromVec ψ‖ := by
    intro ψ
    have h := hbound ψ
    have h' : ‖toEuclidean_fromVec
          (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)
              *ᵥ (probabilityProgramFrame (X := X) a₀ *ᵥ ψ)
            - probabilityProgramFrame (X := X) a₀
              *ᵥ (probabilityPhaseOperator (probabilityMass U a₀ good) *ᵥ ψ))‖
        ≤ (1/2 : ℝ)^k * ‖toEuclidean_fromVec ψ‖ := by
      simpa only [probabilityProgramFrame] using! h
    rw [← hmul] at h'
    exact h'
  have hdiag := probability_frame_diag_error_le hgram
    (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)
      * probabilityProgramFrame (X := X) a₀
      - probabilityProgramFrame (X := X) a₀
        * probabilityPhaseOperator (probabilityMass U a₀ good))
    ((1/2 : ℝ)^k) (by positivity) hop x
  have hstep :
      ((probabilityProgramFrame (X := X) a₀)ᴴ
          * evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)
          * probabilityProgramFrame (X := X) a₀) x x
          - probabilityPhaseOperator (probabilityMass U a₀ good) x x
        = ((probabilityProgramFrame (X := X) a₀)ᴴ
          * (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)
              * probabilityProgramFrame (X := X) a₀
            - probabilityProgramFrame (X := X) a₀
              * probabilityPhaseOperator (probabilityMass U a₀ good))) x x := by
    have h := congrArg (fun M : Matrix X X ℂ => M x x)
      (probability_frame_error_identity hgram
        (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k))
        (probabilityPhaseOperator (probabilityMass U a₀ good))).symm
    exact h
  have hBxx : probabilityPhaseOperator (probabilityMass U a₀ good) x x
      = Complex.exp (Complex.I * (probabilityMass U a₀ good x : ℂ)) := by
    simp only [probabilityPhaseOperator, Matrix.diagonal_apply_eq]
  show ‖probabilityRealizedPhase (X := X) a₀
        (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x
      - Complex.exp (Complex.I * (probabilityMass U a₀ good x : ℂ))‖ ≤ (1/2 : ℝ)^k
  rw [probabilityRealizedPhase, probabilityProgramFrameOperator, ← hBxx, hstep]
  exact hdiag

theorem probability_phase_coefficient_norm (t : ℝ) :
    ‖Complex.exp (Complex.I * (t : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (Complex.I * (t : ℂ)).re = 0 := by simp
  rw [hre, Real.exp_zero]

theorem probability_real_norm (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have hsq : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
    have h := Complex.conj_mul' (r : ℂ)
    rw [Complex.conj_ofReal] at h
    rw [← Complex.ofReal_mul r r] at h
    rw [← Complex.ofReal_pow] at h
    exact Complex.ofReal_inj.mp (by simpa only [pow_two] using! h.symm)
  have hnonneg : 0 ≤ ‖(r : ℂ)‖ := norm_nonneg _
  calc ‖(r : ℂ)‖ = Real.sqrt (‖(r : ℂ)‖ ^ 2) := (Real.sqrt_sq hnonneg).symm
    _ = Real.sqrt (r ^ 2) := by rw [hsq]
    _ = |r| := Real.sqrt_sq_eq_abs r

theorem probability_realized_phase_nonzero :
    ∀ (X A : Type) [Fintype X] [Fintype A] [DecidableEq X] [DecidableEq A]
      (U : Matrix (X × A) (X × A) ℂ) (hU : U ∈ Matrix.unitaryGroup (X × A) ℂ)
      (a₀ : A) (good : Finset A)
      (hlabel : ∀ (x y : X) (a : A), x ≠ y → U (x,a) (y,a₀) = 0) (k : ℕ) (hk : 1 ≤ k) (x : X),
      1 / 2 ≤ ‖probabilityRealizedPhase (X := X) a₀
          (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x‖ := by
  intro X A _ _ _ _ U hU a₀ good hlabel k hk x
  have h := probability_realized_phase_pointwise X A U hU a₀ good hlabel k x
  have hE : ‖Complex.exp (Complex.I * (probabilityMass U a₀ good x : ℂ))‖ = 1 :=
    probability_phase_coefficient_norm _
  have htri : ‖Complex.exp (Complex.I * (probabilityMass U a₀ good x : ℂ))‖
      ≤ ‖probabilityRealizedPhase (X := X) a₀
            (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x‖
        + ‖probabilityRealizedPhase (X := X) a₀
            (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x
            - Complex.exp (Complex.I * (probabilityMass U a₀ good x : ℂ))‖ := by
    calc ‖Complex.exp (Complex.I * (probabilityMass U a₀ good x : ℂ))‖
        = ‖probabilityRealizedPhase (X := X) a₀
              (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x
            + (Complex.exp (Complex.I * (probabilityMass U a₀ good x : ℂ))
              - probabilityRealizedPhase (X := X) a₀
                (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x)‖ := by
          have heq : probabilityRealizedPhase (X := X) a₀
                (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x
              + (Complex.exp (Complex.I * (probabilityMass U a₀ good x : ℂ))
                - probabilityRealizedPhase (X := X) a₀
                  (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x)
              = Complex.exp (Complex.I * (probabilityMass U a₀ good x : ℂ)) := by ring
          rw [heq]
      _ ≤ ‖probabilityRealizedPhase (X := X) a₀
              (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x‖
            + ‖Complex.exp (Complex.I * (probabilityMass U a₀ good x : ℂ))
              - probabilityRealizedPhase (X := X) a₀
                (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x‖ :=
            norm_add_le _ _
      _ = ‖probabilityRealizedPhase (X := X) a₀
              (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x‖
            + ‖probabilityRealizedPhase (X := X) a₀
              (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x
              - Complex.exp (Complex.I * (probabilityMass U a₀ good x : ℂ))‖ := by
          congr 1
          rw [show Complex.exp (Complex.I * (probabilityMass U a₀ good x : ℂ))
                - probabilityRealizedPhase (X := X) a₀
                  (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x
              = -(probabilityRealizedPhase (X := X) a₀
                  (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x
                - Complex.exp (Complex.I * (probabilityMass U a₀ good x : ℂ))) by ring, norm_neg]
  have hhalf : (1/2 : ℝ)^k ≤ 1/2 := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ]
    have h1 : (1/2 : ℝ)^m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc (1/2:ℝ)^m * (1/2) ≤ 1 * (1/2) := by gcongr
      _ = 1/2 := by ring
  rw [hE] at htri
  linarith

theorem probability_realized_phase_operator_dist :
    ∀ (X A : Type) [Fintype X] [Fintype A] [DecidableEq X] [DecidableEq A]
      (U : Matrix (X × A) (X × A) ℂ) (hU : U ∈ Matrix.unitaryGroup (X × A) ℂ)
      (a₀ : A) (good : Finset A)
      (hlabel : ∀ (x y : X) (a : A), x ≠ y → U (x,a) (y,a₀) = 0) (k : ℕ),
      ‖probabilityRealizedPhaseOperator (X := X) a₀
          (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k))
          - probabilityPhaseOperator (probabilityMass U a₀ good)‖
        ≤ (1/2 : ℝ)^k := by
  intro X A _ _ _ _ U hU a₀ good hlabel k
  rw [probabilityRealizedPhaseOperator, probabilityPhaseOperator, Matrix.diagonal_sub,
    Matrix.l2_opNorm_diagonal]
  rw [pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (1/2 : ℝ)^k)]
  intro x
  have h := probability_realized_phase_pointwise X A U hU a₀ good hlabel k x
  simpa only [probabilityRealizedPhase, probabilityProgramFrameOperator] using! h

private theorem probability_realized_modulus_defect :
    ∀ (X A : Type) [Fintype X] [Fintype A] [DecidableEq X] [DecidableEq A]
      (U : Matrix (X × A) (X × A) ℂ) (hU : U ∈ Matrix.unitaryGroup (X × A) ℂ)
      (a₀ : A) (good : Finset A)
      (hlabel : ∀ (x y : X) (a : A), x ≠ y → U (x,a) (y,a₀) = 0) (k : ℕ) (x : X),
      |‖probabilityRealizedPhase (X := X) a₀
            (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x‖
          - 1| ≤ (1/2 : ℝ)^k := by
  intro X A _ _ _ _ U hU a₀ good hlabel k x
  have hpoint := probability_realized_phase_pointwise X A U hU a₀ good hlabel k x
  have hE : ‖Complex.exp (Complex.I * (probabilityMass U a₀ good x : ℂ))‖ = 1 :=
    probability_phase_coefficient_norm _
  have h := abs_norm_sub_norm_le
    (probabilityRealizedPhase (X := X) a₀
      (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x)
    (Complex.exp (Complex.I * (probabilityMass U a₀ good x : ℂ)))
  rw [hE] at h
  exact h.trans hpoint

private theorem norm_normalized_sub_self (z : ℂ) (hz : z ≠ 0) :
    ‖z / (‖z‖ : ℂ) - z‖ = |‖z‖ - 1| := by
  have hrz : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  have hne : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hrz.ne'
  have hconn : (1 : ℂ) - (‖z‖ : ℂ) = ((1 - ‖z‖ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_one, (Complex.ofReal_sub 1 ‖z‖).symm]
  have hdecomp : z / (‖z‖ : ℂ) - z = z * ((1 : ℂ) / (‖z‖ : ℂ) - 1) := by
    field_simp
  rw [hdecomp, norm_mul]
  have hw : ‖(1 : ℂ) / (‖z‖ : ℂ) - 1‖ = |1 - ‖z‖| / ‖z‖ := by
    have h2 : (1 : ℂ) / (‖z‖ : ℂ) - 1 = ((1 - ‖z‖ : ℝ) : ℂ) / (‖z‖ : ℂ) := by
      rw [div_sub' hne, mul_one, hconn]
    rw [h2, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hrz.le]
  rw [hw]
  calc ‖z‖ * (|1 - ‖z‖| / ‖z‖) = (|1 - ‖z‖| * ‖z‖) / ‖z‖ := by ring
    _ = |1 - ‖z‖| := by rw [div_eq_iff hrz.ne']
    _ = |‖z‖ - 1| := abs_sub_comm _ _

theorem probability_realized_phase_modulus_lower :
    ∀ (X A : Type) [Fintype X] [Fintype A] [DecidableEq X] [DecidableEq A]
      (U : Matrix (X × A) (X × A) ℂ) (hU : U ∈ Matrix.unitaryGroup (X × A) ℂ)
      (a₀ : A) (good : Finset A)
      (hlabel : ∀ (x y : X) (a : A), x ≠ y → U (x,a) (y,a₀) = 0) (k : ℕ) (hk : 1 ≤ k) (x : X),
      1 / 2 ≤ probabilityRealizedPhaseModulus (X := X) a₀
          (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x := by
  intro X A _ _ _ _ U hU a₀ good hlabel k hk x
  have hdefect := probability_realized_modulus_defect X A U hU a₀ good hlabel k x
  have hmod : probabilityRealizedPhaseModulus (X := X) a₀
      (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x
      = ‖probabilityRealizedPhase (X := X) a₀
          (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x‖ := rfl
  have hhalf : (1/2 : ℝ)^k ≤ 1/2 := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [pow_succ]
    have h1 : (1/2 : ℝ)^m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    calc (1/2:ℝ)^m * (1/2) ≤ 1 * (1/2) := by gcongr
      _ = 1/2 := by ring
  have hlo := (abs_le.mp hdefect).1
  have hpos : (0 : ℝ) < 1 / 2 := by norm_num
  rw [hmod]
  linarith

theorem probability_normalized_realized_phase_norm :
    ∀ (X A : Type) [Fintype X] [Fintype A] [DecidableEq X] [DecidableEq A]
      (U : Matrix (X × A) (X × A) ℂ) (hU : U ∈ Matrix.unitaryGroup (X × A) ℂ)
      (a₀ : A) (good : Finset A)
      (hlabel : ∀ (x y : X) (a : A), x ≠ y → U (x,a) (y,a₀) = 0) (k : ℕ) (hk : 1 ≤ k) (x : X),
      ‖probabilityNormalizedRealizedPhase (X := X) a₀
          (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x‖
        = 1 := by
  intro X A _ _ _ _ U hU a₀ good hlabel k hk x
  have hlo := probability_realized_phase_modulus_lower X A U hU a₀ good hlabel k hk x
  have hmod : probabilityRealizedPhaseModulus (X := X) a₀
      (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x
      = ‖probabilityRealizedPhase (X := X) a₀
          (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x‖ := rfl
  have hlo0 : (0 : ℝ) ≤ probabilityRealizedPhaseModulus (X := X) a₀
      (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x :=
    le_trans (by norm_num) hlo
  have hposD : (0 : ℝ) < probabilityRealizedPhaseModulus (X := X) a₀
      (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x := by
    have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
    linarith
  have hne : probabilityRealizedPhase (X := X) a₀
      (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x ≠ 0 := by
    intro hz
    have hz0 : ‖probabilityRealizedPhase (X := X) a₀
        (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x‖ = 0 := by
      simp [hz]
    rw [hmod] at hposD
    linarith
  show ‖probabilityRealizedPhase (X := X) a₀
        (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x
        / (probabilityRealizedPhaseModulus (X := X) a₀
            (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x : ℂ)‖
      = 1
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlo0]
  rw [hmod]
  exact div_self (by rw [← hmod]; exact hposD.ne')

private theorem diagonal_unitary_of_unit_modulus {X : Type} [Fintype X] [DecidableEq X]
    (v : X → ℂ) (hv : ∀ x, ‖v x‖ = 1) :
    Matrix.diagonal v ∈ Matrix.unitaryGroup X ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext z
  change (starRingEnd ℂ) (v z) * v z = 1
  rw [Complex.conj_mul']
  rw [hv z]
  norm_num

theorem probability_normalized_phase_operator_unitary :
    ∀ (X A : Type) [Fintype X] [Fintype A] [DecidableEq X] [DecidableEq A]
      (U : Matrix (X × A) (X × A) ℂ) (hU : U ∈ Matrix.unitaryGroup (X × A) ℂ)
      (a₀ : A) (good : Finset A)
      (hlabel : ∀ (x y : X) (a : A), x ≠ y → U (x,a) (y,a₀) = 0) (k : ℕ) (hk : 1 ≤ k),
      probabilityNormalizedRealizedPhaseOperator (X := X) a₀
          (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k))
        ∈ Matrix.unitaryGroup X ℂ := by
  intro X A _ _ _ _ U hU a₀ good hlabel k hk
  unfold probabilityNormalizedRealizedPhaseOperator
  exact diagonal_unitary_of_unit_modulus
    (fun x => probabilityNormalizedRealizedPhase (X := X) a₀
      (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x)
    (fun x => probability_normalized_realized_phase_norm X A U hU a₀ good hlabel k hk x)

theorem probability_normalized_realized_phase_deviation :
    ∀ (X A : Type) [Fintype X] [Fintype A] [DecidableEq X] [DecidableEq A]
      (U : Matrix (X × A) (X × A) ℂ) (hU : U ∈ Matrix.unitaryGroup (X × A) ℂ)
      (a₀ : A) (good : Finset A)
      (hlabel : ∀ (x y : X) (a : A), x ≠ y → U (x,a) (y,a₀) = 0) (k : ℕ) (hk : 1 ≤ k) (x : X),
      ‖probabilityNormalizedRealizedPhase (X := X) a₀
          (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x
        - Complex.exp (Complex.I * (probabilityMass U a₀ good x : ℂ))‖
        ≤ 2 * (1/2 : ℝ)^k := by
  intro X A _ _ _ _ U hU a₀ good hlabel k hk x
  have hpoint := probability_realized_phase_pointwise X A U hU a₀ good hlabel k x
  have hdefect := probability_realized_modulus_defect X A U hU a₀ good hlabel k x
  have hlo := probability_realized_phase_modulus_lower X A U hU a₀ good hlabel k hk x
  have hmod : probabilityRealizedPhaseModulus (X := X) a₀
      (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x
      = ‖probabilityRealizedPhase (X := X) a₀
          (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x‖ := rfl
  have hposD : (0 : ℝ) < probabilityRealizedPhaseModulus (X := X) a₀
      (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x := by
    have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
    linarith
  have hne : probabilityRealizedPhase (X := X) a₀
      (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x ≠ 0 := by
    intro hz
    have hz0 : ‖probabilityRealizedPhase (X := X) a₀
        (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x‖ = 0 := by
      simp [hz]
    rw [hmod] at hposD
    linarith
  have hnorm := norm_normalized_sub_self
    (probabilityRealizedPhase (X := X) a₀
      (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x) hne
  have hsub : ‖probabilityNormalizedRealizedPhase (X := X) a₀
        (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x
        - probabilityRealizedPhase (X := X) a₀
            (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x‖
      ≤ (1/2 : ℝ)^k := by
    unfold probabilityNormalizedRealizedPhase
    rw [hmod, hnorm]
    exact hdefect
  calc ‖probabilityNormalizedRealizedPhase (X := X) a₀
          (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x
        - Complex.exp (Complex.I * (probabilityMass U a₀ good x : ℂ))‖
      ≤ ‖probabilityNormalizedRealizedPhase (X := X) a₀
          (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x
          - probabilityRealizedPhase (X := X) a₀
            (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x‖
        + ‖probabilityRealizedPhase (X := X) a₀
            (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x
          - Complex.exp (Complex.I * (probabilityMass U a₀ good x : ℂ))‖ := by
          have heq : probabilityNormalizedRealizedPhase (X := X) a₀
                (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x
                - Complex.exp (Complex.I * (probabilityMass U a₀ good x : ℂ))
              = (probabilityNormalizedRealizedPhase (X := X) a₀
                  (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x
                  - probabilityRealizedPhase (X := X) a₀
                    (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x)
                + (probabilityRealizedPhase (X := X) a₀
                  (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k)) x
                  - Complex.exp (Complex.I * (probabilityMass U a₀ good x : ℂ))) := by ring
          rw [heq]
          exact norm_add_le _ _
    _ ≤ (1/2 : ℝ)^k + (1/2 : ℝ)^k := add_le_add hsub hpoint
    _ = 2 * (1/2 : ℝ)^k := by ring

theorem probability_normalized_phase_operator_dist :
    ∀ (X A : Type) [Fintype X] [Fintype A] [DecidableEq X] [DecidableEq A]
      (U : Matrix (X × A) (X × A) ℂ) (hU : U ∈ Matrix.unitaryGroup (X × A) ℂ)
      (a₀ : A) (good : Finset A)
      (hlabel : ∀ (x y : X) (a : A), x ≠ y → U (x,a) (y,a₀) = 0) (k : ℕ) (hk : 1 ≤ k),
      ‖probabilityNormalizedRealizedPhaseOperator (X := X) a₀
          (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k))
          - probabilityPhaseOperator (probabilityMass U a₀ good)‖
        ≤ 2 * (1/2 : ℝ)^k := by
  intro X A _ _ _ _ U hU a₀ good hlabel k hk
  rw [probabilityNormalizedRealizedPhaseOperator, probabilityPhaseOperator, Matrix.diagonal_sub,
    Matrix.l2_opNorm_diagonal]
  rw [pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * (1/2 : ℝ)^k)]
  intro x
  have h := probability_normalized_realized_phase_deviation X A U hU a₀ good hlabel k hk x
  simpa only [probabilityNormalizedRealizedPhase, probabilityPhaseOperator,
    Matrix.diagonal_apply_eq] using! h

theorem probability_normalized_readout_normalized :
    ∀ (d M : ℕ) (hM : 0 < M) (A : Type) [Fintype A] [DecidableEq A]
      (U : Matrix (GradientGrid d M × A) (GradientGrid d M × A) ℂ)
      (hU : U ∈ Matrix.unitaryGroup (GradientGrid d M × A) ℂ)
      (a₀ : A) (good : Finset A)
      (hlabel : ∀ (x y : GradientGrid d M) (a : A), x ≠ y → U (x,a) (y,a₀) = 0)
      (k : ℕ) (hk : 1 ≤ k),
      Normalized (Run (probabilityNormalizedRealizedPhaseOperator (X := GradientGrid d M) a₀
          (evaluate (probabilityPrimitiveOracle U)
            (probabilityPhaseWord (X := GradientGrid d M) a₀ good k)))
          (gradientWord d M) (Ket (gradientZero d M hM))) := by
  intro d M hM A _ _ U hU a₀ good hlabel k hk
  obtain ⟨hC, hq, _⟩ := gradient_coordinate_qft_word_unitarity d M hM
  exact hC.normalized_run
    (probability_normalized_phase_operator_unitary (GradientGrid d M) A U hU a₀ good hlabel k hk)
    (normalized_ket _)

theorem probability_normalized_born_transport :
    ∀ (d M : ℕ) (hM : 0 < M) (A : Type) [Fintype A] [DecidableEq A]
      (U : Matrix (GradientGrid d M × A) (GradientGrid d M × A) ℂ)
      (hU : U ∈ Matrix.unitaryGroup (GradientGrid d M × A) ℂ)
      (a₀ : A) (good : Finset A)
      (hlabel : ∀ (x y : GradientGrid d M) (a : A), x ≠ y → U (x,a) (y,a₀) = 0)
      (k : ℕ) (hk : 1 ≤ k) (S : Finset (GradientGrid d M)),
      |MeasureProb (Run (probabilityNormalizedRealizedPhaseOperator (X := GradientGrid d M) a₀
          (evaluate (probabilityPrimitiveOracle U)
            (probabilityPhaseWord (X := GradientGrid d M) a₀ good k)))
          (gradientWord d M) (Ket (gradientZero d M hM))) S
        - MeasureProb (gradientReadout d M hM
            (probabilityReadoutPhase (probabilityMass U a₀ good))) S|
        ≤ 4 * (1/2 : ℝ)^k := by
  intro d M hM A _ _ U hU a₀ good hlabel k hk S
  obtain ⟨hC, hq, _⟩ := gradient_coordinate_qft_word_unitarity d M hM
  have hdist := probability_normalized_phase_operator_dist
    (GradientGrid d M) A U hU a₀ good hlabel k hk

  rw [probability_phase_operator_eq_gradient_phase d M (probabilityMass U a₀ good)] at hdist
  have h := measureProb_run_sub_le_queryCount_of_le
    (probabilityNormalizedRealizedPhaseOperator (X := GradientGrid d M) a₀
      (evaluate (probabilityPrimitiveOracle U)
        (probabilityPhaseWord (X := GradientGrid d M) a₀ good k)))
    (gradientPhase d M (probabilityReadoutPhase (probabilityMass U a₀ good)))
    (gradientWord d M) (Ket (gradientZero d M hM)) S (2 * (1/2 : ℝ)^k)
    (probability_normalized_phase_operator_unitary (GradientGrid d M) A U hU a₀ good hlabel k hk)
    (gradientPhase_unitary d M (probabilityReadoutPhase (probabilityMass U a₀ good)))
    hC (normalized_ket _) hdist
  have hbound : 2 * (QueryCount (gradientWord d M) : ℝ) * (2 * (1/2 : ℝ)^k)
      = 4 * (1/2 : ℝ)^k := by
    rw [hq]
    norm_num
    ring

  exact le_trans h (by rw [hbound])

theorem probability_normalized_readout_composed_guarantee :
    ∀ (d M : ℕ) (hM : 0 < M) (hM2 : 2 ≤ M) (g : Fin d → ℝ) (c w B : ℝ) (hw : 0 < w)
      (hB : 0 ≤ B) (A : Type) [Fintype A] [DecidableEq A]
      (U : Matrix (GradientGrid d M × A) (GradientGrid d M × A) ℂ)
      (hU : U ∈ Matrix.unitaryGroup (GradientGrid d M × A) ℂ)
      (a₀ : A) (good : Finset A)
      (hlabel : ∀ (x y : GradientGrid d M) (a : A), x ≠ y → U (x,a) (y,a₀) = 0)
      (k : ℕ) (hk : 1 ≤ k)
      (hlin : ∀ x : GradientGrid d M,
        |probabilityReadoutPhase (probabilityMass U a₀ good) x
          - (c + ∑ j : Fin d, g j * (x j).val)| ≤ B),
      MeasureProb (Run (probabilityNormalizedRealizedPhaseOperator (X := GradientGrid d M) a₀
          (evaluate (probabilityPrimitiveOracle U)
            (probabilityPhaseWord (X := GradientGrid d M) a₀ good k)))
          (gradientWord d M) (Ket (gradientZero d M hM)))
        (composedGoodWindow d M g w)
        ≥ 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B - 4 * (1/2 : ℝ)^k := by
  intro d M hM hM2 g c w B hw hB A _ _ U hU a₀ good hlabel k hk hlin
  have htransport := probability_normalized_born_transport d M hM A U hU a₀ good hlabel k hk
    (composedGoodWindow d M g w)
  have hideal := gradient_actual_phase_error_transport d M hM g c w B
    (probabilityReadoutPhase (probabilityMass U a₀ good)) hM2 hw hB hlin
  have hideal' :
      MeasureProb (gradientReadout d M hM (probabilityReadoutPhase (probabilityMass U a₀ good)))
          (composedGoodWindow d M g w)
        ≥ 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B := by
    simpa only [composedGoodWindow] using! hideal
  have h := abs_le.mp htransport
  linarith

theorem clause2_next_endpoint : stageB_gradient_oracle_clause2_next_spec := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X _ _ p q ε hε herror
    exact probability_rotation_operator_error p q ε hε herror
  · intro X _ _ p q ε hε herror x
    exact probability_access_phase_error p q ε hε herror x
  · intro d M hM p q ε hε herror S
    exact probability_access_readout_transport d M hM p q ε hε herror S
  · intro d M hM hM2 g c w B hw hB p q ε hε hlin herror
    exact probability_access_composed_guarantee d M hM hM2 g c w B hw hB p q ε hε hlin herror
  · intro X A _ _ _ _ U hU a₀ good hlabel k d M hM
    exact probability_access_ledger X A U hU a₀ good hlabel k d M hM

theorem clause2_endpoint :
    Qatlib.Concepts.FourierRecovery.ModularFourier.stageB_gradient_oracle_clause2_spec ∧
    stageB_gradient_oracle_clause2_next_spec :=
  ⟨Qatlib.Concepts.FourierRecovery.ModularFourier.GradientOracle.clause2_endpoint, clause2_next_endpoint⟩

theorem clause8_endpoint :
    Qatlib.Concepts.FourierRecovery.ModularFourier.stageB_gradient_oracle_clause8_spec :=
  Qatlib.Concepts.FourierRecovery.ModularFourier.GradientOracle.clause8_endpoint

end Qatlib.Concepts.FourierRecovery.ModularFourier.GradientOracleRefined
