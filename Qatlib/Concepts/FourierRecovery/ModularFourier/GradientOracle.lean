/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FourierRecovery.ModularFourier.GradientOracleDefs
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.HspRecovery.Reduction.GradientOracle
open Qatlib.Concepts.GradientOracle.ValueKickback
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.FourierRecovery.ModularFourier
open Qatlib.Concepts.FourierRecovery.ModularFourier.GradientSourceContinuation

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.FourierRecovery.ModularFourier.GradientOracle

open Qatlib
open Qatlib.Concepts.QspSimulation.JacobiAnger
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexConjugate
set_option warningAsError false

private theorem probabilityPhaseCoeff_norm (p : ℝ) :
    ‖Complex.exp (Complex.I * (p : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (Complex.I * (p : ℂ)).re = 0 := by
    rw [Complex.mul_re]
    simp
  rw [hre]
  norm_num

theorem probability_phase_operator_unitary {X : Type} [Fintype X] [DecidableEq X]
    (p : X → ℝ) : probabilityPhaseOperator p ∈ Matrix.unitaryGroup X ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  simp only [probabilityPhaseOperator, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext x
  show conj (Complex.exp (Complex.I * (p x : ℂ))) * Complex.exp (Complex.I * (p x : ℂ)) = 1
  rw [Complex.conj_mul', probabilityPhaseCoeff_norm (p x)]
  norm_num

theorem probability_phase_operator_eq_gradient_phase (d M : ℕ)
    (p : GradientGrid d M → ℝ) :
    probabilityPhaseOperator p = gradientPhase d M (probabilityReadoutPhase p) := by
  unfold probabilityPhaseOperator gradientPhase probabilityReadoutPhase
  congr 1
  funext x
  have hexp : 2 * Real.pi * Complex.I * ((p x / (2 * Real.pi) : ℝ) : ℂ)
      = Complex.I * (p x : ℂ) := by
    push_cast
    field_simp
  rw [hexp]

theorem probability_phase_readout_coincides (d M : ℕ) (hM : 0 < M)
    (p : GradientGrid d M → ℝ) :
    gradientReadout d M hM (probabilityReadoutPhase p) =
      Run (probabilityPhaseOperator p) (gradientWord d M) (Ket (gradientZero d M hM)) := by
  unfold gradientReadout
  rw [probability_phase_operator_eq_gradient_phase]

theorem value_phase_readout_event_error :
    ∀ (d M Q : ℕ) [NeZero Q] (hM : 0 < M)
      (v : GradientGrid d M → ZMod Q) (φ : GradientGrid d M → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
      (herror : ∀ x, ∃ k : ℤ, |gradientValuePhase Q v x - φ x - k| ≤ δ)
      (S : Finset (GradientGrid d M)),
      |MeasureProb (gradientReadout d M hM (gradientValuePhase Q v)) S -
        MeasureProb (gradientReadout d M hM φ) S| ≤ 4 * Real.pi * δ := by
  intro d M Q _ hM v φ δ hδ herror S
  let κ : GradientGrid d M → ℤ := fun x => Classical.choose (herror x)
  have hspec (x : GradientGrid d M) : |gradientValuePhase Q v x - φ x - κ x| ≤ δ := by
    exact Classical.choose_spec (herror x)
  have hshift : gradientPhase d M (gradientValuePhase Q v)
      = gradientPhase d M (fun x => gradientValuePhase Q v x - (κ x : ℝ)) := by
    have h := gradientPhase_int_shift d M (gradientValuePhase Q v) (fun x => -κ x)
    rw [← h]
    funext x
    simp only [Int.cast_neg]
    abel
  have hpoint (x : GradientGrid d M) :
      |gradientValuePhase Q v x - (κ x : ℝ) - φ x| ≤ δ := by
    have h := abs_le.mp (hspec x)
    have heq : |gradientValuePhase Q v x - (κ x : ℝ) - φ x|
        = |gradientValuePhase Q v x - φ x - (κ x : ℝ)| := by
      congr 1
      ring
    rw [heq]
    exact abs_le.mpr h
  have h := gradient_actual_phase_event_error d M hM
    (fun x => gradientValuePhase Q v x - (κ x : ℝ)) φ δ hδ hpoint S
  have hread : gradientReadout d M hM (gradientValuePhase Q v)
      = gradientReadout d M hM (fun x => gradientValuePhase Q v x - (κ x : ℝ)) := by
    unfold gradientReadout
    rw [hshift]
  rw [← hread] at h
  exact h

theorem probability_phase_frame_bound :
    ∀ (X A : Type) [Fintype X] [Fintype A] [DecidableEq X] [DecidableEq A]
      (U : Matrix (X × A) (X × A) ℂ) (hU : U ∈ Matrix.unitaryGroup (X × A) ℂ)
      (a₀ : A) (good : Finset A)
      (hlabel : ∀ (x y : X) (a : A), x ≠ y → U (x,a) (y,a₀) = 0) (k : ℕ),
      WellFormedAdjointCircuit (probabilityPhaseWord (X := X) a₀ good k) ∧
        adjointQueryCount (probabilityPhaseWord (X := X) a₀ good k)
          = 54 * (4 * computedSignalCutoff (1/2) k + 1) ∧
        adjointGateCount (probabilityPhaseWord (X := X) a₀ good k)
          = 1 + (27 * (4 * computedSignalCutoff (1/2) k + 6) + 79)
            + 27 * (4 * computedSignalCutoff (1/2) k + 1) ∧
        ∀ ψ : QState X,
          ‖toEuclidean_fromVec
              (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k) *ᵥ
                  (scaleEightFrame (hamiltonianFrame (cleanFrame (X := X) a₀)) *ᵥ ψ) -
                scaleEightFrame (hamiltonianFrame (cleanFrame (X := X) a₀)) *ᵥ
                  (probabilityPhaseOperator (probabilityMass U a₀ good) *ᵥ ψ))‖
            ≤ (1/2 : ℝ)^k * ‖toEuclidean_fromVec ψ‖ := by
  intro X A _ _ _ _ U hU a₀ good hlabel k
  exact probability_phase_clean_frame_bound U hU a₀ good hlabel k

theorem readout_is_actual_fourier_word_born_law :
    ∀ (d M : ℕ) (hM : 0 < M) (φ : GradientGrid d M → ℝ),
      gradientReadout d M hM φ =
        Run (gradientPhase d M φ) (gradientWord d M) (Ket (gradientZero d M hM)) :=
  fun _ _ _ _ => rfl

theorem readout_decoder_error :
    ∀ (d M : ℕ) (hM : 0 < M) (g : Fin d → ℝ) (w : ℝ)
      (hg : ∀ j : Fin d, |g j| ≤ 1 / 4) (hw : w ≤ 1 / 8)
      (z : GradientGrid d M)
      (hgood : ∀ j : Fin d, phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w),
      ∀ j : Fin d, |readoutDecoder z j - g j| ≤ w := by
  intro d M hM g w hg hw z hgood j
  have h := gradient_signed_decode_window M hM (z j) (g j) w (hg j) hw (hgood j)
  simpa only [readoutDecoder] using! h

theorem readout_joint_success :
    ∀ (d M : ℕ) (hM : 0 < M) (g : Fin d → ℝ) (c w B : ℝ) (φ : GradientGrid d M → ℝ)
      (hM2 : 2 ≤ M) (hw : 0 < w) (hB : 0 ≤ B)
      (herror : ∀ x, |φ x - (c + ∑ j : Fin d, g j * (x j).val)| ≤ B),
      MeasureProb (gradientReadout d M hM φ)
        (Finset.univ.filter (fun z => ∀ j : Fin d,
          phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w))
        ≥ 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B :=
  gradient_actual_phase_error_transport

theorem readout_decoder_dyadic (m : ℕ) (z : Fin (2 ^ m)) :
    ∃ n : ℤ, readoutDecoder (d := 1) (fun _ => z) 0 = (n : ℝ) / (2 : ℝ) ^ m := by
  obtain ⟨n, hn⟩ := centered_output_dyadic m z
  refine ⟨n, ?_⟩
  simpa only [readoutDecoder] using! hn

theorem readout_backend_ledger (d M K k : ℕ) (hM : 0 < M) :
    readoutIntegerBits K k = K + k ∧
      readoutSpaceBits d M K k = d * Nat.clog 2 (max 2 M) + K + k ∧
      QueryCount (gradientWord d M) = 1 ∧
      GateCount (gradientWord d M) = 2 * d := by
  obtain ⟨hC, hq, hg⟩ := gradient_coordinate_qft_word_unitarity d M hM
  exact ⟨rfl, rfl, hq, hg⟩

theorem clause2_endpoint : stageB_gradient_oracle_clause2_spec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d M Q _ v x
    exact value_compute_kickback_uncompute_actual d M Q v x
  · intro d M Q hM _
    obtain ⟨hW, hq, hg, _⟩ := value_compute_kickback_uncompute_resources d M Q
    refine ⟨hW, hq, hg, ?_⟩
    exact (gradient_value_one_query_clean_fourier_consumer d M Q hM
      (fun _ => (0 : ZMod Q))).2.1
  · intro d M Q _ v φ δ hδ herror
    exact value_compute_kickback_uncompute_operator_error d M Q v φ δ hδ herror
  · intro d M Q _ hM v φ δ hδ herror S
    exact value_phase_readout_event_error d M Q hM v φ δ hδ herror S
  · intro X _ _ p
    exact probability_phase_operator_unitary p
  · intro d M p
    exact probability_phase_operator_eq_gradient_phase d M p
  · intro d M hM p
    exact probability_phase_readout_coincides d M hM p
  · intro X A _ _ _ _ U hU a₀ good hlabel k
    exact probability_phase_frame_bound X A U hU a₀ good hlabel k

theorem clause8_endpoint : stageB_gradient_oracle_clause8_spec := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d M hM φ
    exact readout_is_actual_fourier_word_born_law d M hM φ
  · intro d M hM g w hg hw z hgood
    exact readout_decoder_error d M hM g w hg hw z hgood
  · intro d M hM g c w B φ hM2 hw hB herror
    exact readout_joint_success d M hM g c w B φ hM2 hw hB herror
  · intro m z
    exact readout_decoder_dyadic m z
  · exact (non_dyadic_one_third.1)
  · intro d M K k hM
    exact readout_backend_ledger d M K k hM

end Qatlib.Concepts.FourierRecovery.ModularFourier.GradientOracle
