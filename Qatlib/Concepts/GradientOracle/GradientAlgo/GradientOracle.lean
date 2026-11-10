/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.GradientOracleDefs
import Qatlib.Concepts.GradientOracle.ReadoutTools.AlmostAffineVectorMedianOpti
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.ShadowModels.SampleBudget
open Qatlib.Concepts.HspRecovery.Reduction.GradientOracle
open Qatlib.Concepts.GradientOracle.FullRange
open Qatlib.Concepts.GradientOracle.ValueKickback
open Qatlib.Concepts.GradientOracle.ReadoutTools
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.GradientOracle.GradientAlgo

open Qatlib.Concepts.HspRecovery.Reduction.GradientOracle Qatlib.Concepts.GradientOracle.GradientAlgo
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

theorem g8 :

  (∀ (d M : ℕ) (hM : 0 < M) (g : Fin d → ℝ) (c : ℝ),
    gradientReadout d M hM (fun x => c + ∑ j : Fin d, g j * (x j).val) =
      Complex.exp (2 * Real.pi * Complex.I * (c : ℂ)) •
        gridProductState (fun j => qpeKernel M (g j))) ∧

  (∀ (d M : ℕ) (hM : 0 < M) (q : GradientGrid d M) (c : ℝ),
    gradientReadout d M hM
        (fun x => c + ∑ j : Fin d, (q j).val * (x j).val / (M : ℝ)) =
      Complex.exp (2 * Real.pi * Complex.I * (c : ℂ)) • Ket q) ∧

  ((∀ (d M : ℕ) (hM : 0 < M) (g : Fin d → ℝ) (c w : ℝ),
      2 ≤ M → 0 < w →
        MeasureProb
            (gradientReadout d M hM (fun x => c + ∑ j : Fin d, g j * (x j).val))
            (Finset.univ.filter (fun z => ∀ j : Fin d,
              phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w)) ≥
          1 - 16 * (d : ℝ) / ((M : ℝ) * w)) ∧
    (∀ (M : ℕ) (φ w : ℝ) (hM : 0 < M) (hw : 0 < w),
      (∑ y ∈ Finset.univ.filter (fun y : Fin M =>
        w < phaseDistance φ ((y.val : ℝ) / (M : ℝ))), ‖qpeKernel M φ y‖ ^ 2) ≤
        16 / ((M : ℝ) * w))) ∧

  ((∀ (d M Q : ℕ) (hM : 0 < M) [NeZero Q] (v : GradientGrid d M → ZMod Q)
      (S : Finset (GradientGrid d M)),
      MeasureProb
          (Run (gradientValueOracle Q v) (gradientValueWord d M Q)
            (fun xy => Ket (gradientZero d M hM) xy.1 * gradientKickState Q xy.2))
          (S ×ˢ Finset.univ) =
        MeasureProb (gradientReadout d M hM (gradientValuePhase Q v)) S) ∧
    (∀ (d M Q : ℕ) (hM : 0 < M) [NeZero Q] (v : GradientGrid d M → ZMod Q)
        (φ : GradientGrid d M → ℝ) (δ : ℝ) (S : Finset (GradientGrid d M)),
      0 ≤ δ →
        (∀ x, ∃ k : ℤ, |gradientValuePhase Q v x - φ x - k| ≤ δ) →
          |MeasureProb (gradientReadout d M hM (gradientValuePhase Q v)) S -
            MeasureProb (gradientReadout d M hM φ) S| ≤ 4 * Real.pi * δ)) ∧

  (∀ (d M Q : ℕ) (hM : 0 < M) [NeZero Q] (w δ : ℝ) (g : Fin d → ℝ) (c : ℝ)
      (v : GradientGrid d M → ZMod Q),
    2 ≤ M → 0 < w → 0 ≤ δ →
      (∀ x, ∃ k : ℤ,
        |gradientValuePhase Q v x - (c + ∑ j : Fin d, g j * (x j).val) - k| ≤ δ) →
        MeasureProb (gradientReadout d M hM (gradientValuePhase Q v))
            (Finset.univ.filter (fun z => ∀ j : Fin d,
              phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w)) ≥
          1 - readoutErrorBudget d M w δ) ∧

  (∀ (d M : ℕ) (hM : 0 < M) (K k : ℕ),
    IsUnitaryCircuit (fullRangeGradientProgram d M K k) ∧
      QueryCount (fullRangeGradientProgram d M K k) = 1 ∧
      GateCount (fullRangeGradientProgram d M K k) = 2 * d + 1) ∧

  ((∀ (d M : ℕ) (hM : 0 < M) (K k : ℕ) (f : GradientGrid d M → ℝ) (lo s : ℝ),
      fullRangeGradientOutput d M hM K k f lo s =
        TensorState
          (gradientReadout d M hM (fullRangePhase K k (fullRangeValueTable K k f lo s)))
          (fullRangeKickState K k)) ∧
    (∀ (X : Type) (K k : ℕ) (f : X → ℝ) (lo s R : ℝ),
      0 < s → 0 ≤ R → s * R < (2 : ℝ) ^ K → (∀ x, lo ≤ f x ∧ f x ≤ lo + R) →
        ∀ x : X,
          |fullRangePhase K k (fullRangeValueTable K k f lo s) x - s * (f x - lo)| ≤
            1 / (2 : ℝ) ^ k) ∧
    (∀ (X : Type) (K k : ℕ) (f : X → ℝ) (lo s R : ℝ),
      0 < s → 0 ≤ R → s * R < (2 : ℝ) ^ K → (∀ x, lo ≤ f x ∧ f x ≤ lo + R) →
        ∀ x : X,
          0 ≤ f x - dyadicDecode lo s K k (fullRangeValueTable K k f lo s x) ∧
            f x - dyadicDecode lo s K k (fullRangeValueTable K k f lo s x) <
              1 / (s * (2 : ℝ) ^ k)) ∧
    (∀ (X : Type) (K k : ℕ) (v : X → ZMod (2 ^ (K + k))) (x : X),
      HasDyadicRecord k (fullRangePhase K k v x)) ∧
    (∀ k : ℕ, ¬ HasDyadicRecord k (1 / 3))) ∧

  ((∀ (d M : ℕ) (r : ℕ) (ω : Fin (2 * r + 1) → GradientGrid d M),
      medianComparisonCount d M r ω ≤ d * 10000 * (2 * r + 1)) ∧
    (Qatlib.Concepts.GradientOracle.ReadoutTools.AlmostAffineVectorMedian)) ∧

  (∀ (d M : ℕ) (r : ℕ) (ω : Fin (2 * r + 1) → GradientGrid d M) (j : Fin d),
    gradientMedianCounted r ω j =
      qSelect (List.ofFn fun t => gradientSignedValueQ M (ω t j)) r) ∧

  (∀ (K k : ℕ) (v : ZMod (2 ^ (K + k))) (lo s : ℝ),
    dyadicDecode lo s K k v = lo + (v.val : ℝ) / (s * (2 : ℝ) ^ k)) ∧

  (∀ n : ℕ,
    GateCount (localProgramCircuit (localQFT n)) = n + n * (n - 1) / 2 + n / 2 ∧
      QueryCount (localProgramCircuit (localQFT n)) = 0) ∧

  (∀ n b : ℕ,
    GateCount (localProgramCircuit (approxLocalQFT n b)) ≤ n + n * (b + 1) + n / 2) ∧

  (∀ (n b : ℕ) (ψ : QState (Reg n)) (S : Finset (Reg n)),
    Normalized ψ →
      (|MeasureProb
            (Run (1 : Matrix (Reg n) (Reg n) ℂ) (localProgramCircuit (approxLocalQFT n b)) ψ) S -
          MeasureProb
            (ApplyGate (relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n))) ψ) S| ≤
        Real.pi * (n : ℝ) / (2 ^ b : ℝ)) ∧
      (|MeasureProb
            (Run (1 : Matrix (Reg n) (Reg n) ℂ)
              (localProgramCircuit (localProgramAdjoint (approxLocalQFT n b))) ψ) S -
          MeasureProb
            (ApplyGate (relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n)))ᴴ ψ) S| ≤
        Real.pi * (n : ℝ) / (2 ^ b : ℝ))) ∧

  (∀ (d M K k : ℕ),
    readoutIntegerBits K k = K + k ∧
      readoutSpaceBits d M K k = d * Nat.clog 2 (max 2 M) + K + k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gradient_offgrid_actual_readout
  · exact gradient_affine_actual_exact_readout
  · exact ⟨gradient_offgrid_joint_window, gradient_phase_kernel_tail⟩
  · exact ⟨gradient_value_actual_data_marginal, gradient_value_precision_actual_readout_event⟩
  · intro d M Q hM instQ w δ g c v hM2 hw hδ hprec
    have hstable : |MeasureProb (gradientReadout d M hM (gradientValuePhase Q v))
          (Finset.univ.filter (fun z => ∀ j : Fin d,
            phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w)) -
        MeasureProb (gradientReadout d M hM (fun x => c + ∑ j : Fin d, g j * (x j).val))
          (Finset.univ.filter (fun z => ∀ j : Fin d,
            phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w))| ≤ 4 * Real.pi * δ :=
      @gradient_value_precision_actual_readout_event d M Q hM instQ v
        (fun x => c + ∑ j : Fin d, g j * (x j).val) δ
        (Finset.univ.filter (fun z => ∀ j : Fin d,
          phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w)) hδ hprec
    have hwindow : MeasureProb
        (gradientReadout d M hM (fun x => c + ∑ j : Fin d, g j * (x j).val))
        (Finset.univ.filter (fun z => ∀ j : Fin d,
          phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w)) ≥
        1 - 16 * (d : ℝ) / ((M : ℝ) * w) :=
      gradient_offgrid_joint_window d M hM g c w hM2 hw
    have hbase : 1 - 16 * (d : ℝ) / ((M : ℝ) * w) ≤
        MeasureProb (gradientReadout d M hM (fun x => c + ∑ j : Fin d, g j * (x j).val))
          (Finset.univ.filter (fun z => ∀ j : Fin d,
            phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w)) :=
      hwindow
    have habs := abs_sub_le_iff.mp hstable
    have hmain : 1 - readoutErrorBudget d M w δ ≤
        MeasureProb (gradientReadout d M hM (gradientValuePhase Q v))
          (Finset.univ.filter (fun z => ∀ j : Fin d,
            phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w)) := by
      show 1 - (16 * (d : ℝ) / ((M : ℝ) * w) + 4 * Real.pi * δ) ≤ _
      linarith
    exact hmain
  · exact full_range_program_resources
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact full_range_program_clean
    · intro X K k f lo s R hs hR hguard hf x
      exact full_range_phase_precision K k f lo s R hs hR hguard hf x
    · intro X K k f lo s R hs hR hguard hf x
      exact full_range_decoding_precision K k f lo s R hs hR hguard hf x
    · intro X K k v x
      refine ⟨((v x).val : ℤ), ?_⟩
      show ((v x).val : ℝ) / (2 : ℝ) ^ k = (((v x).val : ℤ) : ℝ) / (2 : ℝ) ^ k
      simp
    · intro k hex
      obtain ⟨n, hn⟩ := hex
      have h2 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      have h3 : (n : ℝ) * 3 = (2 : ℝ) ^ k := by
        have h := hn.symm
        rw [div_eq_iff (by positivity : (2 : ℝ) ^ k ≠ 0)] at h
        linarith
      have h4 : (n : ℤ) * 3 = ((2 : ℕ) ^ k : ℤ) := by exact_mod_cast h3
      have h5 : (3 : ℤ) ∣ ((2 : ℕ) ^ k : ℤ) := ⟨n, by linarith⟩
      have h6 : (3 : ℕ) ∣ 2 ^ k := by exact_mod_cast h5
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h6)
        (by omega)
  · refine ⟨?_, Qatlib.Concepts.GradientOracle.ReadoutTools.almostAffineVectorMedian⟩
    intro d M r ω
    have hcount : ∀ (r : ℕ) (v : Fin (2 * r + 1) → ℚ),
        (qSelect (List.ofFn v) r).2 ≤ 10000 * (2 * r + 1) :=
      fun r v => (rational_selection_median_exact_real_sorted_semantics r v).2
    have hp : ∀ j : Fin d, (gradientMedianCounted r ω j).2 ≤ 10000 * (2 * r + 1) := by
      intro j
      exact hcount r (fun t => gradientSignedValueQ M (ω t j))
    show medianComparisonCount d M r ω ≤ d * 10000 * (2 * r + 1)
    show ∑ j : Fin d, (gradientMedianCounted r ω j).2 ≤ d * 10000 * (2 * r + 1)
    calc
      ∑ j : Fin d, (gradientMedianCounted r ω j).2
          ≤ ∑ j : Fin d, 10000 * (2 * r + 1) := Finset.sum_le_sum (fun j _ => hp j)
      _ = Finset.univ.card • (10000 * (2 * r + 1)) :=
        Finset.sum_const (10000 * (2 * r + 1))
      _ = d • (10000 * (2 * r + 1)) := by rw [Finset.card_univ, Fintype.card_fin]
      _ = d * (10000 * (2 * r + 1)) := nsmul_eq_mul _ _
      _ = d * 10000 * (2 * r + 1) := by ring
  · intro d M r ω j
    rfl
  · intro K k v lo s
    rfl
  · intro n
    exact ⟨(localQFT_exact_gate_counts_and_wires n).2.2.2.1,
      (localQFT_exact_gate_counts_and_wires n).2.2.2.2.1⟩
  · intro n b
    exact (approxLocalQFT_actual_filter_and_cost n b).2.2.2.1
  · exact approxLocalQFT_forward_inverse_born_error
  · intro d M K k
    exact ⟨rfl, rfl⟩

end Qatlib.Concepts.GradientOracle.GradientAlgo
