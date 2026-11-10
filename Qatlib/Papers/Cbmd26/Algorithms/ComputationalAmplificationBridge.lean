/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.ComputationalWorkspaceBridge
import Qatlib.Papers.Cbmd26.Algorithms.CountedAmplificationBridge
import Qatlib.Papers.Cbmd26.Algorithms.StaticCBMDParameters
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CBMD
open Matrix
open scoped Matrix.Norms.L2Operator ENNReal
variable {W Aux I : Type} [Fintype W] [DecidableEq W] [Fintype Aux] [DecidableEq Aux]
  [Fintype I] [DecidableEq I]

def ComputationalAmplificationResult (e : W ≃ Aux × I) (a₀ : Aux)
    (O : Matrix W W ℂ) (cs : List (AdjointStep W)) (B : Matrix I I ℂ)
    (i₀ : I) (ψ : QState I) (target : Matrix I I ℂ) (ε η : ℝ) : Prop :=
  let m := staticAmplificationWindow η
  ∃ hm : NeZero m,
  letI := hm
  let Bin := computationalWorkspaceInput e B
  let zero := e.symm (a₀,i₀)
  let S := computationalWorkspaceEvent e a₀
  let A := evaluate O cs * Bin
  ∃ (_hcs : WellFormedAdjointCircuit cs) (hA : A ∈ Matrix.unitaryGroup W ℂ),
    ENNReal.ofReal (1/8 : ℝ) ≤
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (randomizedAAHerald A hA zero S m) (fun x => x.2 = true) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (randomizedAAHerald A hA zero S m)
      (fun x => (preparedInputQueries
        (countedAAWord (preparedTrial cs) zero S (aaRounds x.1)) : ℝ≥0∞)) ≤
      ENNReal.ofReal ((4 * staticMassBudget + 1) / η) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (randomizedAAHerald A hA zero S m)
      (fun x => (preparedDataQueries
        (countedAAWord (preparedTrial cs) zero S (aaRounds x.1)) : ℝ≥0∞)) ≤
      ENNReal.ofReal (((4 * staticMassBudget + 1) / η) * (adjointQueryCount cs : ℝ)) ∧
    (∀ choice : Bool × Fin m,
      (preparedInputQueries (countedAAWord (preparedTrial cs) zero S (aaRounds choice)) : ℝ) ≤
        4 * (4 * staticMassBudget + 1) / η ∧
      (preparedDataQueries (countedAAWord (preparedTrial cs) zero S (aaRounds choice)) : ℝ) ≤
        4 * ((4 * staticMassBudget + 1) / η) * (adjointQueryCount cs : ℝ)) ∧
    (∀ k, PreparedCircuitValid (countedAAWord (preparedTrial cs) zero S k) ∧
      ApplyGate (evaluatePrepared O Bin (countedAAWord (preparedTrial cs) zero S k)) (Ket zero) =
        Run (preparedMark S) (preparedAACircuit A zero k) (Ket zero)) ∧
    (∀ choice : Bool × Fin m,
      (choice, true) ∈ (randomizedAAHerald A hA zero S m).support →
      ∃ (y : QState I) (z : ℂ),
        ConditionalState ((computationalWorkspaceFrame e a₀)ᴴ *ᵥ
          Run (preparedMark S) (preparedAACircuit A zero (aaRounds choice)) (Ket zero)) = some y ∧
        ‖z‖ = 1 ∧ Normalized y ∧ IsNormalizedApplication target ψ ((star z) • y) ε)

theorem computational_amplification (e : W ≃ Aux × I) (a₀ : Aux)
    (O : Matrix W W ℂ) (cs : List (AdjointStep W)) (B : Matrix I I ℂ)
    (hO : O ∈ Matrix.unitaryGroup W ℂ) (hcs : WellFormedAdjointCircuit cs)
    (hB : B ∈ Matrix.unitaryGroup I ℂ) (i₀ : I) (ψ : QState I)
    (hprepare : ApplyGate B (Ket i₀) = ψ)
    (target : Matrix I I ℂ) (scale error ε η : ℝ)
    (henc : BlockEncoding target (evaluate O cs)
      (computationalWorkspaceFrame e a₀) (computationalWorkspaceFrame e a₀) scale error)
    (hscale : scale ≤ 4 * staticMassBudget)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1)
    (htarget : η ≤ ‖stateVector (target *ᵥ ψ)‖) (herror : error ≤ ε * η / 4) :
    ComputationalAmplificationResult e a₀ O cs B i₀ ψ target ε η := by
  have hψ : Normalized ψ := by
    rw [← hprepare]
    exact normalized_applyGate hB (normalized_ket i₀)
  let F := computationalWorkspaceFrame e a₀
  let Bin := computationalWorkspaceInput e B
  let zero := e.symm (a₀,i₀)
  let S := computationalWorkspaceEvent e a₀
  let m := staticAmplificationWindow η
  have hw := static_chosen_window η hη hη1
  have hm : NeZero m := ⟨hw.1.ne'⟩
  letI := hm
  have hBin := computationalWorkspaceInput_unitary e B hB
  have hinit := computationalWorkspaceInput_prepare e B a₀ i₀ ψ hprepare
  have hproj := computationalWorkspaceFrame_rangeProjector e a₀
  have hwindow : 2 * scale / η ≤ (m : ℝ) := by
    have hs := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hscale (by norm_num : (0:ℝ) ≤ 2)) hη.le
    apply hs.trans
    convert! hw.2.1 using 1
    ring
  have hgap : error ≤ η/2 := by
    have hep := mul_le_mul_of_nonneg_right hε1 hη.le
    nlinarith only [herror, hep, hη.le]
  have haa := counted_blockEncoding_randomized_amplification target O Bin cs hO hBin hcs
    F F scale error η henc zero S ψ hψ hinit hproj hη htarget hgap m hwindow
  simp only [evaluate_preparedTrial] at haa
  have hA : evaluate O cs * Bin ∈ Matrix.unitaryGroup W ℂ :=
    (Matrix.unitaryGroup _ ℂ).mul_mem henc.unitary hBin
  have htotal : (((m : ℝ)+1)/2) * (adjointQueryCount cs : ℝ) ≤
      ((4 * staticMassBudget + 1) / η) * (adjointQueryCount cs : ℝ) :=
    mul_le_mul_of_nonneg_right hw.2.2 (Nat.cast_nonneg _)
  refine ⟨hm,hcs,hA,haa.1,haa.2.1.le.trans (ENNReal.ofReal_le_ofReal hw.2.2),
    haa.2.2.1.le.trans (ENNReal.ofReal_le_ofReal htotal),?_,haa.2.2.2.1,?_⟩
  · intro choice
    obtain ⟨hi,hd⟩ := randomizedAA_path_budget cs zero S m choice
    have hm1 : 1 ≤ 2*m := by have := hw.1; change 0 < m at this; omega
    have hworst : ((2*m-1 : ℕ) : ℝ) ≤ 4 * (((m:ℝ)+1)/2) := by
      rw [Nat.cast_sub hm1, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      linarith
    constructor
    · calc
        _ ≤ ((2*m-1 : ℕ) : ℝ) := Nat.cast_le.mpr hi
        _ ≤ 4 * (((m:ℝ)+1)/2) := hworst
        _ ≤ 4 * ((4*staticMassBudget+1)/η) := mul_le_mul_of_nonneg_left hw.2.2 (by norm_num)
        _ = _ := by ring
    · have hdR : (preparedDataQueries (countedAAWord (preparedTrial cs) zero S (aaRounds choice)) : ℝ) ≤
          ((2*m-1 : ℕ) : ℝ) * (adjointQueryCount cs : ℝ) := by
        simpa only [Nat.cast_mul] using! (Nat.cast_le (α := ℝ)).mpr hd
      calc
        _ ≤ ((2*m-1 : ℕ) : ℝ) * (adjointQueryCount cs : ℝ) := hdR
        _ ≤ (4 * (((m:ℝ)+1)/2)) * (adjointQueryCount cs : ℝ) :=
          mul_le_mul_of_nonneg_right hworst (Nat.cast_nonneg _)
        _ = 4 * ((((m:ℝ)+1)/2) * (adjointQueryCount cs : ℝ)) := by ring
        _ ≤ 4 * (((4*staticMassBudget+1)/η) * (adjointQueryCount cs : ℝ)) :=
          mul_le_mul_of_nonneg_left htotal (by norm_num)
        _ = _ := by ring
  · intro choice hs
    obtain ⟨y,z,hy,hz,hyn,happ⟩ := blockEncoding_randomized_supported_output target (evaluate O cs)
      Bin F F scale error henc hBin zero S ψ hψ hinit hproj (by linarith) m choice hs
    refine ⟨y,z,hy,hz,hyn,happ.1,happ.2.1,happ.2.2.trans ?_⟩
    apply (div_le_iff₀ (hη.trans_le htarget)).mpr
    have hεη := mul_le_mul_of_nonneg_left htarget hε.le
    nlinarith only [herror, hεη, mul_nonneg hε.le hη.le]

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
