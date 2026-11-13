/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.ScaleEightCoherentAmplification
import Qatlib.Concepts.QspSimulation.Achievability.CountedHamiltonian

/-!
# Counted simulation with clean workspace

This module combines a counted Hamiltonian block-encoding circuit with scale-eight coherent
amplification to approximate Hamiltonian evolution on the full encoded state, including its
workspace. It records the exact amplification resource overhead and derives an arbitrary
positive relative vector-error bound, connecting QSP simulation [LowChuang2017] with coherent
use of block encodings [GilyenSuLowWiebe2019].

## Main statements

* `signal_simulation_actual_clean_counted_consumer` gives base counts of `4*n+1` queries and
  `4*n+6` gates, amplified counts of `27*(4*n+1)` and `27*(4*n+6)+79`, and clean-workspace error
  at most `η` times the input norm.
- `scaleEight_demo_encoding` constructs an exact scale-eight encoding of the identity.
* `scale_eight_rotation_actual_consumer` verifies exact clean action for the demonstration,
  using 27 queries and 79 gates.

## References

* [Low and Chuang, 2017][LowChuang2017], *Optimal Hamiltonian Simulation by Quantum Signal
  Processing*.
* [Gilyen, Su, Low, and Wiebe, 2019][GilyenSuLowWiebe2019], *Quantum singular value
  transformation and beyond: exponential improvements for quantum matrix arithmetics*.
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
namespace Qatlib.Concepts.QspSimulation.Achievability
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical Matrix.Norms.L2Operator

/-- For a Hermitian `A` with projected unitary encoding and any positive `η`, there is a
well-formed Hamiltonian word with `4*n+1` queries and `4*n+6` gates whose scale-eight
amplification uses `27*(4*n+1)` queries and `27*(4*n+6)+79` gates. On every encoded input,
the amplified word approximates `hamiltonianEvolution A t` in the full workspace with vector
error at most `η` times the input norm. -/
theorem signal_simulation_actual_clean_counted_consumer (H I : Type)
    [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ) (t η : ℝ)
    (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F) (hη : 0 < η) :
    ∃ (n : ℕ) (cs : List (AdjointStep (Bool × (Bool × H)))),
      WellFormedAdjointCircuit cs ∧ adjointQueryCount cs = 4*n+1 ∧
      adjointGateCount cs = 4*n+6 ∧
      adjointQueryCount (scaleEightAmplifyWord (hamiltonianFrame F) cs) = 27*(4*n+1) ∧
      adjointGateCount (scaleEightAmplifyWord (hamiltonianFrame F) cs) = 27*(4*n+6)+79 ∧
      ∀ ψ : QState I, ‖toEuclidean_fromVec
        (evaluate (TensorGate (1 : Matrix Bool Bool ℂ)
          (controlOracle (parallelOracle (J := Bool) U)))
          (scaleEightAmplifyWord (hamiltonianFrame F) cs)*ᵥ
          (scaleEightFrame (hamiltonianFrame F)*ᵥψ)-
          scaleEightFrame (hamiltonianFrame F)*ᵥ(hamiltonianEvolution A t*ᵥψ))‖ ≤
        η*‖toEuclidean_fromVec ψ‖ := by
  obtain ⟨n,cs,hcs,hbe,hq,hg⟩ := hamiltonianSimulation_counted_exists hA h t
    (show 0 < η^2/6750 by positivity)
  have hc := scale_eight_three_level_actual_counts (Bool × (Bool × H)) I
    (hamiltonianFrame F) cs hbe.right_isometry hcs
  refine ⟨n,cs,hcs,hq,hg,?_,?_,?_⟩
  · rw [hc.2.1,hq]
  · rw [hc.2.2,hg]
  · intro ψ
    have he := scale_eight_noisy_clean_workspace_bound (Bool × (Bool × H)) I
      (controlOracle (parallelOracle (J := Bool) U)) (hamiltonianFrame F) cs
      (hamiltonianEvolution A t) (η^2/6750)
      (controlOracle_unitary (parallelOracle_unitary h.unitary)) hcs
      (Qatlib.Foundations.PureStateMath.hamiltonianEvolution_unitary hA t) hbe ψ
    have hs : Real.sqrt (6750*(η^2/6750)) = η := by
      rw [show (6750 : ℝ)*(η^2/6750) = η^2 by ring, Real.sqrt_sq hη.le]
    simpa only [hs] using! he

/-- The tensor product of `scaleEightDemoRotation` with the one-dimensional identity is unitary
and gives an exact scale-eight `BlockEncoding` of the identity in the frame
`scaleEightFrame` of the identity. -/
theorem scaleEight_demo_encoding :
    TensorGate scaleEightDemoRotation (1 : Matrix Unit Unit ℂ) ∈
      Matrix.unitaryGroup (Bool × Unit) ℂ ∧
    BlockEncoding (1 : Matrix Unit Unit ℂ)
      (TensorGate scaleEightDemoRotation (1 : Matrix Unit Unit ℂ))
      (scaleEightFrame (1 : Matrix Unit Unit ℂ))
      (scaleEightFrame (1 : Matrix Unit Unit ℂ)) 8 0 := by
  have hu := tensorGate_unitary (scaleEightRotation_unitary (1/8) (by norm_num))
    (Submonoid.one_mem (Matrix.unitaryGroup Unit ℂ))
  have hr := scaleEightFrame_isometry (1 : Matrix Unit Unit ℂ) (by simp [IsIsometry])
  refine ⟨hu,hu,hr,hr,by norm_num,le_rfl,?_⟩
  have hc : (8 : ℝ) • compress (scaleEightFrame (1 : Matrix Unit Unit ℂ))
      (TensorGate scaleEightDemoRotation (1 : Matrix Unit Unit ℂ))
      (scaleEightFrame (1 : Matrix Unit Unit ℂ)) = (1 : Matrix Unit Unit ℂ) := by
    rw [scaleEightFrame_compress]
    ext i j
    norm_num [scaleEightDemoRotation, scaleEightRotation, compress, Complex.real_smul]
  rw [hc,sub_self,norm_zero]

/-- For the one-forward-query demonstration word, `scaleEightAmplifyWord` uses exactly 27
queries and 79 gates and acts identically on the specified encoded `Ket ()`. The
demonstration oracle is unitary and provides an exact scale-eight `BlockEncoding` of the
identity. -/
theorem scale_eight_rotation_actual_consumer :
    let R := scaleEightFrame (1 : Matrix Unit Unit ℂ)
    let O := TensorGate scaleEightDemoRotation (1 : Matrix Unit Unit ℂ)
    let cs : List (AdjointStep (Bool × Unit)) := [.forward]
    O ∈ Matrix.unitaryGroup (Bool × Unit) ℂ ∧
    BlockEncoding (1 : Matrix Unit Unit ℂ) O R R 8 0 ∧
    adjointQueryCount (scaleEightAmplifyWord R cs) = 27 ∧
    adjointGateCount (scaleEightAmplifyWord R cs) = 79 ∧
    evaluate (TensorGate (1 : Matrix Bool Bool ℂ) O) (scaleEightAmplifyWord R cs)*ᵥ
      (scaleEightFrame R*ᵥKet ()) = scaleEightFrame R*ᵥKet () := by
  (try dsimp only)
  have h := scaleEight_demo_encoding
  have hw : WellFormedAdjointCircuit ([.forward] : List (AdjointStep (Bool × Unit))) := by simp
  have he : evaluate (TensorGate scaleEightDemoRotation (1 : Matrix Unit Unit ℂ))
      ([.forward] : List (AdjointStep (Bool × Unit))) =
      TensorGate scaleEightDemoRotation (1 : Matrix Unit Unit ℂ) := by simp [evaluate,instructionMatrix]
  have hc := scale_eight_three_level_actual_counts (Bool × Unit) Unit
    (scaleEightFrame (1 : Matrix Unit Unit ℂ)) [.forward] h.2.right_isometry hw
  refine ⟨h.1,h.2,?_,?_,?_⟩
  · simpa [adjointQueryCount] using! hc.2.1
  · simpa [adjointGateCount] using! hc.2.2
  · have hf := scale_eight_exact_clean_amplification (Bool × Unit) Unit
      (TensorGate scaleEightDemoRotation (1 : Matrix Unit Unit ℂ))
      (scaleEightFrame (1 : Matrix Unit Unit ℂ)) [.forward] (1 : Matrix Unit Unit ℂ)
      h.1 hw (Submonoid.one_mem _) (by rw [he]; exact h.2) (Ket ())
    simpa only [Matrix.one_mulVec] using! hf
end Qatlib.Concepts.QspSimulation.Achievability
