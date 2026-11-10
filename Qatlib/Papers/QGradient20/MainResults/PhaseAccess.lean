/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QGradient20.DressedUpdate.Stationary
import Qatlib.Papers.QGradient20.FilterBranch.Operator
import Qatlib.Papers.QGradient20.PhaseOracle.UnitInput
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder RealInnerProductSpace
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LocalMachine.LocalTransport
namespace Qatlib.Papers.QGradient20.MainResults.PhaseAccess
open Qatlib.Papers.QGradient20.Polynomial
open Qatlib.Papers.QGradient20.DressedUpdate
open Qatlib.Papers.QGradient20.FilterBranch
open Qatlib.Papers.QGradient20.PhaseOracle
variable {I : Type} [Fintype I] [DecidableEq I]

def effectiveHamiltonian {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ) (x : I → ℝ) :
    Matrix (Option I) (Option I) ℂ := normalizedMatrix (complexDerivative A x)

theorem effectiveHamiltonian_hermitian {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ) (hA : A.IsSymm) (x : I → ℝ) :
    (effectiveHamiltonian A x).IsHermitian := normalizedMatrix_hermitian _ (complexDerivative_hermitian A hA x)

theorem effectiveHamiltonian_norm {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ) (x : I → ℝ) :
    ‖effectiveHamiltonian A x‖ ≤ 1 := normalizedMatrix_norm _

theorem actual_phase_oracle_unitary {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ) (hA : A.IsSymm) (x : I → ℝ) :
    phaseEvolution (effectiveHamiltonian A x) (1/4) ∈ Matrix.unitaryGroup (Option I) ℂ :=
  phaseEvolution_unitary _ (effectiveHamiltonian_hermitian A hA x) _

theorem actual_dressed_qpe_Born {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ) (hA : A.IsSymm) (x : I → ℝ)
    (M : ℕ) (hM : 0 < M) (z : Fin M) :
    let D := effectiveHamiltonian A x
    let hD := effectiveHamiltonian_hermitian A hA x
    (∑ j, ‖UnitInput.coefficients D hD (encoded x) j‖^2=1) ∧
    MeasureProb
      (Run (TensorGate (1 : Matrix (Fin M) (Fin M) ℂ) (controlOracle (phaseEvolution D (1/4))))
        (countedPhaseCircuit M)
        (TensorState (Ket (⟨0,hM⟩ : Fin M)) (TensorState (Ket false) (encoded x).ofLp)))
      ({z}×ˢ(Finset.univ : Finset (Bool×Option I)))=
      ∑ j,‖UnitInput.coefficients D hD (encoded x) j‖^2 *
        ‖qpeKernel M (-(1/4)*hD.eigenvalues j) z‖^2 :=
  UnitInput.actual_unit_input_Born _ (effectiveHamiltonian_hermitian A hA x) _ M hM _ (encoded_norm x) z

theorem actual_dressed_phase_cost {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ) (x : I → ℝ)
    (M : ℕ) (hM : 0 < M) :
    QueryCount (countedPhaseCircuit (I := Option I) M)=M-1 ∧
      physicalTime (Option I) M (1/4)=(Real.pi/2)*((M-1:ℕ):ℝ) := by
  refine ⟨(actual_counted_run (effectiveHamiltonian A x) (1/4) M hM (encoded x).ofLp).2.1,?_⟩
  rw [physicalTime_eq M hM]
  norm_num
  ring

end Qatlib.Papers.QGradient20.MainResults.PhaseAccess
