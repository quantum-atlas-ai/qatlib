/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QGradient20.DressedUpdate.Stationary
import Qatlib.Papers.QGradient20.FilterBranch.Operator
import Qatlib.Papers.QGradient20.PhaseOracle.UnitInput

/-!
# Phase access to the dressed effective Hamiltonian

`effectiveHamiltonian` is the normalized complex derivative matrix at the dressed input.
Symmetric coefficients give a Hermitian contraction and unitary phase evolution; the actual
phase-estimation readout is a spectral mixture with an exact query count and physical-time
formula. The mathematical context is [GaoEtAl2021].

## Main statements

* `actual_dressed_qpe_Born`: The dressed input has spectral coefficient squared norms summing to
  one, and each actual phase-estimation outcome probability is their mixture of squared kernels
  at the negative quarter-scaled eigenvalues.
* `actual_dressed_phase_cost`: For positive `M`, the counted phase circuit uses `M - 1` queries
  and its physical evolution time at scale `1/4` is `(π/2)*(M - 1)`.

## References

* [Gao et al., 2021][GaoEtAl2021]
-/

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

/-- The spectrally normalized complex derivative matrix at the dressed input. -/
def effectiveHamiltonian {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ) (x : I → ℝ) :
    Matrix (Option I) (Option I) ℂ := normalizedMatrix (complexDerivative A x)

/-- Symmetric real polynomial coefficients give a Hermitian effective Hamiltonian. -/
theorem effectiveHamiltonian_hermitian {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ) (hA : A.IsSymm) (x : I → ℝ) :
    (effectiveHamiltonian A x).IsHermitian := normalizedMatrix_hermitian _ (complexDerivative_hermitian A hA x)

/-- The dressed effective Hamiltonian has operator norm at most one. -/
theorem effectiveHamiltonian_norm {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ) (x : I → ℝ) :
    ‖effectiveHamiltonian A x‖ ≤ 1 := normalizedMatrix_norm _

/-- For symmetric real coefficients, phase evolution of the effective Hamiltonian at parameter
`1/4` is unitary. See [GaoEtAl2021]. -/
theorem actual_phase_oracle_unitary {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ) (hA : A.IsSymm) (x : I → ℝ) :
    phaseEvolution (effectiveHamiltonian A x) (1/4) ∈ Matrix.unitaryGroup (Option I) ℂ :=
  phaseEvolution_unitary _ (effectiveHamiltonian_hermitian A hA x) _

/-- The dressed input has spectral coefficient squared norms summing to one, and each actual
phase-estimation outcome probability is their mixture of squared kernels at the negative
quarter-scaled eigenvalues. See [GaoEtAl2021]. -/
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

/-- For positive `M`, the counted phase circuit uses `M - 1` queries and its physical evolution
time at scale `1/4` is `(π/2)*(M - 1)`. See [GaoEtAl2021]. -/
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
