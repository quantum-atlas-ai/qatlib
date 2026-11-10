/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QGradient20.PhaseOracle.HermitianQpe
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder RealInnerProductSpace
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Papers.QGradient20.PhaseOracle

namespace Qatlib.Papers.QGradient20.PhaseOracle.ActualRun
variable {I : Type} [Fintype I] [DecidableEq I]

theorem eigenvalue_abs_le_norm (D : Matrix I I ℂ) (hD : D.IsHermitian) (j : I) : |hD.eigenvalues j|≤‖D‖ := by
  have h := ((Matrix.toEuclideanCLM (𝕜:=ℂ) (n:=I)) D).le_opNorm (hD.eigenvectorBasis j)
  have he : (Matrix.toEuclideanCLM (𝕜:=ℂ) (n:=I)) D (hD.eigenvectorBasis j)=
      (hD.eigenvalues j : ℝ)•hD.eigenvectorBasis j := by
    apply (EuclideanSpace.equiv I ℂ).injective
    exact hD.mulVec_eigenvectorBasis j
  rw [he,norm_smul,Real.norm_eq_abs,hD.eigenvectorBasis.orthonormal.1 j,
    mul_one,Matrix.l2_opNorm_toEuclideanCLM,mul_one] at h
  exact h

theorem corrected_signed_phase_range (D : Matrix I I ℂ) (hD : D.IsHermitian) (hDnorm : ‖D‖≤1)
    (τ : ℝ) (hτ0 : 0≤τ) (hτ1 : τ≤1/4) (j : I) : |-τ*hD.eigenvalues j|≤1/4 := by
  rw [abs_mul,abs_neg,abs_of_nonneg hτ0]
  exact (mul_le_mul_of_nonneg_left ((eigenvalue_abs_le_norm D hD j).trans hDnorm) hτ0).trans
    (by simpa using hτ1)

theorem actual_run_label_Born (D : Matrix I I ℂ) (τ : ℝ) (M : ℕ) (hM : 0<M) (ψ : I→ℂ) (z : Fin M) :
    MeasureProb
      (Run (TensorGate (1 : Matrix (Fin M) (Fin M) ℂ) (controlOracle (phaseEvolution D τ)))
        (countedPhaseCircuit M)
        (TensorState (Ket (⟨0,hM⟩ : Fin M)) (TensorState (Ket false) ψ)))
      ({z}×ˢ(Finset.univ : Finset (Bool×I)))=
      MarginalProbLeft (qpeOutput M (phaseEvolution D τ) ψ) {z} := by
  rw [(actual_counted_run D τ M hM ψ).1]
  simp [MeasureProb,MarginalProbLeft,BornProb,Fintype.sum_prod_type]

theorem actual_run_spectral_Born (D : Matrix I I ℂ) (hD : D.IsHermitian) (τ : ℝ)
    (M : ℕ) (hM : 0<M) (c : I→ℂ) (z : Fin M) :
    MeasureProb
      (Run (TensorGate (1 : Matrix (Fin M) (Fin M) ℂ) (controlOracle (phaseEvolution D τ)))
        (countedPhaseCircuit M)
        (TensorState (Ket (⟨0,hM⟩ : Fin M))
          (TensorState (Ket false) (∑ j,c j•(hD.eigenvectorBasis j : I→ℂ)))))
      ({z}×ˢ(Finset.univ : Finset (Bool×I)))=
      ∑ j,‖c j‖^2*‖qpeKernel M (-τ*hD.eigenvalues j) z‖^2 := by
  rw [actual_run_label_Born,actual_spectral_Born D hD τ M hM]

end Qatlib.Papers.QGradient20.PhaseOracle.ActualRun
