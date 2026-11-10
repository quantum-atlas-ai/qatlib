/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QGradient20.PhaseOracle.ActualRun
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1400000
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
open Qatlib.Papers.QGradient20.PhaseOracle Qatlib.Papers.QGradient20.PhaseOracle.ActualRun

namespace Qatlib.Papers.QGradient20.PhaseOracle.UnitInput
variable {I : Type} [Fintype I] [DecidableEq I]

theorem unit_input_normalized (x : EuclideanSpace ℂ I) (hx : ‖x‖=1) : Normalized (WithLp.ofLp x) := by
  rw [normalized_iff_inner_self,← inner_euclidean_fromVec]
  change inner ℂ x x=1
  rw [inner_self_eq_norm_sq_to_K,hx]
  norm_num

def coefficients (D : Matrix I I ℂ) (hD : D.IsHermitian) (x : EuclideanSpace ℂ I) (j : I) : ℂ :=
  inner ℂ (hD.eigenvectorBasis j) x

theorem actual_input_expansion (D : Matrix I I ℂ) (hD : D.IsHermitian) (x : EuclideanSpace ℂ I) :
    (∑ j,coefficients D hD x j•(hD.eigenvectorBasis j : I→ℂ))=WithLp.ofLp x := by
  funext i
  have h := congrArg (fun y : EuclideanSpace ℂ I => y i) (hD.eigenvectorBasis.sum_repr' x)
  simpa only [coefficients,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,Pi.smul_apply] using h

theorem coefficients_mass_one (D : Matrix I I ℂ) (hD : D.IsHermitian)
    (x : EuclideanSpace ℂ I) (hx : ‖x‖=1) : ∑ j,‖coefficients D hD x j‖^2=1 := by
  simpa only [coefficients,hx,one_pow] using hD.eigenvectorBasis.sum_sq_norm_inner_right x

theorem actual_unit_run_normalized (D : Matrix I I ℂ) (hD : D.IsHermitian) (τ : ℝ)
    (M : ℕ) (hM : 0<M) (x : EuclideanSpace ℂ I) (hx : ‖x‖=1) :
    Normalized
      (Run (TensorGate (1 : Matrix (Fin M) (Fin M) ℂ) (controlOracle (phaseEvolution D τ)))
        (countedPhaseCircuit M)
        (TensorState (Ket (⟨0,hM⟩ : Fin M)) (TensorState (Ket false) (WithLp.ofLp x)))) := by
  apply (actual_counted_run D τ M hM (WithLp.ofLp x)).2.2.2.normalized_run
  · exact tensorGate_unitary (by simp) (controlOracle_unitary (phaseEvolution_unitary D hD τ))
  · exact normalized_tensorState (normalized_ket _) (normalized_tensorState (normalized_ket _)
      (unit_input_normalized x hx))

theorem actual_unit_input_Born (D : Matrix I I ℂ) (hD : D.IsHermitian) (τ : ℝ)
    (M : ℕ) (hM : 0<M) (x : EuclideanSpace ℂ I) (hx : ‖x‖=1) (z : Fin M) :
    (∑ j,‖coefficients D hD x j‖^2=1) ∧
    MeasureProb
      (Run (TensorGate (1 : Matrix (Fin M) (Fin M) ℂ) (controlOracle (phaseEvolution D τ)))
        (countedPhaseCircuit M)
        (TensorState (Ket (⟨0,hM⟩ : Fin M)) (TensorState (Ket false) (WithLp.ofLp x))))
      ({z}×ˢ(Finset.univ : Finset (Bool×I)))=
      ∑ j,‖coefficients D hD x j‖^2*‖qpeKernel M (-τ*hD.eigenvalues j) z‖^2 := by
  refine ⟨coefficients_mass_one D hD x hx,?_⟩
  simpa only [actual_input_expansion] using
      actual_run_spectral_Born D hD τ M hM (coefficients D hD x) z

end Qatlib.Papers.QGradient20.PhaseOracle.UnitInput
