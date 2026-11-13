/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FreshCopyExec.QpeConsumers.DyadicControlledSwap
import Qatlib.Concepts.FreshCopyExec.QpeConsumers.LocalControlledCopyBridge
import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws

/-!
# Numerical controlled-copy steps

`numericCopyRawStep` executes a numerically synthesized local controlled swap, then discards the
fresh copy and auxiliary registers. The resulting map agrees exactly with the abstract
controlled-copy map at `copyPhaseEffectiveAngle`.

The module bounds the error relative to angle `π / 2^b`, including arbitrary finite reference
registers. This supplies a numerical implementation of the density matrix exponentiation
primitive of [LloydMohseniRebentrost2014].

## Main statements

* `numericCopyRawStep_eq`: identifies the discarded local execution with the abstract
  effective-angle map.
* `numericCopy_reference_error`: bounds the amplified trace-norm error on positive inputs.
* `numerical_copy_actual_discard_reference_error`: packages the execution identities and
  reference-register error bound.

## References

* [Lloyd et al., 2014][LloydMohseniRebentrost2014]
-/

open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.ReferenceError.DensityToRaw
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.BlockEncoding.EncodingCore

namespace Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- Executes the numerical controlled-swap word on a framed input with a fresh copy of `rho`,
then traces out the auxiliary and copy registers. -/
noncomputable def numericCopyRawStep (n : ℕ) (rho : Operator (2^n)) (b k : ℕ)
    (X : Matrix (Bool × Fin (2^n)) (Bool × Fin (2^n)) ℂ) :=
  let F := localCopyFrame n
  let W := reflectionProgramMatrix (numericControlledSwapSteps n b k)
  traceRightB (Matrix.traceRight (relabelGate (localCopySplit n) (W*(F*tensorCopyB rho X*Fᴴ)*Wᴴ)))
/-- Transports `numericCopyRawStep` from the Boolean control layout to the flattened
finite-index layout. -/
noncomputable def numericCopyFinStep (n : ℕ) (rho : Operator (2^n)) (b k : ℕ)
    (X : Operator (2*(2^n))) : Operator (2*(2^n)) :=
  relabelGate (controlDataEquiv (2^n)) (numericCopyRawStep n rho b k
    (relabelGate (controlDataEquiv (2^n)).symm X))
/-- Applies a matrix transformation to each block determined by a reference register of size
`r`. -/
noncomputable def numericAmplification {D : ℕ} (T : Operator D → Operator D) (r : ℕ)
    (X : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ) :
    Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ :=
  Matrix.of (fun x y => T (fun i j => X (x.1,i) (y.1,j)) x.2 y.2)

/-- The raw numerical copy step equals the abstract controlled-copy map at the computed
effective angle. -/
theorem numericCopyRawStep_eq (n b k : ℕ) (rho : Operator (2^n))
    (X : Matrix (Bool × Fin (2^n)) (Bool × Fin (2^n)) ℂ) :
    numericCopyRawStep n rho b k X = controlledCopyRawMap rho (copyPhaseEffectiveAngle b k) X := by
  have hi := (numerical_controlled_swap_clean_and_error n b k).2.2.2.1
  have hh := congrArg Matrix.conjTranspose hi
  simp only [Matrix.conjTranspose_mul] at hh
  dsimp only [numericCopyRawStep,controlledCopyRawMap]
  have he : reflectionProgramMatrix (numericControlledSwapSteps n b k)*
      (localCopyFrame n*tensorCopyB rho X*(localCopyFrame n)ᴴ)*
      (reflectionProgramMatrix (numericControlledSwapSteps n b k))ᴴ =
      localCopyFrame n*(controlledSwapRawGate (2^n) (copyPhaseEffectiveAngle b k)*tensorCopyB rho X*
        (controlledSwapRawGate (2^n) (copyPhaseEffectiveAngle b k))ᴴ)*(localCopyFrame n)ᴴ := by
    rw [← Matrix.mul_assoc,← Matrix.mul_assoc,hi]
    simp only [Matrix.mul_assoc]
    rw [hh]
  rw [he,localCopyFrame_actual_scratch_discard]

/-- The flattened numerical copy step equals the abstract controlled-copy channel map at the
computed effective angle. -/
theorem numericCopyFinStep_eq (n b k : ℕ) (rho : Operator (2^n))
    (X : Operator (2*(2^n))) :
    numericCopyFinStep n rho b k X = controlledCopyChannelMap rho (copyPhaseEffectiveAngle b k) X := by
  rw [numericCopyFinStep,numericCopyRawStep_eq]
  have h := controlledCopyChannelMap_relabel (2^n) rho (copyPhaseEffectiveAngle b k)
    (relabelGate (controlDataEquiv (2^n)).symm X)
  have hr : relabelGate (controlDataEquiv (2^n)) (relabelGate (controlDataEquiv (2^n)).symm X) = X := by
    ext i j
    simp [relabelGate]
  rw [hr] at h
  exact h.symm

/-- Blockwise numerical amplification agrees with channel amplification of the effective-angle
controlled-copy map. -/
theorem numericAmplification_eq (n b k : ℕ) (rho : Operator (2^n)) (r : ℕ)
    (X : Matrix (Fin r × Fin (2*(2^n))) (Fin r × Fin (2*(2^n))) ℂ) :
    numericAmplification (numericCopyFinStep n rho b k) r X =
      ChannelAmplification (controlledCopyChannelMap rho (copyPhaseEffectiveAngle b k)) r X := by
  ext x y
  simp only [numericAmplification,ChannelAmplification,Matrix.of_apply,numericCopyFinStep_eq]

/-- Compressing the fast controlled-swap program through the clean local frame gives the raw
controlled-swap gate. -/
theorem fastControlledSwap_compress (n : ℕ) (t : ℝ) :
    compress (localCopyFrame n) (reflectionProgramMatrix (fastControlledSwapSteps n t)) (localCopyFrame n) =
      controlledSwapRawGate (2^n) t := by
  have hi := (direct_parity_controlled_swap_clean_word n t).2.2.1
  have hF : (localCopyFrame n)ᴴ*localCopyFrame n = 1 := localCopyFrame_isometry n
  rw [compress,Matrix.mul_assoc,hi,← Matrix.mul_assoc,hF,Matrix.one_mul]

/-- The operator-norm error between the effective-angle and target-angle raw controlled swaps is
at most `2⁻ᵏ`. -/
theorem numericCopyRawGate_error (n b k : ℕ) :
    ‖controlledSwapRawGate (2^n) (copyPhaseEffectiveAngle b k)-
      controlledSwapRawGate (2^n) (Real.pi/(2^b:ℕ))‖ ≤ ((2:ℝ)⁻¹)^k := by
  have hf := isometry_norm_le (localCopyFrame_isometry n)
  have hh : ‖(localCopyFrame n)ᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact hf
  have hp := numericControlledSwap_error n b k
  rw [numericControlledSwap_effective] at hp
  rw [← fastControlledSwap_compress n (copyPhaseEffectiveAngle b k),
    ← fastControlledSwap_compress n (Real.pi/(2^b:ℕ))]
  unfold compress
  rw [← Matrix.sub_mul,← Matrix.mul_sub]
  calc
    _ ≤ ‖(localCopyFrame n)ᴴ*(_-_)‖*‖localCopyFrame n‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ (‖(localCopyFrame n)ᴴ‖*‖_-_‖)*‖localCopyFrame n‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ ≤ (1*((2:ℝ)⁻¹)^k)*1 := by gcongr
    _ = _ := by ring

/-- The operator-norm error between the effective-angle and target-angle reference gates is at
most `2⁻ᵏ`. -/
theorem numericCopyReferenceGate_error (n b k r : ℕ) :
    ‖controlledCopyReferenceGate (2^n) r (copyPhaseEffectiveAngle b k)-
      controlledCopyReferenceGate (2^n) r (Real.pi/(2^b:ℕ))‖ ≤ ((2:ℝ)⁻¹)^k := by
  have hraw := numericCopyRawGate_error n b k
  have ht : ‖controlledSwapGateTensor (2^n) (copyPhaseEffectiveAngle b k)-
      controlledSwapGateTensor (2^n) (Real.pi/(2^b:ℕ))‖ ≤ ((2:ℝ)⁻¹)^k := by
    simpa only [controlledSwapGateTensor,l2_norm_relabelGate_sub] using! hraw
  rw [controlledCopyReferenceGate,controlledCopyReferenceGate,l2_norm_relabelGate_sub]
  have he : ∀ (A B : Matrix (Fin (2*(2^n)) × Fin (2^n)) (Fin (2*(2^n)) × Fin (2^n)) ℂ),
      TensorGate (1:Operator r) A-TensorGate (1:Operator r) B = TensorGate (1:Operator r) (A-B) := by
    intro A B
    ext ⟨a,i⟩ ⟨b,j⟩
    simp only [tensorGate_apply,Matrix.sub_apply]
    ring
  rw [he,l2_norm_tensorGate]
  exact (mul_le_mul l2_norm_one_le ht (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

/-- Conjugations by unitaries `U` and `V` differ in trace norm by at most `2 * ‖U - V‖ *
traceNorm X`. -/
theorem numeric_conjugation_error {I : Type} [Fintype I] [DecidableEq I]
    (U V X : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (hV : V ∈ Matrix.unitaryGroup I ℂ) :
    Matrix.traceNorm (U*X*Uᴴ-V*X*Vᴴ) ≤ 2*‖U-V‖*Matrix.traceNorm X := by
  have hnX := Matrix.traceNorm_nonneg X
  have hnU := l2_norm_unitary_le_one hU
  have hnV := l2_norm_unitary_le_one hV
  have hnH : ‖Vᴴ‖ ≤ 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact hnV
  have he : U*X*Uᴴ-V*X*Vᴴ = U*X*(Uᴴ-Vᴴ)+(U-V)*X*Vᴴ := by
    simp only [Matrix.mul_sub,Matrix.sub_mul]
    abel
  rw [he]
  calc
    _ ≤ (U*X*(Uᴴ-Vᴴ)).traceNorm+((U-V)*X*Vᴴ).traceNorm := Matrix.traceNorm_add_le _ _
    _ ≤ ((U*X).traceNorm*‖Uᴴ-Vᴴ‖)+(((U-V)*X).traceNorm*‖Vᴴ‖) :=
      add_le_add (Matrix.traceNorm_mul_le_traceNorm_opNorm _ _) (Matrix.traceNorm_mul_le_traceNorm_opNorm _ _)
    _ ≤ ((‖U‖*X.traceNorm)*‖Uᴴ-Vᴴ‖)+((‖U-V‖*X.traceNorm)*‖Vᴴ‖) := by
      gcongr <;> exact Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
    _ ≤ ((1*X.traceNorm)*‖U-V‖)+((‖U-V‖*X.traceNorm)*1) := by
      rw [← Matrix.conjTranspose_sub,Matrix.l2_opNorm_conjTranspose]
      gcongr
    _ = _ := by ring

/-- The controlled-copy reference gate is unitary for every system size, reference size, and
real angle. -/
theorem numericCopyReferenceGate_unitary (D r : ℕ) (t : ℝ) :
    controlledCopyReferenceGate D r t ∈ Matrix.unitaryGroup ((Fin r × Fin (2*D)) × Fin D) ℂ := by
  unfold controlledCopyReferenceGate
  apply relabelGate_mem_unitary
  apply tensorGate_unitary (Matrix.unitaryGroup (Fin r) ℂ).one_mem
  unfold controlledSwapGateTensor
  exact relabelGate_mem_unitary (controlledSwapRawGate_unitarity D t) _

/-- For a density operator `rho` and positive input `X`, the amplified effective-angle copy map
differs from the target-angle map by at most `4 * 2⁻ᵏ * re (trace X)` in trace norm. -/
theorem numericCopy_reference_error (n b k r : ℕ) (rho : Operator (2^n)) (hrho : IsDensityOperator rho)
    (X : Matrix (Fin r × Fin (2*(2^n))) (Fin r × Fin (2*(2^n))) ℂ) (hX : X.PosSemidef) :
    Matrix.traceNorm (ChannelAmplification (controlledCopyChannelMap rho (copyPhaseEffectiveAngle b k)) r X-
      ChannelAmplification (controlledCopyChannelMap rho (Real.pi/(2^b:ℕ))) r X) ≤
        4*((2:ℝ)⁻¹)^k*(Matrix.trace X).re := by
  let U := controlledCopyReferenceGate (2^n) r (copyPhaseEffectiveAngle b k)
  let V := controlledCopyReferenceGate (2^n) r (Real.pi/(2^b:ℕ))
  let Y := TensorGate X rho
  have hy : Y.PosSemidef := hX.kronecker hrho.1
  have hu := numericCopyReferenceGate_unitary (2^n) r (copyPhaseEffectiveAngle b k)
  have hv := numericCopyReferenceGate_unitary (2^n) r (Real.pi/(2^b:ℕ))
  have hdiff : (U*Y*Uᴴ-V*Y*Vᴴ).IsHermitian :=
    (hy.mul_mul_conjTranspose_same U).isHermitian.sub (hy.mul_mul_conjTranspose_same V).isHermitian
  have hyn : Y.traceNorm = (Matrix.trace X).re := by
    rw [traceNorm_tensorGate X hX rho hrho.1,density_traceNorm_eq_one rho hrho,mul_one,psd_traceNorm_eq_trace X hX]
  have hx0 : 0 ≤ (Matrix.trace X).re := by
    rw [← psd_traceNorm_eq_trace X hX]; exact Matrix.traceNorm_nonneg _
  have he := numericCopyReferenceGate_error n b k r
  rw [controlledCopy_reference_actual_bridge,controlledCopy_reference_actual_bridge,← Matrix.traceRight_sub]
  change (Matrix.traceRight (U*Y*Uᴴ-V*Y*Vᴴ)).traceNorm ≤ _
  calc
    _ ≤ (U*Y*Uᴴ-V*Y*Vᴴ).traceNorm := traceRight_hermitian_trace_contraction _ hdiff
    _ ≤ 2*‖U-V‖*Y.traceNorm := numeric_conjugation_error U V Y hu hv
    _ ≤ 2*((2:ℝ)⁻¹)^k*(Matrix.trace X).re := by rw [hyn]; gcongr
    _ ≤ _ := by have hp : 0 ≤ ((2:ℝ)⁻¹)^k := by positivity
                nlinarith [mul_nonneg hp hx0]

/-- Identifies numerical discard execution with the effective-angle copy map and its reference
amplification. For density operators and positive inputs, the target-angle trace-norm error
is at most `4 * 2⁻ᵏ * re (trace X)`. -/
theorem numerical_copy_actual_discard_reference_error : ∀ (n b k : ℕ) (rho : Operator (2^n)),
  (∀ X : Matrix (Bool × Fin (2^n)) (Bool × Fin (2^n)) ℂ,
    numericCopyRawStep n rho b k X = controlledCopyRawMap rho (copyPhaseEffectiveAngle b k) X) ∧
  (∀ (r : ℕ) (X : Matrix (Fin r × Fin (2*(2^n))) (Fin r × Fin (2*(2^n))) ℂ),
    numericAmplification (numericCopyFinStep n rho b k) r X =
      ChannelAmplification (controlledCopyChannelMap rho (copyPhaseEffectiveAngle b k)) r X) ∧
  (IsDensityOperator rho → ∀ (r : ℕ)
    (X : Matrix (Fin r × Fin (2*(2^n))) (Fin r × Fin (2*(2^n))) ℂ), X.PosSemidef →
    Matrix.traceNorm (numericAmplification (numericCopyFinStep n rho b k) r X -
      ChannelAmplification (controlledCopyChannelMap rho (Real.pi/(2^b:ℕ))) r X) ≤
        4*((2:ℝ)⁻¹)^k*(Matrix.trace X).re) := by
  intro n b k rho
  refine ⟨numericCopyRawStep_eq n b k rho, numericAmplification_eq n b k rho,?_⟩
  intro hrho r X hX
  rw [numericAmplification_eq]
  exact numericCopy_reference_error n b k r rho hrho X hX

end Qatlib.Concepts.FreshCopyExec.QpeConsumers
