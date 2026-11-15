/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.LcuPostselect.ScaledLCU.ApproximateCoefficientLCU
public import Qatlib.Concepts.ClusterPatterns.WireComposition.PauliMixtureTwirling

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.BlockEncoding

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.ClusterPatterns.WireComposition

namespace Qatlib.Concepts.OperatorAccess.EncodedAccess

open Matrix Qatlib.Concepts.BlockEncoding

open scoped Matrix.Norms.L2Operator

set_option linter.unusedSectionVars false

/-- The Pauli X gate block-encodes its scalar identity perturbation with scale one and error
bounded by the nonnegative perturbation size. -/
private theorem pauliX_perturbed_encoding (δ : ℝ) (hδ : 0 ≤ δ) :
    BlockEncoding (pauliXChoice true + (δ : ℂ) • (1 : Operator 2)) (pauliXChoice true)
      (1 : Matrix (Fin 2) (Fin 2) ℂ) (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 δ := by
  have hcomp : compress (1 : Matrix (Fin 2) (Fin 2) ℂ) (pauliXChoice true) 1
      = pauliXChoice true := by
    rw [compress, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  refine ⟨pauliXChoice_unitary true, by simp [IsIsometry], by simp [IsIsometry],
    by norm_num, hδ, ?_⟩
  rw [hcomp, one_smul, add_sub_cancel_left, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hδ, l2_norm_one_eq, mul_one]

/-- The Pauli Z gate block-encodes twice Pauli Z plus a Pauli X perturbation with scale two and
error bounded by the nonnegative perturbation size. -/
private theorem pauliZ_perturbed_encoding (δ : ℝ) (hδ : 0 ≤ δ) :
    BlockEncoding ((2 : ℂ) • (pauliZChoice true) + (δ : ℂ) • (pauliXChoice true))
      (pauliZChoice true) (1 : Matrix (Fin 2) (Fin 2) ℂ) (1 : Matrix (Fin 2) (Fin 2) ℂ) 2 δ := by
  have hcomp : compress (1 : Matrix (Fin 2) (Fin 2) ℂ) (pauliZChoice true) 1
      = pauliZChoice true := by
    rw [compress, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  refine ⟨pauliZChoice_unitary true, by simp [IsIsometry], by simp [IsIsometry],
    by norm_num, hδ, ?_⟩
  have hreal : ((2 : ℝ) • (pauliZChoice true : Operator 2))
      = (2 : ℂ) • (pauliZChoice true) := by
    ext a b
    simp [Complex.real_smul]
  rw [hcomp, hreal, add_sub_cancel_left, norm_smul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hδ, l2_norm_unitary_eq_one (pauliXChoice_unitary true),
    mul_one]

/-- The noisy two-term Pauli LCU has scale three and error at most twice the perturbation size,
and its Pauli factors do not commute. -/
theorem encoding_chain_pauli_consumers : ∀ (δ : ℝ), 0 ≤ δ →
    let U : Fin 2 → Operator 2 :=
        fun j => if j = 0 then (pauliXChoice true) else (pauliZChoice true)
    let c : Fin 2 → ℂ := fun j => if j = 0 then 1 else Complex.I
    let α : Fin 2 → ℝ := fun j => if j = 0 then 1 else 2
    let A : Fin 2 → Operator 2 :=
        fun j => if j = 0 then (pauliXChoice true) + (δ:ℂ) • 1 else (2:ℂ) • (pauliZChoice true) + (δ:ℂ) • (pauliXChoice true)
    BlockEncoding (∑ j, c j • A j) (coefficientLCUUnitary (scaledLCUCoefficients c α) U 0)
      (encodingFiber (I := Fin 2) (0 : Fin 2)) (encodingFiber (I := Fin 2) (0 : Fin 2)) 3 (2*δ) ∧
    (pauliXChoice true)*(pauliZChoice true) ≠ (pauliZChoice true)*(pauliXChoice true) := by
  intro δ hδ
  have hmass : 0 < coefficientMass (scaledLCUCoefficients
      (fun j : Fin 2 => if j = 0 then 1 else Complex.I) (fun j : Fin 2 => if j = 0 then 1 else 2)) := by
    have h8 := (scaled_lcu_coefficient_mass (fun j : Fin 2 => if j = 0 then 1 else Complex.I)
      (fun j : Fin 2 => if j = 0 then 1 else 2) (fun j => by fin_cases j <;> norm_num)).1
    rw [h8]
    norm_num
  have hG9 := scaled_approximate_lcu_encoding (J := Fin 2) (H := Fin 2) (O := Fin 2)
    (I := Fin 2) (0 : Fin 2)
    (fun j : Fin 2 => if j = 0 then (pauliXChoice true) + (δ:ℂ) • 1
      else (2:ℂ) • (pauliZChoice true) + (δ:ℂ) • (pauliXChoice true))
    (fun j : Fin 2 => if j = 0 then (pauliXChoice true) else (pauliZChoice true))
    (1 : Matrix (Fin 2) (Fin 2) ℂ) (1 : Matrix (Fin 2) (Fin 2) ℂ)
    (fun j : Fin 2 => if j = 0 then 1 else Complex.I)
    (fun j : Fin 2 => if j = 0 then 1 else 2) (fun _ => δ)
    (fun j => by
      fin_cases j
      · exact pauliX_perturbed_encoding δ hδ
      · exact pauliZ_perturbed_encoding δ hδ)
    hmass
  have hframe : tagFrame (0 : Fin 2) (1 : Matrix (Fin 2) (Fin 2) ℂ)
      = encodingFiber (I := Fin 2) (0 : Fin 2) := tagFrame_one (0 : Fin 2)
  have hnorm3 : (∑ j : Fin 2, ‖(if j = 0 then 1 else Complex.I)‖
      * (if j = 0 then 1 else 2)) = 3 := by
    rw [Fin.sum_univ_two]
    norm_num [Complex.norm_I]
  have herr : (∑ j : Fin 2, ‖(if j = 0 then 1 else Complex.I)‖ * δ) = 2 * δ := by
    rw [Fin.sum_univ_two]
    simp [Complex.norm_I]
    ring
  refine ⟨?_, ?_⟩
  · rw [hframe, hnorm3, herr] at hG9
    exact hG9
  · intro h
    have e := congrFun (congrFun h 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, pauliXChoice_true, pauliZChoice_true,
      relabel_pauliX_entry, relabel_pauliZ_entry] at e
    norm_num at e

/-- Compressing the identity-ancilla tensor extension of Pauli X recovers Pauli X. -/
private theorem pauliX_corner : compress (encodingFiber (0 : Fin 1))
    (TensorGate (1 : Operator 1) (pauliXChoice true)) (encodingFiber (0 : Fin 1))
    = pauliXChoice true := by
  ext i₁ i₂
  rw [compress_encodingFiber_eq]
  simp [TensorGate]

/-- Compressing the identity-ancilla tensor extension of Pauli Z recovers Pauli Z. -/
private theorem pauliZ_corner : compress (encodingFiber (0 : Fin 1))
    (TensorGate (1 : Operator 1) (pauliZChoice true)) (encodingFiber (0 : Fin 1))
    = pauliZChoice true := by
  ext i₁ i₂
  rw [compress_encodingFiber_eq]
  simp [TensorGate]

/-- The identity-ancilla tensor extension of Pauli X gives an exact block encoding with scale
one. -/
private theorem pauliX_tensor_encoding :
    BlockEncoding (pauliXChoice true)
      (TensorGate (1 : Operator 1) (pauliXChoice true))
      (encodingFiber (0 : Fin 1)) (encodingFiber (0 : Fin 1)) 1 0 := by
  exact ⟨tensorGate_unitary (Matrix.unitaryGroup (Fin 1) ℂ).one_mem (pauliXChoice_unitary true),
    encodingFiber_isIsometry (0 : Fin 1), encodingFiber_isIsometry (0 : Fin 1), by norm_num,
    le_rfl, by rw [pauliX_corner, one_smul, sub_self, norm_zero]⟩

/-- The identity-ancilla tensor extension of Pauli Z gives an exact block encoding with scale
one. -/
private theorem pauliZ_tensor_encoding :
    BlockEncoding (pauliZChoice true)
      (TensorGate (1 : Operator 1) (pauliZChoice true))
      (encodingFiber (0 : Fin 1)) (encodingFiber (0 : Fin 1)) 1 0 := by
  exact ⟨tensorGate_unitary (Matrix.unitaryGroup (Fin 1) ℂ).one_mem (pauliZChoice_unitary true),
    encodingFiber_isIsometry (0 : Fin 1), encodingFiber_isIsometry (0 : Fin 1), by norm_num,
    le_rfl, by rw [pauliZ_corner, one_smul, sub_self, norm_zero]⟩

set_option maxHeartbeats 1000000 in

/-- The independent Pauli product circuit block-encodes the scaled noisy product with the stated
quadratic error, zero queries, and two gates. -/
theorem encoding_product_noisy_pauli_consumer : ∀ (δ : ℝ), 0 ≤ δ →
    let U : Matrix (Fin 1 × Fin 2) (Fin 1 × Fin 2) ℂ :=
        TensorGate (1:Operator 1) (pauliXChoice true)
    let V : Matrix (Fin 1 × Fin 2) (Fin 1 × Fin 2) ℂ :=
        TensorGate (1:Operator 1) (pauliZChoice true)
    BlockEncoding (((1+δ)^2:ℂ) • (pauliXChoice true * pauliZChoice true))
      (independentLiftLeft U * independentLiftRight V)
      (jointEncodingFiber (0:Fin 1) (0:Fin 1)) (jointEncodingFiber (0:Fin 1) (0:Fin 1))
      1 (2*δ+δ^2) ∧
    QueryCount (encodingProductCircuit U V)=0 ∧ GateCount (encodingProductCircuit U V)=2 := by
  intro δ hδ
  have hexact := independent_ancilla_blockEncoding_product (J := Fin 1) (K := Fin 1)
    (I := Fin 2) (0 : Fin 1) (0 : Fin 1) (pauliXChoice true) (pauliZChoice true)
    (TensorGate (1 : Operator 1) (pauliXChoice true))
    (TensorGate (1 : Operator 1) (pauliZChoice true)) 1 1 0 0
    pauliX_tensor_encoding pauliZ_tensor_encoding
  have hscalar : (((1+(δ:ℂ))^2) • (pauliXChoice true * pauliZChoice true))
      - (pauliXChoice true * pauliZChoice true) = ((2*δ+δ^2 : ℝ) : ℂ)
      • (pauliXChoice true * pauliZChoice true) := by
    have hcoef : ((1 + (δ : ℂ))^2) = 1 + ((2*δ+δ^2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcoef, add_smul, one_smul, add_sub_cancel_left]
  have hnn : 0 ≤ 2*δ+δ^2 := by nlinarith [hδ]
  have hnorm : ‖((2*δ+δ^2 : ℝ) : ℂ) • (pauliXChoice true * pauliZChoice true)‖
      ≤ 2*δ+δ^2 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
    calc (2*δ+δ^2) * ‖pauliXChoice true * pauliZChoice true‖
        ≤ (2*δ+δ^2) * (‖pauliXChoice true‖ * ‖pauliZChoice true‖) :=
          mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mul _ _) hnn
      _ ≤ (2*δ+δ^2) * (1 * 1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (l2_norm_unitary_le_one (pauliXChoice_unitary true))
              (l2_norm_unitary_le_one (pauliZChoice_unitary true)) (norm_nonneg _)
              zero_le_one) hnn
      _ = 2*δ+δ^2 := by rw [mul_one, mul_one]
  have hjoint : compress (jointEncodingFiber (0 : Fin 1) (0 : Fin 1))
      (independentLiftLeft (TensorGate (1 : Operator 1) (pauliXChoice true))
        * independentLiftRight (TensorGate (1 : Operator 1) (pauliZChoice true)))
      (jointEncodingFiber (0 : Fin 1) (0 : Fin 1))
      = pauliXChoice true * pauliZChoice true := by
    rw [(independent_ancilla_lift_laws (J := Fin 1) (K := Fin 1) (I := Fin 2)
      (0 : Fin 1) (0 : Fin 1) (TensorGate (1 : Operator 1) (pauliXChoice true))
      (TensorGate (1 : Operator 1) (pauliZChoice true))).2.2.2.2, pauliX_corner, pauliZ_corner]
  have hfinal : BlockEncoding (((1+(δ:ℂ))^2) • (pauliXChoice true * pauliZChoice true))
      (independentLiftLeft (TensorGate (1 : Operator 1) (pauliXChoice true))
        * independentLiftRight (TensorGate (1 : Operator 1) (pauliZChoice true)))
      (jointEncodingFiber (0 : Fin 1) (0 : Fin 1)) (jointEncodingFiber (0 : Fin 1) (0 : Fin 1))
      1 (2*δ+δ^2) := by
    refine ⟨hexact.unitary, hexact.left_isometry, hexact.right_isometry, by norm_num, hnn, ?_⟩
    rw [hjoint, one_smul, hscalar]
    exact hnorm
  have hrun := encoding_product_run_cost (J := Fin 1) (K := Fin 1) (I := Fin 2)
    (TensorGate (1 : Operator 1) (pauliXChoice true))
    (TensorGate (1 : Operator 1) (pauliZChoice true)) (fun _ => 0)
  exact ⟨hfinal, hrun.2.1, hrun.2.2.1⟩

end Qatlib.Concepts.OperatorAccess.EncodedAccess
