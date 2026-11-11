/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.LCU
import Qatlib.Foundations.PureStateMath.Tensor
/-!
# Bilinear LCU from distinct unitary preparations

The two PREPARE oracles contribute different normalized columns. Their literal
vacuum sandwich encodes the complex bilinear coefficients required by the
repaired construction for arXiv:2511.10267v3, equations (6)--(9).
-/

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU
open Qatlib.Concepts.Execution.WorkspaceCP
open scoped BigOperators Kronecker
namespace Qatlib.Papers.ContourSim25.LcuCircuit
variable {J I : Type} [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
/-- Actual full unitary preparation supplies a normalized column, without an assumed amplitude law. -/
theorem unitary_column_normalized (P : Matrix J J ℂ)
    (hP : P ∈ Matrix.unitaryGroup J ℂ) (j₀ : J) :
    ∑ j : J, star (P j j₀)*P j j₀=1 := by
  have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp hP) j₀) j₀
  simpa only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply_eq] using h
/-- Distinct genuine preparation oracles retain the complex column product as the encoded coefficient. -/
theorem unitary_prepare_bilinear_encoding (P Q : Matrix J J ℂ)
    (hP : P ∈ Matrix.unitaryGroup J ℂ) (hQ : Q ∈ Matrix.unitaryGroup J ℂ)
    (U : J → Matrix I I ℂ) (hU : ∀ j,U j ∈ Matrix.unitaryGroup I ℂ) (j₀ : J) :
    ProjectedUnitaryEncoding
      (∑ j : J, (star (P j j₀)*Q j j₀) • U j)
      (select U) (prepareLift (fun j=>P j j₀)) (prepareLift (fun j=>Q j j₀)) := by
  exact lcu_factorized_projectedUnitaryEncoding _ _ _ U
    (unitary_column_normalized P hP j₀) (unitary_column_normalized Q hQ j₀)
    (fun _=>rfl) hU
/-- The full PREPARE matrix really maps the vacuum frame to its column frame. -/
theorem prepare_column_frame (P : Matrix J J ℂ) (j₀ : J) :
    TensorGate P (1 : Matrix I I ℂ) * prepareLift (Ket j₀) =
      prepareLift (fun j=>P j j₀) := by
  classical
  ext ⟨j,i⟩ k
  simp [Matrix.mul_apply, TensorGate, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, prepareLift, Ket, Matrix.one_apply]
/-- Vacuum compression of the literal different-PREPARE sandwich has the same complex coefficients. -/
theorem actual_bilinear_sandwich (P Q : Matrix J J ℂ) (U : J → Matrix I I ℂ) (j₀ : J) :
    compress (prepareLift (Ket j₀))
      ((TensorGate P (1 : Matrix I I ℂ))ᴴ * select U * TensorGate Q (1 : Matrix I I ℂ))
      (prepareLift (Ket j₀)) = ∑ j : J, (star (P j j₀)*Q j j₀) • U j := by
  let E : Matrix (J × I) I ℂ := prepareLift (Ket j₀)
  have he : compress E
      ((TensorGate P (1 : Matrix I I ℂ))ᴴ * select U * TensorGate Q (1 : Matrix I I ℂ)) E =
      compress (TensorGate P (1 : Matrix I I ℂ)*E) (select U)
        (TensorGate Q (1 : Matrix I I ℂ)*E) := by
    simp only [compress, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [he,prepare_column_frame,prepare_column_frame,prepare_select_compress_bilinear]
  rfl
end Qatlib.Papers.ContourSim25.LcuCircuit
