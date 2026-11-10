/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TensorRegisters.RegisterModel.TensorRegisters
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Concepts.TensorRegisters.RegisterModel
open scoped Kronecker Matrix.Norms.Operator

namespace Qatlib.Papers.ManyBodySim96.MainResults

theorem exp_reindex {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) (H : Matrix A A ℂ) :
    NormedSpace.exp (Matrix.reindex e e H) = Matrix.reindex e e (NormedSpace.exp H) := by
  have hf : Continuous (Matrix.reindexAlgEquiv ℂ ℂ e) := by
    change Continuous (fun M : Matrix A A ℂ => Matrix.reindex e e M)
    fun_prop
  exact (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) hf H).symm

theorem exp_tensor_right_one {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (H : Matrix A A ℂ) :
    NormedSpace.exp (H ⊗ₖ (1 : Matrix B B ℂ)) =
      NormedSpace.exp H ⊗ₖ (1 : Matrix B B ℂ) := by
  rw [Matrix.kronecker_one, Matrix.exp_blockDiagonal, Matrix.kronecker_one]
  exact congrArg Matrix.blockDiagonal (Pi.exp_def (fun _ : B => H))

theorem exp_partitionLift {S A B : Type*} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : S ≃ A × B) (H : Matrix A A ℂ) :
    NormedSpace.exp (partitionLift e H) = partitionLift e (NormedSpace.exp H) := by
  rw [partitionLift, exp_reindex, exp_tensor_right_one]
  rfl

theorem partitionLift_smul {S A B : Type*} [DecidableEq B]
    (e : S ≃ A × B) (c : ℂ) (H : Matrix A A ℂ) :
    partitionLift e (c • H) = c • partitionLift e H := by
  ext x y
  change (c • H) (e x).1 (e y).1 * (1 : Matrix B B ℂ) (e x).2 (e y).2 =
    c * (H (e x).1 (e y).1 * (1 : Matrix B B ℂ) (e x).2 (e y).2)
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

theorem evolution_partitionLift {S A B : Type*} [Fintype S] [DecidableEq S]
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : S ≃ A × B) (H : Matrix A A ℂ) (t : ℝ) :
    Qatlib.Foundations.PureStateMath.HamiltonianEvolution (partitionLift e H) t =
      partitionLift e (Qatlib.Foundations.PureStateMath.HamiltonianEvolution H t) := by
  unfold Qatlib.Foundations.PureStateMath.HamiltonianEvolution
  rw [← partitionLift_smul, exp_partitionLift]

end Qatlib.Papers.ManyBodySim96.MainResults
