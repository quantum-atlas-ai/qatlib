/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.ChannelTheory.Stinespring.ShadowEstimator
import QuantumInfo.ForMathlib.HermitianMat.Sqrt
import Mathlib.Tactic
set_option warningAsError false
set_option autoImplicit false
open Matrix Qatlib Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ChannelTheory.Stinespring
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TensorProduct

noncomputable def qubitTensor {n : ℕ} (ρ : Fin n → Operator 2) :
    Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun x y => ∏ i, (ρ i) (boolEquivFin2 (x i)) (boolEquivFin2 (y i))

theorem qubitTensor_conjTranspose {n : ℕ} (A : Fin n → Operator 2) :
    (qubitTensor A)ᴴ = qubitTensor (fun i => (A i)ᴴ) := by
  ext x y
  simp [qubitTensor, Matrix.conjTranspose_apply]

theorem qubitTensor_mul {n : ℕ} (A B : Fin n → Operator 2) :
    qubitTensor A * qubitTensor B =
      qubitTensor (fun i => A i * B i) := by
  ext x y
  simp only [Matrix.mul_apply, qubitTensor, Matrix.of_apply]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i b =>
    A i (boolEquivFin2 (x i)) (boolEquivFin2 b) *
      B i (boolEquivFin2 b) (boolEquivFin2 (y i)))]
  apply Finset.prod_congr rfl
  intro i _
  exact (Equiv.sum_comp boolEquivFin2
    (fun k => A i (boolEquivFin2 (x i)) k * B i k (boolEquivFin2 (y i))))

theorem qubitTensor_one (n : ℕ) :
    qubitTensor (fun _ : Fin n => (1 : Operator 2)) = 1 := by
  ext x y
  by_cases h : x = y
  · subst y
    simp [qubitTensor]
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    have hb : boolEquivFin2 (x i) ≠ boolEquivFin2 (y i) :=
      fun he => hi (boolEquivFin2.injective he)
    rw [Matrix.one_apply_ne h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Matrix.one_apply_ne hb

theorem qubitTensor_trace {n : ℕ} (A : Fin n → Operator 2) :
    Matrix.trace (qubitTensor A) = ∏ i, Matrix.trace (A i) := by
  change (∑ x : Reg n, ∏ i, A i (boolEquivFin2 (x i)) (boolEquivFin2 (x i))) = _
  rw [← Fintype.prod_sum (fun i b => A i (boolEquivFin2 b) (boolEquivFin2 b))]
  apply Finset.prod_congr rfl
  intro i _
  exact Equiv.sum_comp boolEquivFin2 (fun k => A i k k)

theorem qubitTensor_sum {n : ℕ} {O : Type*} [Fintype O]
    (A : Fin n → O → Operator 2) :
    (∑ o : Fin n → O, qubitTensor (fun i => A i (o i))) =
      qubitTensor (fun i => ∑ o, A i o) := by
  ext x y
  simp only [Matrix.sum_apply, qubitTensor, Matrix.of_apply]
  exact (Fintype.prod_sum
    (fun i o => A i o (boolEquivFin2 (x i)) (boolEquivFin2 (y i)))).symm

theorem qubitTensor_smul {n : ℕ} (c : Fin n → ℂ) (A : Fin n → Operator 2) :
    qubitTensor (fun i => c i • A i) = (∏ i, c i) • qubitTensor A := by
  ext x y
  simp [qubitTensor, Finset.prod_mul_distrib]

theorem qubitTensor_posSemidef {n : ℕ} (A : Fin n → Operator 2)
    (hA : ∀ i, (A i).PosSemidef) : (qubitTensor A).PosSemidef := by
  let R : Fin n → Operator 2 := fun i =>
    (HermitianMat.sqrt (⟨A i,(hA i).isHermitian⟩ : HermitianMat (Fin 2) ℂ)).mat
  have hR (i : Fin n) : (R i)ᴴ*R i=A i := by
    have hH : (R i)ᴴ=R i :=
        (HermitianMat.sqrt (⟨A i,(hA i).isHermitian⟩ : HermitianMat (Fin 2) ℂ)).H
    rw [hH]
    exact HermitianMat.sqrt_sq (HermitianMat.zero_le_iff.mpr (hA i))
  have he : (qubitTensor R)ᴴ*qubitTensor R=qubitTensor A := by
    rw [qubitTensor_conjTranspose,qubitTensor_mul]
    congr 1
    funext i
    exact hR i
  rw [← he]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem qubitTensor_density {n : ℕ} (A : Fin n → Operator 2)
    (hA : ∀ i, IsDensityOperator (A i)) :
    (qubitTensor A).PosSemidef ∧ (qubitTensor A).trace=1 := by
  constructor
  · exact qubitTensor_posSemidef A (fun i => (hA i).1)
  · rw [qubitTensor_trace]
    simp only [fun i => (hA i).2,Finset.prod_const_one]

theorem axis_adjoint (a : Fin 3) : (pauliMatrix a)ᴴ=pauliMatrix a := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliMatrix,pauliX,pauliY,pauliZ,Matrix.conjTranspose_apply]

theorem axis_square (a : Fin 3) : pauliMatrix a*pauliMatrix a=1 := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [pauliMatrix,pauliX,pauliY,pauliZ,Matrix.mul_apply,Fin.sum_univ_two]
end Qatlib.Papers.RydbergMaxCut26.QubitPhysics.TensorProduct
