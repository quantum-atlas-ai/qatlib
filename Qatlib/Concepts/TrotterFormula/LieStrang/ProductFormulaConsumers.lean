/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.LieStrang.CommutatorProductFormula

/-!
# Consequences of finite product-formula error bounds

This module derives reference-system trace-norm error, a tolerance guarantee for segmented
Strang evolution, and exact factorization for two generators acting on distinct tensor factors.
The error estimates use the commutator bounds of [ChildsEtAl2021Trotter].

## Main statements

* `product_formula_entangled_reference_segmented`: a trace-norm bound with an arbitrary finite
  reference.
* `product_formula_strang_paid_precision`: a budgeted Strang accuracy bound and a `3 * r` word
  length.
* `product_formula_disjoint_local_tensor_consumer`: exact tensor evolution for disjoint factors.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 4096
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ReferenceError.RefTraceError

namespace Qatlib.Concepts.TrotterFormula.LieStrang
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

/-- The sum of a finite family of Hermitian operators is Hermitian. -/
private theorem pf_sum_hermitian {D m : ℕ} (H : Fin m → Operator D)
    (hH : ∀ j, (H j).IsHermitian) : (∑ j, H j).IsHermitian := by
  change (∑ j, H j)ᴴ = _
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun j _ => (hH j).eq

/-- For Hermitian family terms and positive `r`, the product-formula and exact conjugations
tensored with a reference identity differ in trace norm by at most `t² / r * pfCommutatorSum
H * Matrix.traceNorm X`; see [ChildsEtAl2021Trotter] for the simulation bound. -/
theorem product_formula_entangled_reference_segmented
    (D m r a : ℕ) (H : Fin m → Operator D) (t : ℝ)
    (X : Matrix (Fin D × Fin a) (Fin D × Fin a) ℂ) (hr : 0 < r)
    (hH : ∀ j, (H j).IsHermitian) :
    let U := TensorGate (pfFamily H t r) (1 : Operator a)
    let V := TensorGate (HamiltonianEvolution (∑ j, H j) t) (1 : Operator a)
    Matrix.traceNorm (U*X*Uᴴ-V*X*Vᴴ) ≤ t^2/r * pfCommutatorSum H * Matrix.traceNorm X := by
  have hU := (product_formula_actual_word_and_tariffs D m r H t (fun _ => 1) hH).1
  have hV := hamiltonianEvolution_unitary (pf_sum_hermitian H hH) t
  have h := finite_reference_conjugation_error (pfFamily H t r)
    (HamiltonianEvolution (∑ j, H j) t) a X hU hV
  exact h.trans ((mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (product_formula_finite_family_segmented D m r H t hr hH) (by norm_num))
      (Matrix.traceNorm_nonneg X)).trans_eq (by ring))

/-- If the nested-commutator budget is at most `eps`, `r` Strang segments have error at most
`eps` and an explicit word of length `3 * r`, using the bounds of [ChildsEtAl2021Trotter]. -/
theorem product_formula_strang_paid_precision
    (D r : ℕ) (A B : Operator D) (t eps : ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hr : 0 < r) (_heps : 0 ≤ eps)
    (hbudget : |t|^3/(r : ℝ)^2 *
      (‖pfComm B (pfComm B A)‖/12 + ‖pfComm A (pfComm A B)‖/24) ≤ eps) :
    ‖(pfStrang A B (t/r))^r - HamiltonianEvolution (A+B) t‖ ≤ eps ∧
    (List.replicate r [HamiltonianEvolution A (t/(2*r)), HamiltonianEvolution B (t/r),
      HamiltonianEvolution A (t/(2*r))]).flatten.length = 3*r := by
  have hr0 : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hS : pfStrang A B (t/r) ∈ Matrix.unitaryGroup (Fin D) ℂ :=
    (Matrix.unitaryGroup _ _).mul_mem
      ((Matrix.unitaryGroup _ _).mul_mem (hamiltonianEvolution_unitary hA _) (hamiltonianEvolution_unitary hB _))
      (hamiltonianEvolution_unitary hA _)
  have hV := hamiltonianEvolution_unitary (hA.add hB) (t/r)
  have he : (HamiltonianEvolution (A+B) (t/r))^r = HamiltonianEvolution (A+B) t := by
    rw [pf_evolution_pow]
    congr 1
    field_simp
  constructor
  · rw [← he]
    have h := pf_unitary_power_error _ _ hS hV r
    have hlocal := product_formula_strang_nested_commutator D A B (t/r) hA hB
    apply (h.trans (mul_le_mul_of_nonneg_left hlocal hr0.le)).trans
    apply le_trans ?_ hbudget
    apply le_of_eq
    rw [abs_div, abs_of_pos hr0]
    field_simp
  · simp [List.length_flatten, List.map_replicate, Nat.mul_comm]

/-- The complex algebra homomorphism tensoring an operator on the left with the right identity. -/
private noncomputable def pfTensorLeft (D E : ℕ) :
    Operator D →ₐ[ℂ] Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ where
  toFun A := TensorGate A 1
  map_one' := tensorGate_one
  map_mul' A B := by rw [tensorGate_mul, Matrix.one_mul]
  map_zero' := by ext p q; simp [TensorGate]
  map_add' A B := by ext p q; simp [TensorGate, add_mul]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, TensorGate, Matrix.smul_kronecker]
    change c • TensorGate (1 : Operator D) (1 : Operator E) = c • 1
    rw [tensorGate_one]

/-- The complex algebra homomorphism tensoring an operator on the right with the left identity. -/
private noncomputable def pfTensorRight (D E : ℕ) :
    Operator E →ₐ[ℂ] Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ where
  toFun B := TensorGate 1 B
  map_one' := tensorGate_one
  map_mul' A B := by rw [tensorGate_mul, Matrix.one_mul]
  map_zero' := by ext p q; simp [TensorGate]
  map_add' A B := by ext p q; simp [TensorGate, mul_add]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, TensorGate, Matrix.kronecker_smul]
    change c • TensorGate (1 : Operator D) (1 : Operator E) = c • 1
    rw [tensorGate_one]

/-- Hamiltonian evolution of `A` tensored with identity equals the evolution of `A` tensored
with identity. -/
private theorem pfEvolution_tensor_left (D E : ℕ) (A : Operator D) (t : ℝ) :
    HamiltonianEvolution (TensorGate A (1 : Operator E)) t =
      TensorGate (HamiltonianEvolution A t) (1 : Operator E) := by
  have h := NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) (pfTensorLeft D E)
    (pfTensorLeft D E).toLinearMap.continuous_of_finiteDimensional ((-Complex.I * (t : ℂ)) • A)
    (by simpa only [NormedSpace.expSeries_radius_eq_top] using! edist_lt_top ((-Complex.I * (t : ℂ)) • A) 0)
  rw [map_smul] at h
  exact h.symm

/-- Hamiltonian evolution of identity tensored with `B` equals identity tensored with the
evolution of `B`. -/
private theorem pfEvolution_tensor_right (D E : ℕ) (B : Operator E) (t : ℝ) :
    HamiltonianEvolution (TensorGate (1 : Operator D) B) t =
      TensorGate (1 : Operator D) (HamiltonianEvolution B t) := by
  have h := NormedSpace.map_exp_of_mem_ball (𝕂 := ℂ) (pfTensorRight D E)
    (pfTensorRight D E).toLinearMap.continuous_of_finiteDimensional ((-Complex.I * (t : ℂ)) • B)
    (by simpa only [NormedSpace.expSeries_radius_eq_top] using! edist_lt_top ((-Complex.I * (t : ℂ)) • B) 0)
  rw [map_smul] at h
  exact h.symm

/-- A natural power of a tensor product equals the tensor product of the corresponding powers. -/
private theorem pfTensor_pow (D E : ℕ) (A : Operator D) (B : Operator E) (r : ℕ) :
    (TensorGate A B)^r = TensorGate (A^r) (B^r) := by
  induction r with
  | zero => exact tensorGate_one.symm
  | succ r ih => rw [pow_succ, ih, tensorGate_mul, pow_succ, pow_succ]

/-- The two generators acting on separate tensor factors commute, and their positive-segment
product formula equals the tensor product of their full-time evolutions. -/
theorem product_formula_disjoint_local_tensor_consumer
    (D E r : ℕ) (A : Operator D) (B : Operator E) (t : ℝ)
    (_hA : A.IsHermitian) (_hB : B.IsHermitian) (hr : 0 < r) :
    let H : Fin 2 → Matrix (Fin D × Fin E) (Fin D × Fin E) ℂ :=
      fun j => if j=0 then TensorGate A (1 : Operator E) else TensorGate (1 : Operator D) B
    pfComm (H 0) (H 1) = 0 ∧
    ((List.ofFn (fun j : Fin 2 => HamiltonianEvolution (H j) (t/r))).foldl
      (fun U V => V*U) 1)^r = TensorGate (HamiltonianEvolution A t) (HamiltonianEvolution B t) := by
  dsimp
  have hr0 : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr)
  constructor
  · simp only [pfComm, tensorGate_mul, Matrix.mul_one, Matrix.one_mul, sub_self]
  · simp only [List.ofFn_succ, List.ofFn_zero, List.foldl_cons, List.foldl_nil, mul_one]
    simp only [Fin.succ_ne_zero, if_true, if_false]
    rw [pfEvolution_tensor_left, pfEvolution_tensor_right, tensorGate_mul, Matrix.one_mul, Matrix.mul_one,
      pfTensor_pow, pf_evolution_pow, pf_evolution_pow]
    congr 2 <;> field_simp

end Qatlib.Concepts.TrotterFormula.LieStrang
