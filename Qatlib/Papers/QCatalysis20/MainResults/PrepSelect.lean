/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.State
import Qatlib.Concepts.BlockEncoding.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# PREP–SELECT matrices and compression

This module constructs a unitary with a prescribed normalized column and defines lifted PREP,
controlled SELECT, and the ancilla embedding frame. Its compression formulas express the
resulting block as a probability-weighted matrix sum, including normalized garbage registers.
See [VonBurgEtAl2021].

## Main statements

* `exists_prepare`: Every normalized vector on a finite register is the designated column of
  some unitary matrix.
* `compression`: Compressing a PREP–SELECT circuit yields the sum of selected matrices weighted
  by the squared absolute values of PREP's designated column.
* `garbage_compression`: If PREP's designated column has amplitudes `√(p j) * g j k` with
  normalized garbage vectors, compression yields the selected matrices weighted by `p`.

## References

* [von Burg et al., 2021][VonBurgEtAl2021]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator Kronecker
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding

namespace Qatlib.Papers.QCatalysis20.MainResults.PrepSelect

variable {J G I W : Type} [Fintype J] [Fintype G] [Fintype I] [Fintype W]
  [DecidableEq J] [DecidableEq G] [DecidableEq I] [DecidableEq W]

/-- Every normalized vector on a finite register is the designated column of some unitary
matrix. -/
theorem exists_prepare (v : W→ℂ) (zero : W) (hv : ∑w,star (v w)*v w=1) :
    ∃P : Matrix W W ℂ,P∈unitaryGroup W ℂ ∧ ∀w,P w zero=v w := by
  let C : Matrix W (Fin 1) ℂ := fun w _=>v w
  have hC : Cᴴ*C=1 := by
    ext i j
    fin_cases i
    fin_cases j
    simpa [C,Matrix.mul_apply,Matrix.conjTranspose_apply] using hv
  obtain ⟨P,hP,_,hcol⟩ := Qatlib.Foundations.MatrixGeometry.State.exists_unitary_extend_cols
    C (fun _=>zero) (fun i j _=>Subsingleton.elim i j) hC
  exact ⟨P,by simpa only [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose] using hP,
    fun w=>hcol w 0⟩

/-- Lift an ancilla matrix to the joint register by taking its Kronecker product with the system
identity. -/
def lift (P : Matrix W W ℂ) : Matrix (W×I) (W×I) ℂ := P ⊗ₖ (1 : Matrix I I ℂ)

/-- The block-diagonal matrix applying `U w` conditional on the ancilla value `w`. -/
def select (U : W→Matrix I I ℂ) : Matrix (W×I) (W×I) ℂ :=
  fun p q=>if p.1=q.1 then U p.1 p.2 q.2 else 0

/-- The embedding of the system register with the ancilla fixed to `zero`. -/
def frame (zero : W) : Matrix (W×I) I ℂ := fun p i=>if p.1=zero then (1 : Matrix I I ℂ) p.2 i else 0

/-- Embedding the system with a fixed ancilla basis value is an isometry. -/
theorem frame_isometry (zero : W) : IsIsometry (frame (I:=I) zero) := by
  ext i j
  simp [frame,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.conjTranspose_apply,Matrix.one_apply,eq_comm]

/-- Lifting a unitary ancilla matrix by the system identity preserves unitarity. -/
theorem lift_unitary {P : Matrix W W ℂ} (hP : P∈unitaryGroup W ℂ) :
    lift (I:=I) P∈unitaryGroup (W×I) ℂ :=
  Matrix.kronecker_mem_unitary hP (unitaryGroup I ℂ).one_mem

/-- The controlled SELECT matrix is unitary if each selected system matrix is unitary. -/
theorem select_unitary (U : W→Matrix I I ℂ) (hU : ∀w,U w∈unitaryGroup I ℂ) :
    select U∈unitaryGroup (W×I) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
  ext ⟨w,i⟩ ⟨v,j⟩
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,Matrix.conjTranspose_apply,select]
  by_cases hw : w=v
  · subst v
    simpa [Matrix.one_apply] using! congrFun (congrFun
      (show (U w)ᴴ*U w=1 by simpa only [Matrix.star_eq_conjTranspose] using (hU w).1) i) j
  · simp [hw,Ne.symm hw]

/-- The joint-register matrix obtained by applying lifted PREP, controlled SELECT, and the
adjoint of lifted PREP. -/
def circuit (P : Matrix W W ℂ) (U : W→Matrix I I ℂ) : Matrix (W×I) (W×I) ℂ :=
  (lift P)ᴴ*select U*lift P

/-- The PREP–SELECT circuit is unitary when PREP and every selected matrix are unitary. -/
theorem circuit_unitary {P : Matrix W W ℂ} (hP : P∈unitaryGroup W ℂ)
    (U : W→Matrix I I ℂ) (hU : ∀w,U w∈unitaryGroup I ℂ) :
    circuit P U∈unitaryGroup (W×I) ℂ :=
  (unitaryGroup (W×I) ℂ).mul_mem
    ((unitaryGroup (W×I) ℂ).mul_mem (adjoint_unitary (lift_unitary hP)) (select_unitary U hU))
    (lift_unitary hP)

/-- Compression by a fixed ancilla frame extracts the matrix entries with both ancilla indices
equal to `zero`. -/
theorem frame_compression (A : Matrix (W×I) (W×I) ℂ) (zero : W) (i j : I) :
    compress (frame zero) A (frame zero) i j=A (zero,i) (zero,j) := by
  change (∑q:W×I,(∑r:W×I,star (frame zero r i)*A r q)*frame zero q j)=_
  simp [frame,Fintype.sum_prod_type,Matrix.one_apply,apply_ite]

/-- Each PREP–SELECT matrix entry is the sum of selected-matrix entries weighted by the
corresponding conjugated and unconjugated PREP entries. -/
theorem circuit_entry (P : Matrix W W ℂ) (U : W→Matrix I I ℂ) (p q : W×I) :
    circuit P U p q=∑w,star (P w p.1)*P w q.1*U w p.2 q.2 := by
  rw [circuit,Matrix.mul_assoc]
  rcases p with ⟨w,i⟩
  rcases q with ⟨v,j⟩
  simp [Matrix.mul_apply,Fintype.sum_prod_type,Matrix.conjTranspose_apply,select,
    lift,Matrix.one_apply,mul_assoc,mul_left_comm,mul_comm,apply_ite]

/-- Compressing a PREP–SELECT circuit yields the sum of selected matrices weighted by the
squared absolute values of PREP's designated column. See [VonBurgEtAl2021]. -/
theorem compression (P : Matrix W W ℂ) (U : W→Matrix I I ℂ) (zero : W) :
    compress (frame (I:=I) zero) (circuit P U) (frame (I:=I) zero)=
      ∑w,(star (P w zero)*P w zero) • U w := by
  ext i j
  rw [frame_compression,circuit_entry]
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]

/-- The joint-register amplitude `√(p j) * g j k` formed from label weights and garbage vectors. -/
def garbageColumn (p : J→ℝ) (g : J→G→ℂ) : J×G→ℂ :=
  fun w=>(Real.sqrt (p w.1):ℂ)*g w.1 w.2

omit [Fintype J] [Fintype G] [DecidableEq J] [DecidableEq G] in

/-- For nonnegative weights, the squared absolute garbage-column entry is the weight times the
squared absolute garbage amplitude. -/
theorem garbageColumn_square (p : J→ℝ) (hp : ∀j,0≤p j) (g : J→G→ℂ) (j : J) (k : G) :
    star (garbageColumn p g (j,k))*garbageColumn p g (j,k)=
      (p j:ℂ)*(star (g j k)*g j k) := by
  have hc : (Real.sqrt (p j):ℂ)*(Real.sqrt (p j):ℂ)=(p j:ℂ) := by
    exact_mod_cast Real.mul_self_sqrt (hp j)
  change star ((Real.sqrt (p j):ℂ)*g j k)*((Real.sqrt (p j):ℂ)*g j k)=_
  rw [star_mul,show star (Real.sqrt (p j):ℂ)=(Real.sqrt (p j):ℂ) by simp]
  calc
    _=((Real.sqrt (p j):ℂ)*(Real.sqrt (p j):ℂ))*(star (g j k)*g j k) := by ring
    _=_ := by rw [hc]

omit [DecidableEq J] [DecidableEq G] in

/-- Probability weights and individually normalized garbage vectors give a normalized joint
garbage column. -/
theorem garbageColumn_normalized (p : J→ℝ) (hp : ∀j,0≤p j) (hs : ∑j,p j=1)
    (g : J→G→ℂ) (hg : ∀j,∑k,star (g j k)*g j k=1) :
    ∑w,star (garbageColumn p g w)*garbageColumn p g w=1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [garbageColumn_square p hp g,← Finset.mul_sum,hg,mul_one]
  exact_mod_cast hs

/-- If PREP's designated column has amplitudes `√(p j) * g j k` with normalized garbage vectors,
compression yields the selected matrices weighted by `p`. See [VonBurgEtAl2021]. -/
theorem garbage_compression (p : J→ℝ) (hp : ∀j,0≤p j) (g : J→G→ℂ)
    (hg : ∀j,∑k,star (g j k)*g j k=1) (P : Matrix (J×G) (J×G) ℂ) (zero : J×G)
    (hcol : ∀w,P w zero=garbageColumn p g w) (U : J→Matrix I I ℂ) :
    compress (frame (I:=I) zero) (circuit P (fun w=>U w.1)) (frame (I:=I) zero)=∑j,(p j:ℂ)•U j := by
  rw [compression,Fintype.sum_prod_type]
  simp_rw [hcol,garbageColumn_square p hp g]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_smul,← Finset.mul_sum,hg,mul_one]

end Qatlib.Papers.QCatalysis20.MainResults.PrepSelect
