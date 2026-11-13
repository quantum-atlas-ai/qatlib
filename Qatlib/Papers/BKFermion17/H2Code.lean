/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BKFermion17.H2Edge.GraphAdapter

/-!
# The hydrogen loop code projector

This module represents the hydrogen vertex, edge, and loop Pauli elements as matrices. It
constructs the projector onto the loop’s fixed subspace, proves that this projector is nonzero
and Hermitian, and shows that the vertex and edge matrices preserve that subspace. See
[SetiaWhitfield2018].

## Main statements

* `projector_fixed_iff`: projector-fixed vectors are exactly loop-fixed vectors.
* `projector_ne_zero`: the code projector is nonzero.
* `vertex_preserves`: vertex matrices preserve the loop-fixed subspace.
* `edge_preserves`: edge matrices preserve the loop-fixed subspace.

## References

* [Setia and Whitfield, 2018][SetiaWhitfield2018]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.BKFermion17.H2Code
set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.BKFermion17.H2Edge

/-- The matrix represented by the hydrogen vertex Pauli generator at `i`. -/
def vertex (i : Fin 4) : Matrix (Reg 4) (Reg 4) ℂ := op (h2B i)

/-- The matrix represented by the hydrogen oriented edge Pauli element from `i` to `j`. -/
def edge (i j : Fin 4) : Matrix (Reg 4) (Reg 4) ℂ := op (h2A i j)

/-- The matrix represented by the hydrogen loop Pauli element. -/
def loopMatrix : Matrix (Reg 4) (Reg 4) ℂ := op h2Loop

/-- Each hydrogen vertex matrix squares to the identity. -/
theorem vertex_square (i : Fin 4) : vertex i*vertex i=1 := by
  rw [vertex,← op_mul,h2B_sq,op_one]

/-- The hydrogen edge matrix squares to the identity when its endpoints form an edge. -/
theorem edge_square (i j : Fin 4) (h : h2Edge i j) : edge i j*edge i j=1 := by
  rw [edge,← op_mul,h2A_sq i j h,op_one]

/-- The hydrogen loop matrix squares to the identity. -/
theorem loop_square : loopMatrix*loopMatrix=1 := by
  rw [loopMatrix,← op_mul,h2Loop_sq,op_one]

/-- The hydrogen loop matrix is Hermitian. -/
theorem loop_hermitian : loopMatrixᴴ=loopMatrix := by
  rw [loopMatrix,op_conjTranspose]
  congr 1

/-- The hydrogen loop matrix commutes with every vertex matrix. -/
theorem loop_vertex_commutes (i : Fin 4) : loopMatrix*vertex i=vertex i*loopMatrix := by
  have h : PauliElem.mul h2Loop (h2B i)=PauliElem.mul (h2B i) h2Loop := by decide +revert
  rw [loopMatrix,vertex,← op_mul,← op_mul,h]

/-- The hydrogen loop matrix commutes with every oriented edge matrix. -/
theorem loop_edge_commutes (i j : Fin 4) : loopMatrix*edge i j=edge i j*loopMatrix := by
  have h : PauliElem.mul h2Loop (h2A i j)=PauliElem.mul (h2A i j) h2Loop := by decide +revert
  rw [loopMatrix,edge,← op_mul,← op_mul,h]

/-- One half of `1 + loopMatrix`, defining the projector onto loop-fixed vectors. -/
def projector : Matrix (Reg 4) (Reg 4) ℂ := (2⁻¹ : ℂ) • (1+loopMatrix)

/-- Left multiplication of the projector by the loop matrix leaves the projector unchanged. -/
theorem loop_projector : loopMatrix*projector=projector := by
  simp only [projector,Matrix.mul_smul,mul_add,mul_one,loop_square]
  rw [add_comm loopMatrix 1]

/-- The hydrogen code projector is idempotent. See [Setia and Whitfield,
2018][SetiaWhitfield2018]. -/
theorem projector_square : projector*projector=projector := by
  have h : (1+loopMatrix)*(1+loopMatrix)=(2:ℂ) • (1+loopMatrix) := by
    calc (1+loopMatrix)*(1+loopMatrix)=1+loopMatrix+loopMatrix+loopMatrix*loopMatrix := by noncomm_ring
      _=(2:ℂ) • (1+loopMatrix) := by rw [loop_square];simp [two_smul];abel
  rw [projector,Matrix.smul_mul,Matrix.mul_smul,smul_smul,h,smul_smul]
  norm_num

/-- The hydrogen code projector is Hermitian. -/
theorem projector_hermitian : projectorᴴ=projector := by
  simp [projector,loop_hermitian]

/-- A vector is fixed by the hydrogen code projector if and only if it is fixed by the loop
matrix. See [Setia and Whitfield, 2018][SetiaWhitfield2018]. -/
theorem projector_fixed_iff (ψ : Reg 4→ℂ) : projector*ᵥψ=ψ ↔ loopMatrix*ᵥψ=ψ := by
  constructor
  · intro h
    calc loopMatrix*ᵥψ=loopMatrix*ᵥ(projector*ᵥψ) := by rw [h]
      _=(loopMatrix*projector)*ᵥψ := by rw [Matrix.mulVec_mulVec]
      _=ψ := by rw [loop_projector,h]
  · intro h
    rw [projector,Matrix.smul_mulVec,Matrix.add_mulVec,Matrix.one_mulVec,h,← two_smul ℂ ψ,smul_smul]
    norm_num

/-- The all-zero diagonal entry of the loop matrix is zero. -/
theorem loop_zero_entry : loopMatrix (fun _=>false) (fun _=>false)=0 := by
  rw [loopMatrix,h2Loop_eq,op_apply]
  norm_num [P1,Fin.prod_univ_succ]

/-- The all-zero diagonal entry of the code projector is one half. -/
theorem projector_zero_entry : projector (fun _=>false) (fun _=>false)=(2⁻¹:ℂ) := by
  simp [projector,loop_zero_entry]

/-- The hydrogen code projector is nonzero. See [Setia and Whitfield, 2018][SetiaWhitfield2018]. -/
theorem projector_ne_zero : projector≠0 := by
  intro h
  have hh := congrArg (fun A : Matrix (Reg 4) (Reg 4) ℂ => A (fun _=>false) (fun _=>false)) h
  change projector (fun _=>false) (fun _=>false)=0 at hh
  rw [projector_zero_entry] at hh
  norm_num at hh

/-- Every vertex matrix maps a loop-fixed vector to another loop-fixed vector. -/
theorem vertex_preserves (i : Fin 4) (ψ : Reg 4→ℂ) (h : loopMatrix*ᵥψ=ψ) :
    loopMatrix*ᵥ(vertex i*ᵥψ)=vertex i*ᵥψ := by
  rw [Matrix.mulVec_mulVec,loop_vertex_commutes,← Matrix.mulVec_mulVec,h]

/-- Every oriented edge matrix maps a loop-fixed vector to another loop-fixed vector. See [Setia
and Whitfield, 2018][SetiaWhitfield2018]. -/
theorem edge_preserves (i j : Fin 4) (ψ : Reg 4→ℂ) (h : loopMatrix*ᵥψ=ψ) :
    loopMatrix*ᵥ(edge i j*ᵥψ)=edge i j*ᵥψ := by
  rw [Matrix.mulVec_mulVec,loop_edge_commutes,← Matrix.mulVec_mulVec,h]

end
end Qatlib.Papers.BKFermion17.H2Code
