/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BKFermion17.H2Edge.GraphAdapter
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.BKFermion17.H2Code
set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.PauliCliffordLawsProofs
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.BKFermion17.H2Edge

def vertex (i : Fin 4) : Matrix (Reg 4) (Reg 4) ℂ := op (h2B i)

def edge (i j : Fin 4) : Matrix (Reg 4) (Reg 4) ℂ := op (h2A i j)

def loopMatrix : Matrix (Reg 4) (Reg 4) ℂ := op h2Loop

theorem vertex_square (i : Fin 4) : vertex i*vertex i=1 := by
  rw [vertex,← op_mul,h2B_sq,op_one]

theorem edge_square (i j : Fin 4) (h : h2Edge i j) : edge i j*edge i j=1 := by
  rw [edge,← op_mul,h2A_sq i j h,op_one]

theorem loop_square : loopMatrix*loopMatrix=1 := by
  rw [loopMatrix,← op_mul,h2Loop_sq,op_one]

theorem loop_hermitian : loopMatrixᴴ=loopMatrix := by
  rw [loopMatrix,op_conjTranspose]
  congr 1

theorem loop_vertex_commutes (i : Fin 4) : loopMatrix*vertex i=vertex i*loopMatrix := by
  have h : PauliElem.mul h2Loop (h2B i)=PauliElem.mul (h2B i) h2Loop := by decide +revert
  rw [loopMatrix,vertex,← op_mul,← op_mul,h]

theorem loop_edge_commutes (i j : Fin 4) : loopMatrix*edge i j=edge i j*loopMatrix := by
  have h : PauliElem.mul h2Loop (h2A i j)=PauliElem.mul (h2A i j) h2Loop := by decide +revert
  rw [loopMatrix,edge,← op_mul,← op_mul,h]

def projector : Matrix (Reg 4) (Reg 4) ℂ := (2⁻¹ : ℂ) • (1+loopMatrix)

theorem loop_projector : loopMatrix*projector=projector := by
  simp only [projector,Matrix.mul_smul,mul_add,mul_one,loop_square]
  rw [add_comm loopMatrix 1]

theorem projector_square : projector*projector=projector := by
  have h : (1+loopMatrix)*(1+loopMatrix)=(2:ℂ) • (1+loopMatrix) := by
    calc (1+loopMatrix)*(1+loopMatrix)=1+loopMatrix+loopMatrix+loopMatrix*loopMatrix := by noncomm_ring
      _=(2:ℂ) • (1+loopMatrix) := by rw [loop_square];simp [two_smul];abel
  rw [projector,Matrix.smul_mul,Matrix.mul_smul,smul_smul,h,smul_smul]
  norm_num

theorem projector_hermitian : projectorᴴ=projector := by
  simp [projector,loop_hermitian]

theorem projector_fixed_iff (ψ : Reg 4→ℂ) : projector*ᵥψ=ψ ↔ loopMatrix*ᵥψ=ψ := by
  constructor
  · intro h
    calc loopMatrix*ᵥψ=loopMatrix*ᵥ(projector*ᵥψ) := by rw [h]
      _=(loopMatrix*projector)*ᵥψ := by rw [Matrix.mulVec_mulVec]
      _=ψ := by rw [loop_projector,h]
  · intro h
    rw [projector,Matrix.smul_mulVec,Matrix.add_mulVec,Matrix.one_mulVec,h,← two_smul ℂ ψ,smul_smul]
    norm_num

theorem loop_zero_entry : loopMatrix (fun _=>false) (fun _=>false)=0 := by
  rw [loopMatrix,h2Loop_eq,op_apply]
  norm_num [P1,Fin.prod_univ_succ]

theorem projector_zero_entry : projector (fun _=>false) (fun _=>false)=(2⁻¹:ℂ) := by
  simp [projector,loop_zero_entry]

theorem projector_ne_zero : projector≠0 := by
  intro h
  have hh := congrArg (fun A : Matrix (Reg 4) (Reg 4) ℂ => A (fun _=>false) (fun _=>false)) h
  change projector (fun _=>false) (fun _=>false)=0 at hh
  rw [projector_zero_entry] at hh
  norm_num at hh

theorem vertex_preserves (i : Fin 4) (ψ : Reg 4→ℂ) (h : loopMatrix*ᵥψ=ψ) :
    loopMatrix*ᵥ(vertex i*ᵥψ)=vertex i*ᵥψ := by
  rw [Matrix.mulVec_mulVec,loop_vertex_commutes,← Matrix.mulVec_mulVec,h]

theorem edge_preserves (i j : Fin 4) (ψ : Reg 4→ℂ) (h : loopMatrix*ᵥψ=ψ) :
    loopMatrix*ᵥ(edge i j*ᵥψ)=edge i j*ᵥψ := by
  rw [Matrix.mulVec_mulVec,loop_edge_commutes,← Matrix.mulVec_mulVec,h]

end
end Qatlib.Papers.BKFermion17.H2Code
