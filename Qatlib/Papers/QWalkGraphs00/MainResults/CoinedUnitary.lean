/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QWalkGraphs00.MainResults.Cayley
public import Qatlib.Papers.QWalkGraphs00.MainResults.Cycle.CycleWalk
public import Qatlib.Foundations.PureStateMath.Tensor
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# Unitarity of the Cayley and cycle walk steps

The source walk applies a coin and a controlled permutation of the
vertices. The stored Cayley convention shifts by the input coin label.
The stored cycle convention shifts by the output coin label. Both
orders are unitary, and the shift intertwines the two orders.
-/

set_option autoImplicit false

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QWalkGraphs00.MainResults.Cayley
open Qatlib.Papers.QWalkGraphs00.MainResults.Cycle

namespace Qatlib.Papers.QWalkGraphs00.MainResults

variable {A ι : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
  [Fintype ι] [DecidableEq ι]

/-- The coin-controlled vertex translation of the walk. -/
def vertexShift (shift : ι → A) : Equiv.Perm (ι × A) where
  toFun p := (p.1, p.2 + shift p.1)
  invFun p := (p.1, p.2 - shift p.1)
  left_inv p := by simp
  right_inv p := by simp

/-- The matrix taking input basis coordinate `p` to `vertexShift shift p`. -/
def vertexShiftMatrix (shift : ι → A) : Matrix (ι × A) (ι × A) ℂ :=
  Equiv.Perm.permMatrix ℂ ((vertexShift shift)⁻¹)

/-- The matrix of the vertex translation is unitary. -/
theorem vertex_shift_unitary (shift : ι → A) :
    vertexShiftMatrix shift ∈ Matrix.unitaryGroup (ι × A) ℂ := by
  rw [vertexShiftMatrix, Matrix.mem_unitaryGroup_iff]
  change _ * (Equiv.Perm.permMatrix ℂ ((vertexShift shift)⁻¹))ᴴ = 1
  rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp

omit [Fintype A] [Fintype ι] in
/-- The permutation entries are obtained by selecting the predecessor row
of the identity for each output coordinate. -/
private theorem vertex_shift_submatrix (shift : ι → A) :
    vertexShiftMatrix shift = (1 : Matrix (ι × A) (ι × A) ℂ).submatrix
      (vertexShift shift).symm id := by
  ext p q
  simp [vertexShiftMatrix, Matrix.one_apply, Equiv.Perm.inv_def, eq_comm]

/-- The supplied Cayley step shifts according to the input coin and then
applies the coin matrix. -/
theorem cayley_step_eq_coin_shift (C : Matrix ι ι ℂ) (shift : ι → A) :
    cayleyStep C shift = TensorGate C (1 : Matrix A A ℂ) * vertexShiftMatrix shift := by
  rw [vertex_shift_submatrix, Matrix.mul_submatrix_one]
  ext p q
  obtain ⟨a,u⟩ := p
  obtain ⟨b,v⟩ := q
  change _ = TensorGate C (1 : Matrix A A ℂ) (a,u) (b,v + shift b)
  simp [cayleyStep, tensorGate_apply, Matrix.one_apply]

/-- A unitary coin makes the supplied Cayley operator unitary. -/
theorem cayley_step_unitary (C : Matrix ι ι ℂ) (shift : ι → A)
    (hC : C ∈ Matrix.unitaryGroup ι ℂ) :
    cayleyStep C shift ∈ Matrix.unitaryGroup (ι × A) ℂ := by
  rw [cayley_step_eq_coin_shift]
  exact mul_mem (tensorGate_unitary hC (one_mem _)) (vertex_shift_unitary shift)

/-- Translating the stored Cayley step intertwines it with the paper's
coin-then-shift step on the same state space. -/
theorem cayley_step_intertwine (C : Matrix ι ι ℂ) (shift : ι → A) :
    vertexShiftMatrix shift * cayleyStep C shift =
      (vertexShiftMatrix shift * TensorGate C (1 : Matrix A A ℂ)) * vertexShiftMatrix shift := by
  rw [cayley_step_eq_coin_shift, mul_assoc]

/-- The two-index Hadamard coin is the existing Boolean Hadamard in the
equivalent index basis. -/
theorem hadamard_coin_unitary : hadamardCoin ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have h : hadamardCoin = Hadamard.submatrix finTwoEquiv finTwoEquiv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hadamardCoin, Hadamard, finTwoEquiv]
  rw [h, Matrix.mem_unitaryGroup_iff]
  change _ * (Hadamardᴴ).submatrix finTwoEquiv finTwoEquiv = 1
  rw [Matrix.submatrix_mul_equiv,
    show Hadamard * Hadamardᴴ = 1 from Matrix.mem_unitaryGroup_iff.mp hadamard_unitary,
    Matrix.submatrix_one_equiv]

/-- The source cycle step uses the Hadamard coin, then the conditional
translation with direction chosen by the output coin. -/
theorem cycle_step_eq_shift_coin (n : ℕ) [NeZero n] :
    cycleStep n =
      vertexShiftMatrix (fun a : Fin 2 => if a = 0 then (1 : ZMod n) else -1) *
        TensorGate hadamardCoin (1 : Matrix (ZMod n) (ZMod n) ℂ) := by
  rw [vertex_shift_submatrix]
  rw [show (id : Fin 2 × ZMod n → Fin 2 × ZMod n) = Equiv.refl _ from rfl,
    Matrix.one_submatrix_mul]
  ext p q
  obtain ⟨a,u⟩ := p
  obtain ⟨b,v⟩ := q
  change _ = TensorGate hadamardCoin (1 : Matrix (ZMod n) (ZMod n) ℂ)
    (a,u - (if a = 0 then 1 else -1)) (b,v)
  simp [cycleStep, tensorGate_apply, Matrix.one_apply, sub_eq_iff_eq_add]

/-- The supplied Hadamard cycle walk implements a unitary step. -/
theorem cycle_step_unitary (n : ℕ) [NeZero n] :
    cycleStep n ∈ Matrix.unitaryGroup (Fin 2 × ZMod n) ℂ := by
  rw [cycle_step_eq_shift_coin]
  exact mul_mem (vertex_shift_unitary _)
    (tensorGate_unitary hadamard_coin_unitary (one_mem _))

end Qatlib.Papers.QWalkGraphs00.MainResults
