/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BeyondCircuit08.MainResults.Model.Basic

set_option autoImplicit false
noncomputable section

open scoped Matrix Matrix.Norms.L2Operator BigOperators
open Complex

namespace Qatlib.Papers.BeyondCircuit08.MainResults.LocalGates

open Qatlib.Papers.BeyondCircuit08.MainResults.Model

def Mn5 : Matrix (Fin 5) (Fin 5) ℂ :=
  !![fibb, 0, 0, 0, 0;
     0, fiba, 0, 0, 0;
     0, 0, fiba, 0, 0;
     0, 0, 0, fibe, fibd;
     0, 0, 0, fibd, fibc]

def Mdiag5 (α : ℝ) : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.diagonal fun i =>
    if i = 4 then Complex.exp (((-(α / 2) : ℝ) : ℂ) * Complex.I)
    else Complex.exp (((α / 2 : ℝ) : ℂ) * Complex.I)

inductive Gate5
  | diag (α : ℝ)
  | sigma

def gateMatrix : Gate5 → Matrix (Fin 5) (Fin 5) ℂ
  | .diag α => Mdiag5 α
  | .sigma => Mn5

def evalGate : List Gate5 → Matrix (Fin 5) (Fin 5) ℂ
  | [] => 1
  | g :: w => gateMatrix g * evalGate w

def lemma3Block (φ₁ φ₂ : ℂ) (V : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j =>
    if hi : i.1 < 3 then
      if hj : j.1 < 3 then
        if i = j then (if i.1 = 0 then φ₁ else φ₂) else 0
      else 0
    else
      if hj : 3 ≤ j.1 then
        V ⟨i.1 - 3, by omega⟩ ⟨j.1 - 3, by omega⟩
      else 0

theorem Mdiag5_mem_unitaryGroup (α : ℝ) :
    Mdiag5 α ∈ Matrix.unitaryGroup (Fin 5) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  simp only [Mdiag5, Matrix.diagonal, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, Matrix.one_apply]
  by_cases hi : i = 4 <;> by_cases hij : i = j <;>
    simp_all [Complex.mul_conj, Complex.normSq, Complex.exp_re, Complex.exp_im,
      Complex.cos_sq_add_sin_sq, ← pow_two, Real.exp_zero, eq_comm]

def lemma3_local_gate_decomposition_statement : Prop :=
  ∃ C : ℕ, ∀ V : Matrix (Fin 2) (Fin 2) ℂ, IsSUOn (Fin 2) V →
    ∃ w : List Gate5, w.length ≤ C ∧
      ∃ φ₁ φ₂ : ℂ, ‖φ₁‖ = 1 ∧ ‖φ₂‖ = 1 ∧
        evalGate w = lemma3Block φ₁ φ₂ V

end Qatlib.Papers.BeyondCircuit08.MainResults.LocalGates
