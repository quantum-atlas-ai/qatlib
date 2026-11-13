/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BeyondCircuit08.MainResults.Model.Basic

/-!
# Five-dimensional local gate model

The gate type `Gate5` contains a one-parameter diagonal phase gate and the Fibonacci gate `Mn5`.
Products are evaluated by `evalGate`, and `lemma3Block` describes their intended decomposition
into three scalar coordinates and a two-dimensional block.

The proposition `lemma3_local_gate_decomposition_statement` states the bounded-length
realization of any special unitary two-dimensional block, up to the recorded scalar phases,
corresponding to Lemma 3 of [Jordan2008].

## Main statements

* `Mdiag5_mem_unitaryGroup`: each diagonal phase gate is unitary.
* `lemma3_local_gate_decomposition_statement`: the proposition specifying a uniform word-length
  bound for the local decomposition.

## References

* [Jordan, 2008][Jordan2008]
-/

set_option autoImplicit false
noncomputable section

open scoped Matrix Matrix.Norms.L2Operator BigOperators
open Complex

namespace Qatlib.Papers.BeyondCircuit08.MainResults.LocalGates

open Qatlib.Papers.BeyondCircuit08.MainResults.Model

/-- The five-dimensional Fibonacci gate with scalar entries `fibb`, `fiba`, `fiba` and final
block with rows `(fibe, fibd)` and `(fibd, fibc)`. -/
def Mn5 : Matrix (Fin 5) (Fin 5) ℂ :=
  !![fibb, 0, 0, 0, 0;
     0, fiba, 0, 0, 0;
     0, 0, fiba, 0, 0;
     0, 0, 0, fibe, fibd;
     0, 0, 0, fibd, fibc]

/-- The diagonal gate with phase `exp (i * α / 2)` on the first four coordinates and `exp (-i *
α / 2)` on the last. -/
def Mdiag5 (α : ℝ) : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.diagonal fun i =>
    if i = 4 then Complex.exp (((-(α / 2) : ℝ) : ℂ) * Complex.I)
    else Complex.exp (((α / 2 : ℝ) : ℂ) * Complex.I)

/-- The local gate symbols consisting of a real-parameter diagonal gate and a fixed Fibonacci
gate. -/
inductive Gate5
  | diag (α : ℝ)
  | sigma

/-- The five-dimensional matrix associated with a local gate symbol. -/
def gateMatrix : Gate5 → Matrix (Fin 5) (Fin 5) ℂ
  | .diag α => Mdiag5 α
  | .sigma => Mn5

/-- The ordered matrix product of a list of local gates, with the empty list evaluated as the
identity. -/
def evalGate : List Gate5 → Matrix (Fin 5) (Fin 5) ℂ
  | [] => 1
  | g :: w => gateMatrix g * evalGate w

/-- The five-dimensional block matrix with initial diagonal entries `φ₁`, `φ₂`, `φ₂` and final
two-by-two block `V`. -/
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

/-- Every real-parameter diagonal gate `Mdiag5 α` is unitary [Jordan2008]. -/
theorem Mdiag5_mem_unitaryGroup (α : ℝ) :
    Mdiag5 α ∈ Matrix.unitaryGroup (Fin 5) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  simp only [Mdiag5, Matrix.diagonal, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.of_apply, Matrix.one_apply]
  by_cases hi : i = 4 <;> by_cases hij : i = j <;>
    simp_all [Complex.mul_conj, Complex.normSq, Complex.exp_re, Complex.exp_im,
      Complex.cos_sq_add_sin_sq, ← pow_two, Real.exp_zero, eq_comm]

/-- **Statement only — not proved in Qatlib.** The proposition that every two-dimensional special unitary is the final block of a local
gate word of uniformly bounded length, with unit scalar phases on the remaining coordinates
[Jordan2008, Lemma 3][Jordan2008]. -/
def lemma3_local_gate_decomposition_statement : Prop :=
  ∃ C : ℕ, ∀ V : Matrix (Fin 2) (Fin 2) ℂ, IsSUOn (Fin 2) V →
    ∃ w : List Gate5, w.length ≤ C ∧
      ∃ φ₁ φ₂ : ℂ, ‖φ₁‖ = 1 ∧ ‖φ₂‖ = 1 ∧
        evalGate w = lemma3Block φ₁ φ₂ V

end Qatlib.Papers.BeyondCircuit08.MainResults.LocalGates
