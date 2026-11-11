/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NoncommRing

set_option backward.isDefEq.respectTransparency false

/-!
# OracleWord — the paper's clean deterministic forward-call model

Fixed arXiv:2607.29382v2, Eq. (S14) (page S5) and the surrounding discussion of
"clean deterministic protocol with exactly q forward calls" (page S9).
A `q`-query clean protocol on a register `H` (which already includes every ancilla the
protocol uses — the paper absorbs fixed swaps and coherent fixed gates into the
surrounding unitaries) is a word

`C[U](x) = G_q (I ⊗ U(x)) G_{q−1} ⋯ (I ⊗ U(x)) G_0`

with `q` forward calls to `U(x)` interleaved with fixed gates `G_0, …, G_q` that do not
depend on `x`.  `Word H q` stores the fixed gates in reverse order: the constructor
`done g` records `G_0`, and each `step g rest` records `G_{i+1}` followed by `U` and the
rest of the word.  `Word.eval` is exactly the product above.

The model records only the *number* of forward calls and the resulting operator; this
is the level at which the paper's cleaner statements (S6)–(S25) live ("only the number
of forward calls is counted", page S9).  Register routing (the swap networks used to move
a register to the input port) is part of the fixed wiring `G_i`.

Main facts proved here:
* `Word.eval_kron` — tensoring every gate and the oracle with `1` tensors the whole run.
* `Word.eval_conj` — conjugating every gate/oracle by an isometry pair `(ι, ξ)` with
  `ξ ι = 1` conjugates the whole run (the split–load wiring of Lemma S5 / Prop. S7).
* `Word.eval_seq` — concatenating words closes under query-count addition.
-/

open Matrix
open scoped Kronecker BigOperators

namespace Qatlib.Papers.HamInversion26.SpinInversion.Model

set_option autoImplicit false
noncomputable section

universe u

variable {H : Type u} [Fintype H] [DecidableEq H]

/-- A clean deterministic protocol with `q` forward calls: `q+1` fixed gates with the
unknown oracle inserted between consecutive gates.  Gates are stored beginning with the
*last* gate (`G_q`) in `step`, so `step G_q (step G_{q-1} (… (done G_0)))` reads
`G_q U G_{q-1} U ⋯ U G_0`. -/
inductive Word (H : Type u) [Fintype H] [DecidableEq H] : ℕ → Type u where
  /-- The zero-query word: a single fixed gate. -/
  | done (g : Matrix H H ℂ) : Word H 0
  /-- Prepend one fixed gate and one forward call. -/
  | step {q : ℕ} (g : Matrix H H ℂ) (rest : Word H q) : Word H (q + 1)

namespace Word

/-- Evaluate a word at an oracle `U`: the product `G_q U ⋯ U G_0`. -/
def eval : {q : ℕ} → Word H q → Matrix H H ℂ → Matrix H H ℂ
  | 0, .done g, _ => g
  | _, .step g rest, U => g * U * eval rest U

/-- Evaluation of the zero-query word is its single fixed gate. -/
@[simp] theorem eval_done (g U : Matrix H H ℂ) :
    eval (Word.done (H := H) g) U = g := rfl

/-- Evaluation of a word with one more forward call prepends the fixed gate
and the oracle to the evaluation of the rest. -/
@[simp] theorem eval_step {q : ℕ} (g : Matrix H H ℂ) (rest : Word H q) (U : Matrix H H ℂ) :
    eval (Word.step g rest) U = g * U * eval rest U := rfl

/-- Prepend one fixed gate *without* inserting an oracle call. -/
def prependGate (g : Matrix H H ℂ) : {q : ℕ} → Word H q → Word H q
  | 0, .done g0 => .done (g * g0)
  | _, .step g0 rest => .step (g * g0) rest

/-- Prepending a fixed gate multiplies the evaluated word on the left by it. -/
@[simp] theorem eval_prependGate {q : ℕ} (g : Matrix H H ℂ) (W : Word H q)
    (U : Matrix H H ℂ) :
    eval (prependGate g W) U = g * eval W U := by
  induction W with
  | done g0 => simp [prependGate, eval]
  | step g0 rest ih => simp [prependGate, eval, ih, Matrix.mul_assoc]

/-- Run `W₂` after `W₁`; the query counts add and the gate at the seam merges. -/
def seq : {q₁ q₂ : ℕ} → Word H q₁ → Word H q₂ → Word H (q₁ + q₂)
  | _, 0, W, .done g => prependGate g W
  | _, _, W, .step g rest => .step g (seq W rest)

/-- Evaluation of a concatenation is the product of evaluations. -/
theorem eval_seq {q₁ q₂ : ℕ} (W₁ : Word H q₁) (W₂ : Word H q₂)
    (U : Matrix H H ℂ) :
    eval (seq W₁ W₂) U = eval W₂ U * eval W₁ U := by
  induction W₂ with
  | done g => simp [seq, eval_prependGate]
  | step g rest ih =>
    simp [seq, eval, ih, Matrix.mul_assoc]

/-- Condition `ξ ι = 1` makes `(ι, ξ)` an isometric embedding followed by its compression. -/
def IsCompression {K : Type*} [Fintype K] [DecidableEq K]
    (ι : Matrix K H ℂ) (ξ : Matrix H K ℂ) : Prop :=
  ξ * ι = 1

/-- Conjugate every gate of a word by the pair `(ι, ξ)`. -/
def conj {K : Type*} [Fintype K] [DecidableEq K]
    (ι : Matrix K H ℂ) (ξ : Matrix H K ℂ) : {q : ℕ} → Word H q → Word K q
  | 0, .done g => .done (ι * g * ξ)
  | _, .step g rest => .step (ι * g * ξ) (conj ι ξ rest)

/-- Conjugating every gate and every oracle call by `(ι, ξ)` with `ξ ι = 1` conjugates
the whole evaluated circuit. -/
theorem eval_conj {K : Type*} [Fintype K] [DecidableEq K]
    (ι : Matrix K H ℂ) (ξ : Matrix H K ℂ) (h : IsCompression ι ξ)
    (U : Matrix H H ℂ) :
    ∀ {q : ℕ} (W : Word H q), eval (conj ι ξ W) (ι * U * ξ) = ι * eval W U * ξ := by
  intro q W
  induction W with
  | done g =>
    simp [conj, eval]
  | step g rest ih =>
    simp only [conj, eval]
    rw [ih]
    calc
      (ι * g * ξ) * (ι * U * ξ) * (ι * rest.eval U * ξ)
          = ι * (g * ((ξ * ι) * (U * ((ξ * ι) * (rest.eval U * ξ))))) := by
            simp only [Matrix.mul_assoc]
      _ = ι * (g * (U * (rest.eval U * ξ))) := by rw [h]; simp
      _ = ι * (g * U * rest.eval U) * ξ := by simp only [Matrix.mul_assoc]

/-- Tensor every gate and the oracle with the identity on an auxiliary register. -/
def kronLeft (M : Type*) [Fintype M] [DecidableEq M] :
    {q : ℕ} → Word H q → Word (M × H) q
  | 0, .done g => .done ((1 : Matrix M M ℂ) ⊗ₖ g)
  | _, .step g rest => .step ((1 : Matrix M M ℂ) ⊗ₖ g) (kronLeft M rest)

/-- Tensoring gates/oracle with `1` tensors the whole run. -/
theorem eval_kron (M : Type*) [Fintype M] [DecidableEq M]
    (U : Matrix H H ℂ) :
    ∀ {q : ℕ} (W : Word H q),
      eval (kronLeft M W) ((1 : Matrix M M ℂ) ⊗ₖ U) =
        (1 : Matrix M M ℂ) ⊗ₖ eval W U := by
  intro q W
  induction W with
  | done g => simp [kronLeft, eval]
  | step g rest ih =>
    simp only [kronLeft, eval]
    rw [ih,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp [Matrix.one_mul]

end Word

/-- A clean deterministic protocol inverts `U` up to a global phase `ω`.  This is the
paper's `C[U](x) = ω(x) U(x)†` (Eq. (S65), page S12), with `U` the oracle family. -/
def CleanInverts {P : Type*} {q : ℕ} (W : Word H q)
    (U : P → Matrix H H ℂ) (ω : P → ℂ) : Prop :=
  ∀ x, Word.eval W (U x) = ω x • (U x)ᴴ

/-- Existence of a clean `q`-query exact inversion protocol for a family `U`. -/
def InvertsIn {P : Type*} (q : ℕ) (U : P → Matrix H H ℂ) : Prop :=
  ∃ (W : Word H q) (ω : P → ℂ), CleanInverts W U ω

end

end Qatlib.Papers.HamInversion26.SpinInversion.Model
