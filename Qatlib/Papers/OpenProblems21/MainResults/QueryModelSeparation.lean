/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OpenProblems21.MainResults.SimonGarbage

set_option backward.isDefEq.respectTransparency false

/-!
# OpenProblems21.MainResults — Problem 11: the standard-vs-erasing separation

Source: Scott Aaronson, *Open Problems Related to Quantum Query Complexity*,
arXiv:2109.06917v1 (fixed version), §9 "Comparing Query Models", p. 6,
Problem 11.

This module turns Problem 11 into a Lean proposition. An algorithm is a finite
word of arbitrary unitary known gates and oracle queries (`Program`), the only
resource is the number of oracle queries, and success means that a final
computational-basis measurement of a designated answer register returns the
prescribed answer with probability at least `2/3`. The two oracle matrices are
the standard XOR oracle and the erasing oracle of `OracleModels`.

The resulting `Problem11 : Prop` says: there are a finite family of injective
functions and a property such that one *uniform* standard-oracle algorithm
(with few queries) succeeds on every member of the family, while no
erasing-oracle algorithm with few queries succeeds on all of them. This is a
faithful rendering of the open question; it is a `def`, not a theorem, because
the question is open in the fixed paper version. Every declaration in this
module is either a definition or a fully proved theorem.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OpenProblems21.MainResults

open Qatlib.Foundations.PureStateMath
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-! ## §1. Query programs -/

/-- A single step of a query algorithm: an arbitrary known gate, or one call
to the oracle. -/
inductive Step (I : Type*) where
  | gate (U : Matrix I I ℂ)
  | query

/-- A finite query program. -/
abbrev Program (I : Type*) := List (Step I)

/-- The matrix of one step against the oracle matrix `O`. -/
def stepMatrix {I : Type*} (O : Matrix I I ℂ) : Step I → Matrix I I ℂ
  | .gate U => U
  | .query => O

/-- Evaluation of a program: the first step is applied first, so the program
matrix is read right-to-left. -/
def evalProgram {I : Type*} [Fintype I] [DecidableEq I] (O : Matrix I I ℂ) :
    Program I → Matrix I I ℂ
  | [] => 1
  | .gate U :: W => evalProgram O W * U
  | .query :: W => evalProgram O W * O

/-- The number of oracle queries in a program. -/
def queryCount {I : Type*} : Program I → ℕ
  | [] => 0
  | .gate _ :: W => queryCount W
  | .query :: W => queryCount W + 1

/-- The empty program evaluates to the identity matrix. (arXiv:2109.06917v1, §9, p. 6). -/
@[simp] theorem evalProgram_nil {I : Type*} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) : evalProgram O ([] : Program I) = 1 := rfl

/-- Prepending a query multiplies the remaining program by the oracle. (arXiv:2109.06917v1, §9, p. 6). -/
theorem evalProgram_query {I : Type*} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) (W : Program I) :
    evalProgram O (.query :: W) = evalProgram O W * O := rfl

/-- A gate-free program of `q` queries has query count `q`. (arXiv:2109.06917v1, §9, p. 6). -/
theorem queryCount_query {I : Type*} (W : Program I) :
    queryCount (.query :: W) = queryCount W + 1 := rfl

/-- A known gate is free: it adds no query. (arXiv:2109.06917v1, §9, p. 6). -/
theorem queryCount_gate {I : Type*} (U : Matrix I I ℂ) (W : Program I) :
    queryCount (.gate U :: W) = queryCount W := rfl

/-- Admissibility of a step: known gates must be unitary, oracle queries are
always allowed. This is the standard quantum-mechanical restriction on the
free part of an algorithm (arXiv:2109.06917v1, §9, p. 6). -/
def admissibleStep {I : Type*} [Fintype I] [DecidableEq I] (_O : Matrix I I ℂ) :
    Step I → Prop
  | .gate U => U ∈ Matrix.unitaryGroup I ℂ
  | .query => True

/-- A program is admissible when every known gate in it is unitary. -/
def Admissible {I : Type*} [Fintype I] [DecidableEq I] (O : Matrix I I ℂ)
    (W : Program I) : Prop :=
  ∀ s ∈ W, admissibleStep O s

/-- The empty program is admissible. -/
theorem admissible_nil {I : Type*} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) : Admissible O ([] : Program I) := by
  intro s hs
  simp at hs

/-- An oracle query is an admissible step. (arXiv:2109.06917v1, §9, p. 6). -/
theorem admissibleStep_query {I : Type*} [Fintype I] [DecidableEq I]
    (O : Matrix I I ℂ) : admissibleStep O (.query : Step I) := trivial

/-! ## §2. Success probability of an algorithm -/

/-- Probability that a computational-basis measurement of the final state
`U |init⟩` returns `b` in the answer register. -/
def answerProb {X R : Type*} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]
    (U : Matrix (X × R) (X × R) ℂ) (init : X × R) (b : R) : ℝ :=
  MeasureProb (ApplyGate U (Ket init)) (Finset.univ.filter (fun s : X × R => s.2 = b))

/-- With zero queries an algorithm can only report the answer already written
in the initial state: the success probability is `1` when the initial answer
register already holds `b`, and `0` otherwise. (arXiv:2109.06917v1, §9, p. 6). -/
theorem answerProb_one {X R : Type*} [Fintype X] [DecidableEq X] [Fintype R]
    [DecidableEq R] (init : X × R) (b : R) :
    answerProb (1 : Matrix (X × R) (X × R) ℂ) init b =
      if init.2 = b then 1 else 0 := by
  unfold answerProb MeasureProb BornProb
  rw [applyGate_one]
  by_cases h : init.2 = b
  · rw [if_pos h]
    rw [Finset.sum_eq_single init]
    · simp
    · intro s _ hs
      have hne : s ≠ init := hs
      simp [Ket, hne]
    · intro hnot
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ init, h⟩) hnot
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro s hs
    have hs2 : s.2 = b := (Finset.mem_filter.mp hs).2
    have hne : s ≠ init := fun he => h (he ▸ hs2)
    simp [Ket, hne]

/-- An algorithm with at most `q` oracle queries, all of whose non-query gates
are unitary, that solves the answer `b` from the initial state `init` with
probability at least `2/3`. -/
def learnsWithin {X R : Type*} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]
    (O : Matrix (X × R) (X × R) ℂ) (q : ℕ) (init : X × R) (b : R) : Prop :=
  ∃ W : Program (X × R), queryCount W ≤ q ∧ Admissible O W ∧
    answerProb (evalProgram O W) init b ≥ (2 / 3 : ℝ)

/-- No algorithm with at most `q` queries solves the answer `b` to the stated
confidence from the initial state `init`. -/
def failsWithin {X R : Type*} [Fintype X] [DecidableEq X] [Fintype R] [DecidableEq R]
    (O : Matrix (X × R) (X × R) ℂ) (q : ℕ) (init : X × R) (b : R) : Prop :=
  ¬ learnsWithin O q init b

/-! ## §3. The two oracle matrices in the presence of an answer register -/

/-- The standard oracle on the pair-valued candidate, with a passive answer
register. -/
def stdAnswerUpdate {N k g r : ℕ} (f : Fin N → Reg k × Reg g)
    (s : (Fin N × (Reg k × Reg g)) × Reg r) : (Fin N × (Reg k × Reg g)) × Reg r :=
  ((s.1.1, pairXor s.1.2 (f s.1.1)), s.2)

/-- The standard query is an involution even with a passive answer register. (arXiv:2109.06917v1, §9, p. 6). -/
theorem stdAnswerUpdate_involutive {N k g r : ℕ} (f : Fin N → Reg k × Reg g) :
    Function.Involutive (stdAnswerUpdate (r := r) f) := by
  intro s
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · apply Prod.ext <;> funext j <;>
        simp [stdAnswerUpdate, pairXor]
  · rfl

/-- The standard oracle matrix on the answer-carrying state space. -/
def standardOracleAnswer {N k g r : ℕ} (f : Fin N → Reg k × Reg g) :
    Matrix ((Fin N × (Reg k × Reg g)) × Reg r)
      ((Fin N × (Reg k × Reg g)) × Reg r) ℂ :=
  permMatrix (stdAnswerUpdate f)

/-- The standard oracle of the candidate acts by the pair XOR update. (arXiv:2109.06917v1, §9, p. 6). -/
theorem standardOracleAnswer_ket {N k g r : ℕ} (f : Fin N → Reg k × Reg g)
    (x : Fin N) (a : Reg k × Reg g) (z : Reg r) :
    ApplyGate (standardOracleAnswer f) (Ket ((x, a), z)) =
      Ket (stdAnswerUpdate (r := r) f ((x, a), z)) :=
  applyGate_permMatrix_ket (stdAnswerUpdate_involutive (r := r) f) _

/-- The standard oracle of the candidate is unitary. (arXiv:2109.06917v1, §9, p. 6). -/
theorem standardOracleAnswer_unitary {N k g r : ℕ} (f : Fin N → Reg k × Reg g) :
    standardOracleAnswer f ∈
      Matrix.unitaryGroup ((Fin N × (Reg k × Reg g)) × Reg r) ℂ :=
  permMatrix_unitary (stdAnswerUpdate_involutive (r := r) f)

/-- The **erasing oracle** for `f : Fin N → Reg k × Reg g` on the encoded
input subspace `{enc x}` and a passive answer register (arXiv:2109.06917v1,
§9, p. 6): the basis state `|enc x, z⟩` is sent to `|f(x), z⟩`, and the
previous content of the input register is erased. Off the encoded subspace
the oracle is set to zero, reflecting that the erasing oracle is only defined
on the actual inputs (and is not reversible when `f` is not injective). -/
def erasingOracleAnswer {N k g r : ℕ} (enc : Fin N ↪ Reg k × Reg g)
    (f : Fin N → Reg k × Reg g) :
    Matrix ((Reg k × Reg g) × Reg r) ((Reg k × Reg g) × Reg r) ℂ := by
  classical
  exact fun y x => if ∃ i, x.1 = enc i ∧ y = (f i, x.2) then 1 else 0

/-- On an encoded input the erasing oracle returns `|f(x)⟩` and leaves the
answer register untouched. -/
theorem erasingOracleAnswer_mulVec_ket {N k g r : ℕ} (enc : Fin N ↪ Reg k × Reg g)
    (f : Fin N → Reg k × Reg g) (i : Fin N) (z : Reg r) :
    erasingOracleAnswer enc f *ᵥ Ket (enc i, z) = Ket (f i, z) := by
  funext y
  show (∑ x' : (Reg k × Reg g) × Reg r,
      (if ∃ j : Fin N, x'.1 = enc j ∧ y = (f j, x'.2) then (1 : ℂ) else 0)
        * Ket (enc i, z) x') = Ket (f i, z) y
  rw [Finset.sum_eq_single (enc i, z)]
  · simp only [Ket, if_true, mul_one]
    by_cases h : y = (f i, z)
    · rw [if_pos h, if_pos ⟨i, rfl, h⟩]
    · rw [if_neg h, if_neg]
      rintro ⟨j, hj, hy⟩
      have hji : j = i := enc.injective hj.symm
      exact h (hji ▸ hy)
  · intro x' _ hx'
    simp [Ket, hx']
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ## §4. Problem 11 -/

/-- **Open conjecture / complexity hypothesis — not proved in Qatlib.** **Problem 11** (arXiv:2109.06917v1, §9, p. 6, open). Are there sets of
injective functions for which a quantum computer can learn a property with few
standard-oracle queries but not with few erasing-oracle queries?

The formal statement uses the paper's candidate family
`f_i(x) = ⟨h_i(x), gar_i(x)⟩` (injective for every `i`), one uniform
standard-oracle program `WS` with `qS` queries that answers `P i` on every
family member, `qS < qE`, and the failure of every erasing-oracle program with
at most `qE` queries on at least one family member.

This is the open question itself, recorded as a `Prop`; it is not proved (and
must not be), since Problem 11 asks whether it is true. -/
def Problem11 : Prop :=
  ∃ (N k g r : ℕ) (x₀ : Fin N) (enc : Fin N ↪ Reg k × Reg g)
    (ι : Type) (h : ι → Fin N → Reg k) (gar : ι → Fin N → Reg g)
    (P : ι → Reg r) (qS qE : ℕ),
    qS < qE ∧
    (∀ i, Function.Injective (garbagePair (h i) (gar i))) ∧
    (∃ WS : Program ((Fin N × (Reg k × Reg g)) × Reg r),
      queryCount WS ≤ qS ∧
      ∀ i, answerProb
        (evalProgram (standardOracleAnswer (garbagePair (h i) (gar i))) WS)
        ((x₀, (ZeroStr k, ZeroStr g)), ZeroStr r) (P i) ≥ (2 / 3 : ℝ)) ∧
    (∀ WE : Program ((Reg k × Reg g) × Reg r),
      queryCount WE ≤ qE →
      ∃ i, answerProb
        (evalProgram (erasingOracleAnswer enc (garbagePair (h i) (gar i))) WE)
        (enc x₀, ZeroStr r) (P i) < (2 / 3 : ℝ))

end Qatlib.Papers.OpenProblems21.MainResults
