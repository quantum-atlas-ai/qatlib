/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.OverlapGapGoh26.Resources.ParityGadget

@[expose] public section

/-!
# The clause-program CNOT budget

Section 4.5 of Goh and Müller (arXiv:2609.35131v1) counts six CNOTs per
Max-4-XORSAT clause. Count the concatenation of the emitted clause words
and apply the independent error model in Eq. (40).
-/

set_option autoImplicit false

open Qatlib.Papers.OverlapGapGoh26.Resources
open scoped ENNReal

namespace Qatlib.Papers.OverlapGapGoh26.Resources

/-- Concatenation adds the CNOT counts of the constituent instruction words. -/
theorem twoQCount_flatten (words : List (List ParityGadget.Gate)) :
    ParityGadget.twoQCount words.flatten = (words.map ParityGadget.twoQCount).sum := by
  induction words with
  | nil => rfl
  | cons word words ih =>
      simpa only [List.flatten_cons, List.map_cons, List.sum_cons, ParityGadget.twoQCount,
        List.map_append, List.sum_append] using congrArg
          (fun n => ParityGadget.twoQCount word + n) ih

/-- A cost layer charges six CNOTs for each clause, allowing arbitrary clause angles. -/
theorem layer_twoQCount (angles : List ℝ) :
    ParityGadget.twoQCount (angles.map ParityGadget.word).flatten = 6 * angles.length := by
  rw [twoQCount_flatten]
  induction angles with
  | nil => rfl
  | cons angle angles ih =>
      simp only [List.map_cons, List.sum_cons, ParityGadget.actual_word_twoQCount,
        List.length_cons, Nat.mul_succ] at *
      omega

/-- A program with `p` cost layers of `m` clauses costs exactly `6 * m * p` CNOTs. -/
theorem program_twoQCount {m p : ℕ} (angles : Fin p → Fin m → ℝ) :
    ParityGadget.twoQCount
      ((List.ofFn fun j => (List.ofFn (angles j)).map ParityGadget.word).map List.flatten).flatten =
        6 * m * p := by
  rw [twoQCount_flatten]
  have hcount (j : Fin p) := layer_twoQCount (List.ofFn (angles j))
  simp only [List.map_ofFn, Function.comp_def, List.length_ofFn] at hcount ⊢
  simp only [hcount, List.ofFn_const, List.sum_replicate, nsmul_eq_mul]
  exact Nat.mul_comm _ _

/-- Equation (40) is the mass of the event that all CNOTs in the clause program are fault-free. -/
theorem program_no_fault {m p : ℕ} (angles : Fin p → Fin m → ℝ) (e : ℝ) (he : e ≤ 1) :
    Faults.independentLaw e (ParityGadget.twoQCount
      ((List.ofFn fun j => (List.ofFn (angles j)).map ParityGadget.word).map List.flatten).flatten)
      {x | ∀ i, x i = false} = ENNReal.ofReal ((1 - e) ^ (6 * m * p)) := by
  rw [program_twoQCount]
  exact Faults.actual_no_fault_probability e he _

end Qatlib.Papers.OverlapGapGoh26.Resources
