/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryModelComparisonContinuationDefs
import Mathlib.Tactic.Linarith

/-!
# Query convention implications and attained minima

This module compares the exact, bounded, success, and parameterized inconclusive predicates for
finite quantum and classical program classes. Implication between conventions gives inclusion of
feasible query counts and reverses the corresponding minimum-budget inequalities, with explicit
witnesses for attained minima. These comparisons support the query-model framework of
[BealsEtAl2001].

The module also bounds expected classical queries by the worst-case budget and proves
monotonicity and rounding properties of the Grover search parameters. Search-class minima are
attained by programs meeting the prescribed success threshold, in the amplitude-amplification
setting of [BrassardEtAl2002].

## Main statements

* `conventionMin_antitone`: Weakening a convention cannot increase the minimum feasible query
  count.
* `conventionMin_attained`: Every nonempty convention count set has a program realizing its
  minimum.
* `ClassicalProgram.expectedQueries_le`: Expected queries do not exceed the worst-case budget.
* `searchMin_attained`: A search-class minimum is realized by a program meeting the success
  threshold.

## References

* [Beals et al., 2001][BealsEtAl2001]
* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Matrix
open scoped Classical BigOperators ENNReal

variable {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]

/-- A program satisfying `ExactFor` also satisfies `BoundedFor` for the same Boolean function. -/
theorem exact_convention_bounded {P : DecisionProgram I W} {f : (I → Bool) → Bool}
    (h : P.ExactFor f) : P.BoundedFor f := by
  intro g
  rw [h g]
  by_cases hf : f g = true <;> simp [hf]

/-- A program satisfying `ExactFor` also satisfies `SuccessFor` for the same Boolean function. -/
theorem exact_convention_success {P : DecisionProgram I W} {f : (I → Bool) → Bool}
    (h : P.ExactFor f) : P.SuccessFor f := by
  intro g
  rw [h g]
  by_cases hf : f g = true
  · simp [hf]
    norm_num
  · simp [hf]

/-- A program satisfying `ExactFor` satisfies `ZeroErrorInconclusiveFor` at every nonnegative
parameter `t`. -/
theorem exact_convention_inconclusive {P : DecisionProgram I W} {f : (I → Bool) → Bool}
    {t : ℝ} (ht0 : 0 ≤ t) (h : P.ExactFor f) :
    P.ZeroErrorInconclusiveFor f t := by
  intro g
  rw [h g]
  by_cases hf : f g = true
  · simp [hf]
    linarith
  · simp [hf]
    linarith

/-- A program satisfying `BoundedFor` also satisfies `SuccessFor` for the same Boolean function. -/
theorem bounded_convention_success {P : DecisionProgram I W} {f : (I → Bool) → Bool}
    (h : P.BoundedFor f) : P.SuccessFor f := by
  intro g
  by_cases hf : f g = true
  · have h1 := h g
    rw [if_pos hf] at h1
    rw [abs_le] at h1
    rw [if_pos hf]
    linarith
  · have h1 := h g
    rw [if_neg hf] at h1
    rw [abs_le] at h1
    rw [if_neg hf]
    linarith

/-- A program satisfying `BoundedFor` satisfies `ZeroErrorInconclusiveFor` whenever its
parameter is at least `1 / 3`. -/
theorem bounded_convention_inconclusive {P : DecisionProgram I W} {f : (I → Bool) → Bool}
    {t : ℝ} (ht : 1 / 3 ≤ t) (h : P.BoundedFor f) :
    P.ZeroErrorInconclusiveFor f t := by
  intro g
  by_cases hf : f g = true
  · have h1 := h g
    rw [if_pos hf] at h1
    rw [abs_le] at h1
    rw [if_pos hf]
    linarith
  · have h1 := h g
    rw [if_neg hf] at h1
    rw [abs_le] at h1
    rw [if_neg hf]
    linarith

/-- A program satisfying `SuccessFor` satisfies `ZeroErrorInconclusiveFor` whenever its
parameter is at least `1 / 3`. -/
theorem success_convention_inconclusive {P : DecisionProgram I W} {f : (I → Bool) → Bool}
    {t : ℝ} (ht : 1 / 3 ≤ t) (h : P.SuccessFor f) :
    P.ZeroErrorInconclusiveFor f t := by
  intro g
  by_cases hf : f g = true
  · have h1 := h g
    rw [if_pos hf] at h1
    rw [if_pos hf]
    linarith
  · have h1 := h g
    rw [if_neg hf] at h1
    rw [if_neg hf]
    linarith

/-- The predicates `SuccessFor` and `ZeroErrorInconclusiveFor` with parameter `1 / 3` are
equivalent. -/
theorem success_iff_inconclusive_one_third {P : DecisionProgram I W}
    {f : (I → Bool) → Bool} :
    P.SuccessFor f ↔ P.ZeroErrorInconclusiveFor f (1 / 3) := by
  constructor
  · intro h
    exact success_convention_inconclusive (t := 1 / 3) (by norm_num) h
  · intro h
    intro g
    by_cases hf : f g = true
    · have h1 := h g
      rw [if_pos hf] at h1
      rw [if_pos hf]
      linarith
    · have h1 := h g
      rw [if_neg hf] at h1
      rw [if_neg hf]
      linarith

/-- The exact comparison convention implies the bounded comparison convention. -/
theorem conventionStronger_exact_bounded :
    ConventionStronger (I := I) (W := W) .exact .bounded := by
  intro P f h
  simp only [ConventionHolds] at h ⊢
  exact exact_convention_bounded h

/-- The exact comparison convention implies the success comparison convention. -/
theorem conventionStronger_exact_success :
    ConventionStronger (I := I) (W := W) .exact .success := by
  intro P f h
  simp only [ConventionHolds] at h ⊢
  exact exact_convention_success h

/-- The exact comparison convention implies the inconclusive comparison convention at every
nonnegative parameter. -/
theorem conventionStronger_exact_inconclusive {t : ℝ} (ht : 0 ≤ t) :
    ConventionStronger (I := I) (W := W) .exact (.zeroErrorInconclusive t) := by
  intro P f h
  simp only [ConventionHolds] at h ⊢
  exact exact_convention_inconclusive (t := t) ht h

/-- The bounded comparison convention implies the success comparison convention. -/
theorem conventionStronger_bounded_success :
    ConventionStronger (I := I) (W := W) .bounded .success := by
  intro P f h
  simp only [ConventionHolds] at h ⊢
  exact bounded_convention_success h

/-- The success comparison convention implies the inconclusive comparison convention for
parameters at least `1 / 3`. -/
theorem conventionStronger_success_inconclusive {t : ℝ} (ht : 1 / 3 ≤ t) :
    ConventionStronger (I := I) (W := W) .success (.zeroErrorInconclusive t) := by
  intro P f h
  simp only [ConventionHolds] at h ⊢
  exact success_convention_inconclusive (t := t) ht h

/-- A query count belongs to a convention's count set exactly when a program in the machine
class satisfies that convention and has that query count. -/
theorem mem_conventionCountSet {M : MachineClass I W} {c : ComparisonConvention}
    {f : (I → Bool) → Bool} {n : ℕ} :
    n ∈ ConventionCountSet M c f ↔
      ∃ P ∈ M.programs, ConventionHolds c P f ∧ QueryCount P.circuit = n := by
  unfold ConventionCountSet
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨P, hP, hn⟩
    obtain ⟨hPm, hdec⟩ := List.mem_filter.mp hP
    exact ⟨P, hPm, of_decide_eq_true hdec, hn⟩
  · rintro ⟨P, hPm, hPf, hn⟩
    exact ⟨P, List.mem_filter.mpr ⟨hPm, by rw [decide_eq_true_eq]; exact hPf⟩, hn⟩

/-- Implication from convention `c` to convention `c'` gives inclusion of the feasible query
counts for `c` in those for `c'`. -/
theorem conventionCountSet_subset {M : MachineClass I W} {c c' : ComparisonConvention}
    (hstrong : ConventionStronger (I := I) (W := W) c c') {f : (I → Bool) → Bool} :
    ConventionCountSet M c f ⊆ ConventionCountSet M c' f := by
  intro n hn
  obtain ⟨P, hP, hPf, hcnt⟩ :=
    (mem_conventionCountSet (M := M) (c := c) (f := f) (n := n)).mp hn
  exact (mem_conventionCountSet (M := M) (c := c') (f := f) (n := n)).mpr
    ⟨P, hP, hstrong P f hPf, hcnt⟩

/-- If convention `c` implies `c'` and both count sets are nonempty, the minimum query count for
`c'` is at most that for `c`. -/
theorem conventionMin_antitone {M : MachineClass I W} {c c' : ComparisonConvention}
    (hstrong : ConventionStronger (I := I) (W := W) c c') {f : (I → Bool) → Bool}
    {h : ∃ n, n ∈ ConventionCountSet M c f}
    {h' : ∃ n, n ∈ ConventionCountSet M c' f} :
    ConventionMinQueries M c' f h' ≤ ConventionMinQueries M c f h := by
  have hmem : ConventionMinQueries M c f h ∈ ConventionCountSet M c f :=
    finsetMinNat_mem (s := ConventionCountSet M c f) (h := h)
  have hmem' : ConventionMinQueries M c f h ∈ ConventionCountSet M c' f :=
    conventionCountSet_subset hstrong hmem
  exact finsetMinNat_le (s := ConventionCountSet M c' f) (h := h') hmem'

/-- The count set for the exact comparison convention equals the machine class's exact count
set. -/
theorem conventionCountSet_exact_eq (M : MachineClass I W) (f : (I → Bool) → Bool) :
    ConventionCountSet M .exact f = M.exactCountSet f := by
  ext n
  constructor
  · intro hn
    obtain ⟨P, hP, hPf, hcnt⟩ :=
      (mem_conventionCountSet (M := M) (c := .exact) (f := f) (n := n)).mp hn
    unfold MachineClass.exactCountSet
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨P, List.mem_filter.mpr ⟨hP, by rw [decide_eq_true_eq]; exact hPf⟩, hcnt⟩
  · intro hn
    unfold MachineClass.exactCountSet at hn
    rw [List.mem_toFinset, List.mem_map] at hn
    obtain ⟨P, hP, hcnt⟩ := hn
    obtain ⟨hPm, hdec⟩ := List.mem_filter.mp hP
    exact (mem_conventionCountSet (M := M) (c := .exact) (f := f) (n := n)).mpr
      ⟨P, hPm, of_decide_eq_true hdec, hcnt⟩

/-- The count set for the bounded comparison convention equals the machine class's bounded count
set. -/
theorem conventionCountSet_bounded_eq (M : MachineClass I W) (f : (I → Bool) → Bool) :
    ConventionCountSet M .bounded f = M.boundedCountSet f := by
  ext n
  constructor
  · intro hn
    obtain ⟨P, hP, hPf, hcnt⟩ :=
      (mem_conventionCountSet (M := M) (c := .bounded) (f := f) (n := n)).mp hn
    unfold MachineClass.boundedCountSet
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨P, List.mem_filter.mpr ⟨hP, by rw [decide_eq_true_eq]; exact hPf⟩, hcnt⟩
  · intro hn
    unfold MachineClass.boundedCountSet at hn
    rw [List.mem_toFinset, List.mem_map] at hn
    obtain ⟨P, hP, hcnt⟩ := hn
    obtain ⟨hPm, hdec⟩ := List.mem_filter.mp hP
    exact (mem_conventionCountSet (M := M) (c := .bounded) (f := f) (n := n)).mpr
      ⟨P, hPm, of_decide_eq_true hdec, hcnt⟩

/-- The count set for the success comparison convention equals the machine class's success count
set. -/
theorem conventionCountSet_success_eq (M : MachineClass I W) (f : (I → Bool) → Bool) :
    ConventionCountSet M .success f = M.successCountSet f := by
  ext n
  constructor
  · intro hn
    obtain ⟨P, hP, hPf, hcnt⟩ :=
      (mem_conventionCountSet (M := M) (c := .success) (f := f) (n := n)).mp hn
    unfold MachineClass.successCountSet
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨P, List.mem_filter.mpr ⟨hP, by rw [decide_eq_true_eq]; exact hPf⟩, hcnt⟩
  · intro hn
    unfold MachineClass.successCountSet at hn
    rw [List.mem_toFinset, List.mem_map] at hn
    obtain ⟨P, hP, hcnt⟩ := hn
    obtain ⟨hPm, hdec⟩ := List.mem_filter.mp hP
    exact (mem_conventionCountSet (M := M) (c := .success) (f := f) (n := n)).mpr
      ⟨P, hPm, of_decide_eq_true hdec, hcnt⟩

/-- The convention minimum is at most the query count of any program in the class satisfying
that convention. -/
theorem conventionMin_le_of_program {M : MachineClass I W} {c : ComparisonConvention}
    {f : (I → Bool) → Bool} {h : ∃ n, n ∈ ConventionCountSet M c f}
    {P : DecisionProgram I W} (hP : P ∈ M.programs) (hPf : ConventionHolds c P f) :
    ConventionMinQueries M c f h ≤ QueryCount P.circuit := by
  have hmem : QueryCount P.circuit ∈ ConventionCountSet M c f :=
    (mem_conventionCountSet (M := M) (c := c) (f := f) (n := QueryCount P.circuit)).mpr
      ⟨P, hP, hPf, rfl⟩
  exact finsetMinNat_le hmem

/-- A nonempty convention count set has a program in the class satisfying the convention whose
query count equals the minimum. -/
theorem conventionMin_attained {M : MachineClass I W} {c : ComparisonConvention}
    {f : (I → Bool) → Bool} {h : ∃ n, n ∈ ConventionCountSet M c f} :
    ∃ P ∈ M.programs, ConventionHolds c P f ∧
      QueryCount P.circuit = ConventionMinQueries M c f h := by
  have hmem : ConventionMinQueries M c f h ∈ ConventionCountSet M c f :=
    finsetMinNat_mem (s := ConventionCountSet M c f) (h := h)
  obtain ⟨P, hP, hPf, hcnt⟩ :=
    (mem_conventionCountSet (M := M) (c := c) (f := f)
      (n := ConventionMinQueries M c f h)).mp hmem
  exact ⟨P, hP, hPf, hcnt⟩

/-- When the three feasible count sets are nonempty, the success minimum is at most the bounded
minimum, which is at most the exact minimum. -/
theorem conventionMin_chain {M : MachineClass I W} {f : (I → Bool) → Bool}
    {hE : ∃ n, n ∈ ConventionCountSet M .exact f}
    {hB : ∃ n, n ∈ ConventionCountSet M .bounded f}
    {hS : ∃ n, n ∈ ConventionCountSet M .success f} :
    ConventionMinQueries M .success f hS ≤ ConventionMinQueries M .bounded f hB ∧
      ConventionMinQueries M .bounded f hB ≤ ConventionMinQueries M .exact f hE := by
  refine ⟨?_, ?_⟩
  · exact conventionMin_antitone (c := .bounded) (c' := .success)
      conventionStronger_bounded_success (f := f) (h := hB) (h' := hS)
  · exact conventionMin_antitone (c := .exact) (c' := .bounded)
      conventionStronger_exact_bounded (f := f) (h := hE) (h' := hB)

/-- The minimum for the exact comparison convention equals the machine class's minimum exact
query count. -/
theorem conventionMin_exact_eq (M : MachineClass I W) (f : (I → Bool) → Bool)
    (h : ∃ n, n ∈ ConventionCountSet M .exact f) :
    ConventionMinQueries M .exact f h
      = M.minExactQueries f (by rw [← conventionCountSet_exact_eq M f]; exact h) := by
  have h' : ∃ n, n ∈ M.exactCountSet f := by
    rw [← conventionCountSet_exact_eq M f]
    exact h
  have hmemA : ConventionMinQueries M .exact f h ∈ ConventionCountSet M .exact f :=
    finsetMinNat_mem (s := ConventionCountSet M .exact f) (h := h)
  have hmemB : ConventionMinQueries M .exact f h ∈ M.exactCountSet f := by
    rw [conventionCountSet_exact_eq M f] at hmemA
    exact hmemA
  have h1 : M.minExactQueries f h' ≤ ConventionMinQueries M .exact f h :=
    finsetMinNat_le (s := M.exactCountSet f) (h := h') hmemB
  have hmemC : M.minExactQueries f h' ∈ M.exactCountSet f :=
    finsetMinNat_mem (s := M.exactCountSet f) (h := h')
  have hmemC' : M.minExactQueries f h' ∈ ConventionCountSet M .exact f := by
    rw [← conventionCountSet_exact_eq M f] at hmemC
    exact hmemC
  have h2 : ConventionMinQueries M .exact f h ≤ M.minExactQueries f h' :=
    finsetMinNat_le (s := ConventionCountSet M .exact f) (h := h) hmemC'
  exact le_antisymm h1 h2

/-- A classical program with correct-output probability one satisfies
`ComputesZeroErrorInconclusive` at every extended nonnegative parameter. -/
theorem classical_zeroError_inconclusive {prog : ClassicalProgram I Bool}
    {f : (I → Bool) → Bool} {t : ℝ≥0∞} (h : prog.ComputesZeroError f) :
    prog.ComputesZeroErrorInconclusive f t := by
  intro g
  have h1 := h g
  rw [h1]
  exact tsub_le_self

/-- A classical program with correct-output probability one meets every success threshold at
most one. -/
theorem classical_zeroError_success {prog : ClassicalProgram I Bool}
    {f : (I → Bool) → Bool} {s : ℝ≥0∞} (hs : s ≤ 1) (h : prog.ComputesZeroError f) :
    prog.ComputesWithSuccess f s := by
  intro g
  have h1 := h g
  rw [h1]
  exact hs

/-- A classical program satisfying `ComputesZeroErrorInconclusive` with parameter `t` meets
every success threshold at most `1 - t`. -/
theorem classical_inconclusive_success {prog : ClassicalProgram I Bool}
    {f : (I → Bool) → Bool} {t s : ℝ≥0∞} (hs : s ≤ 1 - t)
    (h : prog.ComputesZeroErrorInconclusive f t) :
    prog.ComputesWithSuccess f s := by
  intro g
  have h1 := h g
  exact hs.trans h1

/-- The classical zero-error convention implies the parameterized inconclusive convention for
every extended nonnegative parameter. -/
theorem classicalConventionStronger_zeroError_inconclusive (t : ℝ≥0∞) :
    ClassicalConventionStronger (I := I) .zeroError (.zeroErrorInconclusive t) := by
  intro prog f h
  simp only [ClassicalConventionHolds] at h ⊢
  exact classical_zeroError_inconclusive (t := t) h

/-- The classical zero-error convention implies the success convention at every threshold at
most one. -/
theorem classicalConventionStronger_zeroError_success {s : ℝ≥0∞} (hs : s ≤ 1) :
    ClassicalConventionStronger (I := I) .zeroError (.success s) := by
  intro prog f h
  simp only [ClassicalConventionHolds] at h ⊢
  exact classical_zeroError_success (s := s) hs h

/-- A natural number belongs to a randomized machine class's budget set exactly when a program
satisfying the specified predicate has that worst-case query count. -/
theorem mem_budgetSet {M : RandomizedMachineClass I} {P : ClassicalProgram I Bool → Prop}
    {n : ℕ} :
    n ∈ M.budgetSet P ↔
      ∃ prog ∈ M.programs, P prog ∧ ClassicalProgram.worstQueries prog = n := by
  unfold RandomizedMachineClass.budgetSet
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨prog, hprog, hn⟩
    obtain ⟨hPm, hdec⟩ := List.mem_filter.mp hprog
    exact ⟨prog, hPm, of_decide_eq_true hdec, hn⟩
  · rintro ⟨prog, hPm, hP, hn⟩
    exact ⟨prog, List.mem_filter.mpr ⟨hPm, by simp [hP]⟩, hn⟩

/-- Implication between classical conventions makes the weaker convention's minimum worst-case
budget no larger, provided both feasible budget sets are nonempty. -/
theorem classicalMinBudget_antitone {M : RandomizedMachineClass I} {c c' : ClassicalConvention}
    (hstrong : ClassicalConventionStronger (I := I) c c') {f : (I → Bool) → Bool}
    {h : ∃ n, n ∈ M.budgetSet (fun prog => ClassicalConventionHolds c prog f)}
    {h' : ∃ n, n ∈ M.budgetSet (fun prog => ClassicalConventionHolds c' prog f)} :
    M.minBudget (fun prog => ClassicalConventionHolds c' prog f) h'
      ≤ M.minBudget (fun prog => ClassicalConventionHolds c prog f) h := by
  have hmem : M.minBudget (fun prog => ClassicalConventionHolds c prog f) h
      ∈ M.budgetSet (fun prog => ClassicalConventionHolds c prog f) :=
    finsetMinNat_mem (s := M.budgetSet (fun prog => ClassicalConventionHolds c prog f))
      (h := h)
  obtain ⟨prog, hPm, hP, hcnt⟩ :=
    (mem_budgetSet (M := M) (P := fun prog => ClassicalConventionHolds c prog f)
      (n := M.minBudget (fun prog => ClassicalConventionHolds c prog f) h)).mp hmem
  have hmem' : M.minBudget (fun prog => ClassicalConventionHolds c prog f) h
      ∈ M.budgetSet (fun prog => ClassicalConventionHolds c' prog f) := by
    apply (mem_budgetSet (M := M)
      (P := fun prog => ClassicalConventionHolds c' prog f)
      (n := M.minBudget (fun prog => ClassicalConventionHolds c prog f) h)).mpr
    exact ⟨prog, hPm, hstrong prog f hP, hcnt⟩
  exact finsetMinNat_le (s := M.budgetSet (fun prog => ClassicalConventionHolds c' prog f))
    (h := h') hmem'

/-- A nonempty classical convention budget set has a program realizing its minimum worst-case
query count. -/
theorem classicalMinBudget_attained {M : RandomizedMachineClass I}
    {c : ClassicalConvention} {f : (I → Bool) → Bool}
    {h : ∃ n, n ∈ M.budgetSet (fun prog => ClassicalConventionHolds c prog f)} :
    ∃ prog ∈ M.programs, ClassicalConventionHolds c prog f ∧
      ClassicalProgram.worstQueries prog =
        M.minBudget (fun prog => ClassicalConventionHolds c prog f) h := by
  have hmem : M.minBudget (fun prog => ClassicalConventionHolds c prog f) h
      ∈ M.budgetSet (fun prog => ClassicalConventionHolds c prog f) :=
    finsetMinNat_mem (s := M.budgetSet (fun prog => ClassicalConventionHolds c prog f))
      (h := h)
  obtain ⟨prog, hPm, hP, hcnt⟩ :=
    (mem_budgetSet (M := M) (P := fun prog => ClassicalConventionHolds c prog f)
      (n := M.minBudget (fun prog => ClassicalConventionHolds c prog f) h)).mp hmem
  exact ⟨prog, hPm, hP, hcnt⟩

/-- On every oracle input, the expected query count of a classical program is at most its
worst-case query count. -/
theorem ClassicalProgram.expectedQueries_le (prog : ClassicalProgram I Bool) (o : I → Bool) :
    BoolQueryTree.ExpectedQueries prog.law o ≤ (prog.worstQueries : ℝ≥0∞) := by
  classical
  unfold BoolQueryTree.ExpectedQueries
  have hpoint : ∀ t : BoolQueryTree I Bool,
      prog.law t * (BoolQueryTree.Run o t).2 ≤ prog.law t * (prog.worstQueries : ℝ≥0∞) := by
    intro t
    by_cases hz : prog.law t = 0
    · simp [hz]
    · have ht : t ∈ prog.support := (prog.support_eq t).mpr hz
      have hmax : BoolQueryTree.MaxQueries t ≤ prog.worstQueries := prog.worstQueries_spec t ht
      have hr : (BoolQueryTree.Run o t).2 ≤ (prog.worstQueries : ℝ) := by
        exact_mod_cast le_trans (BoolQueryTree.run_queries_le o t) hmax
      have hcast : ((BoolQueryTree.Run o t).2 : ℝ≥0∞) ≤ (prog.worstQueries : ℝ≥0∞) := by
        exact_mod_cast le_trans (BoolQueryTree.run_queries_le o t) hmax
      exact mul_le_mul_of_nonneg_left hcast bot_le
  have hsum : (∑' t : BoolQueryTree I Bool, prog.law t * (BoolQueryTree.Run o t).2)
      ≤ ∑' t : BoolQueryTree I Bool, prog.law t * (prog.worstQueries : ℝ≥0∞) :=
    ENNReal.tsum_le_tsum hpoint
  calc
    (∑' t : BoolQueryTree I Bool, prog.law t * (BoolQueryTree.Run o t).2)
        ≤ ∑' t : BoolQueryTree I Bool, prog.law t * (prog.worstQueries : ℝ≥0∞) := hsum
    _ = (prog.worstQueries : ℝ≥0∞) * ∑' t : BoolQueryTree I Bool, prog.law t := by
        rw [← ENNReal.tsum_mul_left (a := (prog.worstQueries : ℝ≥0∞))
            (f := fun t => prog.law t)]
        exact tsum_congr fun t => mul_comm _ _
    _ = (prog.worstQueries : ℝ≥0∞) := by
        rw [PMF.tsum_coe]
        simp

/-- The marked count of a search instance's Boolean membership oracle equals the instance's
number of solutions. -/
theorem markedCount_instance {N : ℕ} (inst : SearchInstance N) :
    markedCount (fun i => decide (i ∈ inst.marked)) = inst.solutions := by
  have hfilter : Finset.univ.filter (fun i => decide (i ∈ inst.marked) = true)
      = inst.marked := by
    ext i
    simp
  unfold markedCount
  rw [hfilter]
  exact inst.card_marked

/-- For a fixed search-space size and positive valid marked counts, increasing the marked count
cannot decrease the Grover angle. -/
theorem groverAngle_mono {N M₁ M₂ : ℕ} (hM₁ : 0 < M₁) (hN₁ : M₁ ≤ N)
    (hM₂ : 0 < M₂) (hN₂ : M₂ ≤ N) (h : M₁ ≤ M₂) :
    groverAngle N M₁ hM₁ hN₁ ≤ groverAngle N M₂ hM₂ hN₂ := by
  unfold groverAngle
  apply Real.arcsin_le_arcsin
  apply Real.sqrt_le_sqrt
  have hN0 : 0 < N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  apply div_le_div_of_nonneg_right
  · exact_mod_cast h
  · exact hNpos.le

/-- For a fixed search-space size and positive valid marked counts, increasing the marked count
cannot increase the selected Grover iteration count. -/
theorem groverIterations_anti_mono {N M₁ M₂ : ℕ} (hM₁ : 0 < M₁) (hN₁ : M₁ ≤ N)
    (hM₂ : 0 < M₂) (hN₂ : M₂ ≤ N) (h : M₁ ≤ M₂) :
    groverIterations N M₂ hM₂ hN₂ ≤ groverIterations N M₁ hM₁ hN₁ := by
  have hθ := groverAngle_mono hM₁ hN₁ hM₂ hN₂ h
  have hθ₁ : 0 < groverAngle N M₁ hM₁ hN₁ := groverAngle_pos hM₁ hN₁
  have hθ₂ : 0 < groverAngle N M₂ hM₂ hN₂ := groverAngle_pos hM₂ hN₂
  have h4 : 4 * groverAngle N M₁ hM₁ hN₁ ≤ 4 * groverAngle N M₂ hM₂ hN₂ := by linarith
  have hinv : (4 * groverAngle N M₂ hM₂ hN₂)⁻¹
      ≤ (4 * groverAngle N M₁ hM₁ hN₁)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) h4
  have hmul : Real.pi * (4 * groverAngle N M₂ hM₂ hN₂)⁻¹
      ≤ Real.pi * (4 * groverAngle N M₁ hM₁ hN₁)⁻¹ :=
    mul_le_mul_of_nonneg_left hinv Real.pi_pos.le
  have hdiv : Real.pi / (4 * groverAngle N M₂ hM₂ hN₂)
      ≤ Real.pi / (4 * groverAngle N M₁ hM₁ hN₁) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact hmul
  unfold groverIterations
  exact Nat.ceil_le_ceil (by linarith [hdiv])

/-- The selected Grover iteration count is the first natural number whose amplified angle
reaches `π / 2`. -/
theorem searchEndpoint_grover_least {N M : ℕ} (hM : 0 < M) (hN : M ≤ N) :
    (∀ k : ℕ, k < groverIterations N M hM hN →
        (2 * k + 1) * groverAngle N M hM hN < Real.pi / 2) ∧
      (2 * groverIterations N M hM hN + 1) * groverAngle N M hM hN ≥ Real.pi / 2 :=
  groverIterations_least hM hN

/-- The selected Grover iteration count lies between the natural floor and ceiling of `π / (4 *
θ)`. -/
theorem searchEndpoint_grover_floor {N M : ℕ} (hM : 0 < M) (hN : M ≤ N) :
    Nat.floor (Real.pi / (4 * groverAngle N M hM hN)) ≤ groverIterations N M hM hN ∧
      groverIterations N M hM hN ≤ Nat.ceil (Real.pi / (4 * groverAngle N M hM hN)) :=
  groverIterations_floor_bounds hM hN

/-- The minimum search query count is at most the query count of any program in the search class
meeting the instance's success threshold. -/
theorem searchMin_le_of_program {N : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    {C : SearchClass N W} {inst : SearchInstance N} {threshold : ℝ}
    {h : ∃ k, k ∈ C.realizedCountSet inst threshold}
    {P : SearchProgram N W} (hP : P ∈ C.programs)
    (hPf : threshold ≤ P.successProb (fun i => decide (i ∈ inst.marked)) inst.marked) :
    C.minSearchQueries inst threshold h ≤ QueryCount P.circuit := by
  have hmem : QueryCount P.circuit ∈ C.realizedCountSet inst threshold := by
    unfold SearchClass.realizedCountSet
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨P, List.mem_filter.mpr ⟨hP, by simp [hPf]⟩, rfl⟩
  exact finsetMinNat_le hmem

/-- A nonempty realized search count set has a program meeting the success threshold whose query
count equals the minimum. -/
theorem searchMin_attained {N : ℕ} {W : Type} [Fintype W] [DecidableEq W]
    {C : SearchClass N W} {inst : SearchInstance N} {threshold : ℝ}
    {h : ∃ k, k ∈ C.realizedCountSet inst threshold} :
    ∃ P ∈ C.programs,
      threshold ≤ P.successProb (fun i => decide (i ∈ inst.marked)) inst.marked ∧
        QueryCount P.circuit = C.minSearchQueries inst threshold h := by
  have hmem : C.minSearchQueries inst threshold h ∈ C.realizedCountSet inst threshold :=
    finsetMinNat_mem (s := C.realizedCountSet inst threshold) (h := h)
  unfold SearchClass.realizedCountSet at hmem
  rw [List.mem_toFinset, List.mem_map] at hmem
  obtain ⟨P, hP, hcnt⟩ := hmem
  obtain ⟨hPm, hdec⟩ := List.mem_filter.mp hP
  exact ⟨P, hPm, of_decide_eq_true hdec, hcnt⟩

end Qatlib.Concepts.QueryComplexity.DegreeMethod
