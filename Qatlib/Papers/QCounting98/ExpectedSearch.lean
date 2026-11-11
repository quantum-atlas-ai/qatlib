/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.QueryLowerBound.Theorem8CorrectedTigh
import Qatlib.Concepts.SearchStopping.UnknownCount.SearchBudget
import Qatlib.Concepts.SearchStopping.UnknownCount.Theorem3SourceFamilyTigh

/-!
# Expected query bounds for search with an unknown marked count

This module specializes the unknown-count search schedule to the marked set `sourceMarked F` of
a finite Boolean function. It records the normalized terminal law, uniform output on marked
inputs, and an expected Boolean-query bound for the search procedure discussed in
[BrassardHoyerTapp1998Counting].

The choice `sourceGrowth = 6 / 5` gives the explicit coefficient `29 / 2`. The module also
states finite-budget nontermination when the marked set is empty and a query lower bound under
the stated unitary-oracle agreement and average-success hypotheses.

## Main statements

* `source_corollary1_search`: terminal probability law and expected cost for growth between 1
  and 4/3.
* `source_corollary1_search_printed`: expected cost at most `(29 / 2) * sqrt (|X| / t)` for a
  nonempty marked set.
* `source_corollary1_runs_forever`: every finite budget times out when there are no marked
  inputs.
* `source_search_lower_bound`: a lower bound on the number of unitary query steps.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QCounting98.ExpectedSearch

open Qatlib.Concepts.SearchStopping.QueryLowerBound
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib.Concepts.AmplitudeSearch.InterruptMin
open scoped BigOperators

/-- The finite set of inputs on which the Boolean function `F` is true. -/
def sourceMarked {X : Type} [Fintype X] (F : X → Bool) : Finset X :=
  Finset.univ.filter (fun x => F x = true)

/-- The search-schedule growth factor `6 / 5`. -/
def sourceGrowth : ℝ := 6 / 5

/-- The chosen growth factor lies strictly between 1 and 4/3. -/
theorem sourceGrowth_mem : 1 < sourceGrowth ∧ sourceGrowth < 4 / 3 := by
  constructor <;> unfold sourceGrowth <;> norm_num

/-- The source phase-cost constant at `sourceGrowth` equals `9 / 2`. -/
theorem sourcePhaseConstant_printed : SourcePhaseConstant sourceGrowth = 9 / 2 := by
  unfold SourcePhaseConstant sourceGrowth
  norm_num

/-- For a nonempty marked set and `1 < l < 4 / 3`, the terminal masses form a nonnegative
probability law supported on marked outputs, with uniform output distribution there. The
expected Boolean-query count exists and is at most `(1 + 3 * SourcePhaseConstant l) * sqrt
(|X| / t)`, where `t` is the marked count; see [BrassardHoyerTapp1998Counting]. -/
theorem source_corollary1_search {X : Type} [Fintype X] [DecidableEq X]
    (F : X → Bool) {l : ℝ} (hl : 1 < l) (hl4 : l < 4 / 3)
    (hpos : 0 < (sourceMarked F).card) :
    HasSum (TerminalMass (sourceMarked F) (SourceSizes (Fintype.card X) l)) 1 ∧
      (∀ y : TerminalTrace X (SourceSizes (Fintype.card X) l),
        0 ≤ TerminalMass (sourceMarked F) (SourceSizes (Fintype.card X) l) y ∧
          (TerminalOutput y ∉ sourceMarked F →
            TerminalMass (sourceMarked F) (SourceSizes (Fintype.card X) l) y = 0)) ∧
      (∀ x : X, HasSum (fun y : TerminalTrace X (SourceSizes (Fintype.card X) l) =>
          if TerminalOutput y = x then
            TerminalMass (sourceMarked F) (SourceSizes (Fintype.card X) l) y else 0)
        (if x ∈ sourceMarked F then 1 / ((sourceMarked F).card : ℝ) else 0)) ∧
      (∃ q : ℝ, HasSum (fun y : TerminalTrace X (SourceSizes (Fintype.card X) l) =>
          TerminalMass (sourceMarked F) (SourceSizes (Fintype.card X) l) y *
            (TerminalBooleanQueries (SourceSizes (Fintype.card X) l) y : ℝ)) q ∧
        0 ≤ q ∧ q ≤ (1 + 3 * SourcePhaseConstant l) *
          Real.sqrt ((Fintype.card X : ℝ) / (sourceMarked F).card)) :=
  ⟨(search_source_terminal_law_nonempty l hl hl4 (sourceMarked F) hpos).1,
    (search_source_terminal_law_nonempty l hl hl4 (sourceMarked F) hpos).2,
    search_source_terminal_output_nonempty l hl hl4 (sourceMarked F) hpos,
    search_source_terminal_boolean_cost l hl hl4 (sourceMarked F) hpos⟩

/-- For a nonempty marked set, the search schedule with growth `6 / 5` has a nonnegative
expected Boolean-query count bounded by `(29 / 2) * sqrt (|X| / t)`, where `t` is the marked
count. This gives an explicit upper bound for [Brassard et al., Corollary
1][BrassardHoyerTapp1998Counting]. -/
theorem source_corollary1_search_printed {X : Type} [Fintype X] [DecidableEq X]
    (F : X → Bool) (hpos : 0 < (sourceMarked F).card) :
    ∃ q : ℝ, HasSum (fun y : TerminalTrace X (SourceSizes (Fintype.card X) sourceGrowth) =>
        TerminalMass (sourceMarked F)
          (SourceSizes (Fintype.card X) sourceGrowth) y *
          (TerminalBooleanQueries (SourceSizes (Fintype.card X) sourceGrowth) y : ℝ)) q ∧
      0 ≤ q ∧ q ≤ 29 / 2 * Real.sqrt ((Fintype.card X : ℝ) / (sourceMarked F).card) := by
  obtain ⟨q, hq, hq0, hqb⟩ :=
    (source_corollary1_search F sourceGrowth_mem.1 sourceGrowth_mem.2 hpos).2.2.2
  refine ⟨q, hq, hq0, ?_⟩
  rw [sourcePhaseConstant_printed] at hqb
  linarith

/-- On a nonempty input type with no marked inputs and growth at least 1, every finite-budget
search law assigns mass one to timeout and zero to each returned input. This is the
empty-marked-set case of the search procedure in [BrassardHoyerTapp1998Counting]. -/
theorem source_corollary1_runs_forever {X : Type} [Fintype X] [DecidableEq X]
    (F : X → Bool) (hN : 0 < Fintype.card X) {l : ℝ} (hl : 1 ≤ l)
    (hempty : (sourceMarked F).card = 0) (stage budget : ℕ) :
    FiniteBudgetMass (sourceMarked F) (SourceSizes (Fintype.card X) l) stage budget none = 1 ∧
      (∀ x : X, FiniteBudgetMass (sourceMarked F)
        (SourceSizes (Fintype.card X) l) stage budget (some x) = 0) := by
  have hzero : sourceMarked F = ∅ := Finset.card_eq_zero.mp hempty
  have hsizes : ∀ k, 0 < SourceSizes (Fintype.card X) l k :=
    (search_source_schedule_laws (Fintype.card X) hN l hl).2.1
  rw [hzero]
  exact ⟨search_empty_budget_timeout hN _ hsizes stage budget,
    fun x => search_finite_budget_no_false_positive hN ∅ _ hsizes stage budget x (by simp)⟩

/-- For `0 < t ≤ |Y|`, the stated oracle-agreement condition and average success at least one
half imply `floor (sin (π / 8) * sqrt (|Y| / t)) ≤ r`, with the quotient taken in the
natural numbers. This supplies a query lower bound for the search comparison in
[BrassardHoyerTapp1998Counting]. -/
theorem source_search_lower_bound {C Y : Type} [Fintype C] [DecidableEq C]
    [Fintype Y] [DecidableEq Y] (t : ℕ) (ht : 0 < t) (htY : t ≤ Fintype.card Y)
    (U : ℕ → EuclideanSpace ℂ C ≃ₗᵢ[ℂ] EuclideanSpace ℂ C)
    (V : MarkedSubsets Y t → ℕ → EuclideanSpace ℂ C ≃ₗᵢ[ℂ] EuclideanSpace ℂ C)
    (f : ℕ → C → Option Y) (ψ : EuclideanSpace ℂ C) (hψ : ‖ψ‖ = 1) (r : ℕ)
    (hq : ∀ A n, n < r → ∀ c, c ∉ SubsetQuerySet (f n) A.val →
      V A n (EuclideanSpace.single c 1) = U n (EuclideanSpace.single c 1))
    (hs : (Fintype.card (MarkedSubsets Y t) : ℝ) / 2 ≤
      ∑ A : MarkedSubsets Y t,
        ‖QueryProjection (SubsetQuerySet (f r) A.val) (UnitaryEvolution (V A) ψ r)‖ ^ 2) :
    ⌊Real.sin (Real.pi / 8) * Real.sqrt (Fintype.card Y / t : ℕ)⌋ ≤ (r : ℤ) :=
  theorem8Corrected t ht htY U V f ψ hψ r hq hs

end Qatlib.Papers.QCounting98.ExpectedSearch
