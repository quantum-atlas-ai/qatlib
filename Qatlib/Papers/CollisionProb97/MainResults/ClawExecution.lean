/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.SearchReceipt
import Qatlib.Papers.CollisionProb97.MainResults.TableRecords
import Qatlib.Papers.CollisionProb97.MainResults.CollisionCounting

/-!
# Claw search against a read-only table

This module searches a function `G` for values present in a read-only table and recovers the
associated input of `F`. It proves candidate counting, output correctness, and an expected-cost
bound for the table-based claw construction associated with [BrassardHoyerTapp1998Collision].

## Main statements

* `marked_card`: candidate count for a regular `G` whose image contains the table values.
* `search_correct`: correctness from the stored-row equations for `F`.
* `search_expected`: the expected query bound in terms of the marked-set size.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Collision]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal Classical
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
namespace Qatlib.Papers.CollisionProb97.MainResults.ClawExecution
variable {S X R : Type} [Fintype S] [DecidableEq S] [Fintype X] [DecidableEq X] [Nonempty X]
    [AddCommGroup R] [Fintype R] [DecidableEq R]

omit [Fintype S] [DecidableEq S] [Nonempty X] [AddCommGroup R] [Fintype R] in

/-- Searching `G` against the values of a read-only table, with no excluded inputs, marks
exactly the claw candidates for those values. -/
theorem marked_eq (G : X → R) {k : ℕ} (L : ReadOnlyTable.Memory (X := S) (R := R) k) :
    ActualSearch.marked G ∅ (ReadOnlyTable.values L) = clawCandidates G (ReadOnlyTable.values L) := by
  ext x
  simp [ActualSearch.marked, clawCandidates]

omit [Fintype S] [DecidableEq S] [Nonempty X] [AddCommGroup R] [Fintype R] in

/-- For an `r`-to-one function `G` and table values contained in its image, the number of marked
inputs is the number of distinct table values times `r`. -/
theorem marked_card (G : X → R) (r : ℕ) (hG : RToOne G r) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k)
    (hL : ReadOnlyTable.values L ⊆ Finset.univ.image G) :
    (ActualSearch.marked G ∅ (ReadOnlyTable.values L)).card = (ReadOnlyTable.values L).card*r := by
  rw [marked_eq]
  exact clawCandidates_card G r hG (ReadOnlyTable.values L) hL

/-- The costed claw-search law that searches `G` for a stored value and recovers the
corresponding table input. -/
def search (G : X → R) {k : ℕ} (L : ReadOnlyTable.Memory (X := S) (R := R) k)
    (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3)
    (hA : 0 < (ActualSearch.marked G ∅ (ReadOnlyTable.values L)).card) :
    CostedLaw (Option (S × X)) :=
  (SearchReceipt.recordReceipt Fintype.card_pos G ∅ L l hl hl4 hA).map fun z =>
    (TableLookup.recover (TableRecords.rows L) z.1,z.2)

/-- If every table row stores the value of `F` at its input, every search output with nonzero
mass is a pair `(s,x)` satisfying `F s = G x`. -/
theorem search_correct (F : S → R) (G : X → R) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (hL : ∀ i, (L i).2 = F (L i).1)
    (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3)
    (hA : 0 < (ActualSearch.marked G ∅ (ReadOnlyTable.values L)).card)
    (out : Option (S × X)) (c : ℕ) (hm : search G L l hl hl4 hA (out,c) ≠ 0) :
    ∃ s x, out = some (s,x) ∧ F s = G x := by
  change (out,c) ∈
      ((SearchReceipt.recordReceipt Fintype.card_pos G ∅ L l hl hl4 hA).map _).support at hm
  obtain ⟨w,hw,he⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
  obtain ⟨hvalue,hmarked⟩ :=
      SearchReceipt.recordReceipt_valid Fintype.card_pos G ∅ L l hl hl4 hA w.1 w.2 hw
  have hp : w.1.2 ∈ ReadOnlyTable.values L := by
    simpa [ActualSearch.marked, hvalue] using hmarked
  obtain ⟨s,hs,_⟩ := TableRecords.recover_exists L w.1 hp
  have hc := TableRecords.recover_sound F L hL w.1 s w.1.1 hs
  exact ⟨s,w.1.1,(congrArg Prod.fst he).symm.trans hs,hc.1.trans hvalue⟩

/-- For a positive number of marked inputs and `1 < l < 4/3`, the expected claw-search cost is
at most `(1+4*SourcePhaseConstant l)*sqrt (|X|/|marked|)`. -/
theorem search_expected (G : X → R) {k : ℕ} (L : ReadOnlyTable.Memory (X := S) (R := R) k)
    (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3)
    (hA : 0 < (ActualSearch.marked G ∅ (ReadOnlyTable.values L)).card) :
    expectedCost (search G L l hl hl4 hA) ≤ ENNReal.ofReal ((1+4*SourcePhaseConstant l)*
      Real.sqrt ((Fintype.card X : ℝ)/(ActualSearch.marked G ∅ (ReadOnlyTable.values L)).card)) := by
  obtain ⟨q,hq,_,hqb⟩ := SearchReceipt.receipt_expected Fintype.card_pos G ∅ L l hl hl4 hA
  have he : expectedCost (search G L l hl hl4 hA) =
      expectedCost (SearchReceipt.recordReceipt Fintype.card_pos G ∅ L l hl hl4 hA) := by
    unfold search expectedCost
    rw [expectation_map]
  rw [he, SearchReceipt.recordReceipt_expected, hq]
  exact ENNReal.ofReal_le_ofReal hqb

end Qatlib.Papers.CollisionProb97.MainResults.ClawExecution
