/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.ReadOnlySearch
import Qatlib.Papers.CollisionProb97.MainResults.ReturningStages

/-!
# Costed receipts for verified quantum search

This module turns the normalized terminal-history masses of verified table search into
probability mass functions and costed output laws. These receipts package the search stage used
by the collision and claw algorithms in [BrassardHoyerTapp1998Collision].

The construction `receipt` retains a marked input and its actual query count; `recordReceipt`
also stores its function value while preserving the cost coordinate.

## Main statements

* `receipt_marked`: Every input supported by the search receipt belongs to the corresponding
  marked set.
* `receipt_expected`: The search receipt has a finite nonnegative real expected cost bounded by
  the explicit search coefficient times `sqrt (|X| / |marked|)`.
* `recordReceipt_valid`: Every supported record receipt contains an accurate function record
  whose input belongs to the marked set.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Collision]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal Classical
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib.Concepts.AmplitudeSearch.InterruptMin
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
namespace Qatlib.Papers.CollisionProb97.MainResults.SearchReceipt

/-- Constructs a probability mass function from nonnegative real masses whose sum is one. -/
def fromReal {α : Type} (f : α → ℝ) (hn : ∀ a, 0 ≤ f a) (hs : HasSum f 1) : PMF α :=
  ⟨fun a => ENNReal.ofReal (f a), by
    have ht : ∑' a, ENNReal.ofReal (f a) = 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg hn hs.summable, hs.tsum_eq]
      norm_num
    rw [← ht]
    exact ENNReal.summable.hasSum⟩

/-- A convergent real sum of probability masses weighted by natural costs gives the
corresponding extended nonnegative expectation under `fromReal`. -/
theorem fromReal_mean {α : Type} (f : α → ℝ) (hn : ∀ a, 0 ≤ f a) (hs : HasSum f 1)
    (cost : α → ℕ) (q : ℝ) (hc : HasSum (fun a => f a * (cost a : ℝ)) q) :
    expectation (fromReal f hn hs) (fun a => (cost a : ℝ≥0∞)) = ENNReal.ofReal q := by
  unfold expectation fromReal
  change (∑' a, ENNReal.ofReal (f a) * (cost a : ℝ≥0∞)) = ENNReal.ofReal q
  have he (a : α) : ENNReal.ofReal (f a) * (cost a : ℝ≥0∞) =
      ENNReal.ofReal (f a * (cost a : ℝ)) := by
    rw [ENNReal.ofReal_mul (hn a), ENNReal.ofReal_natCast]
  simp_rw [he]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun a => mul_nonneg (hn a) (Nat.cast_nonneg _)) hc.summable,
    hc.tsum_eq]

variable {S X R : Type} [Fintype S] [DecidableEq S] [Fintype X] [DecidableEq X]
    [AddCommGroup R] [Fintype R] [DecidableEq R]

/-- The probability law of terminal traces for verified read-only table search with a nonempty
marked set. -/
def traceLaw (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3)
    (hA : 0 < (ActualSearch.marked F K (ReadOnlyTable.values L)).card) :
    PMF (TerminalTrace X (SourceSizes (Fintype.card X) l)) :=
  fromReal (ReadOnlySearch.terminalMass F K L _)
    (fun tr => (ReadOnlySearch.terminal_law hN F K L l hl hl4 hA).2 tr |>.1)
    (ReadOnlySearch.terminal_law hN F K L l hl hl4 hA).1

/-- The costed law recording the terminal marked input and the total oracle query count from a
search trace. -/
def receipt (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3)
    (hA : 0 < (ActualSearch.marked F K (ReadOnlyTable.values L)).card) : CostedLaw X :=
  (traceLaw hN F K L l hl hl4 hA).map fun tr =>
    (TerminalOutput tr, ReadOnlySearch.terminalQueries (S := S) (R := R) K k _ tr)

/-- Every input supported by the search receipt belongs to the corresponding marked set. -/
theorem receipt_marked (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3)
    (hA : 0 < (ActualSearch.marked F K (ReadOnlyTable.values L)).card)
    (x : X) (c : ℕ) (hm : receipt hN F K L l hl hl4 hA (x,c) ≠ 0) :
    x ∈ ActualSearch.marked F K (ReadOnlyTable.values L) := by
  change (x,c) ∈ ((traceLaw hN F K L l hl hl4 hA).map _).support at hm
  obtain ⟨tr, ht, he⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
  have hx : TerminalOutput tr = x := congrArg Prod.fst he
  by_contra hb
  have hz := (ReadOnlySearch.terminal_law hN F K L l hl hl4 hA).2 tr |>.2
  have hz' := hz (by simpa only [hx] using hb)
  change ENNReal.ofReal (ReadOnlySearch.terminalMass F K L _ tr) ≠ 0 at ht
  exact ht (by rw [hz', ENNReal.ofReal_zero])

/-- The search receipt has a finite nonnegative real expected cost bounded by the explicit
search coefficient times `sqrt (|X| / |marked|)`. -/
theorem receipt_expected (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3)
    (hA : 0 < (ActualSearch.marked F K (ReadOnlyTable.values L)).card) :
    ∃ q : ℝ, expectedCost (receipt hN F K L l hl hl4 hA) = ENNReal.ofReal q ∧
      0 ≤ q ∧ q ≤ (1 + 4*SourcePhaseConstant l) *
        Real.sqrt ((Fintype.card X : ℝ) / (ActualSearch.marked F K (ReadOnlyTable.values L)).card) := by
  obtain ⟨q, hq, hq0, hqb⟩ := ReadOnlySearch.expected_queries hN F K L l hl hl4 hA
  refine ⟨q, ?_, hq0, hqb⟩
  unfold receipt expectedCost
  rw [expectation_map]
  exact fromReal_mean _ _ _ _ q hq

/-- The search receipt augmented with the function value of its returned input, retaining the
same cost coordinate. -/
def recordReceipt (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3)
    (hA : 0 < (ActualSearch.marked F K (ReadOnlyTable.values L)).card) : CostedLaw (X × R) :=
  (receipt hN F K L l hl hl4 hA).map fun z => ((z.1,F z.1),z.2)

/-- Every supported record receipt contains an accurate function record whose input belongs to
the marked set. -/
theorem recordReceipt_valid (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3)
    (hA : 0 < (ActualSearch.marked F K (ReadOnlyTable.values L)).card)
    (p : X × R) (c : ℕ) (hm : recordReceipt hN F K L l hl hl4 hA (p,c) ≠ 0) :
    p.2 = F p.1 ∧ p.1 ∈ ActualSearch.marked F K (ReadOnlyTable.values L) := by
  change (p,c) ∈ ((receipt hN F K L l hl hl4 hA).map _).support at hm
  obtain ⟨z,hz,he⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
  have hp : (z.1,F z.1) = p := congrArg Prod.fst he
  rw [← hp]
  exact ⟨rfl, receipt_marked hN F K L l hl hl4 hA z.1 z.2 hz⟩

/-- Augmenting the search receipt with its function value preserves expected cost. -/
theorem recordReceipt_expected (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3)
    (hA : 0 < (ActualSearch.marked F K (ReadOnlyTable.values L)).card) :
    expectedCost (recordReceipt hN F K L l hl hl4 hA) =
      expectedCost (receipt hN F K L l hl hl4 hA) := by
  unfold recordReceipt expectedCost
  rw [expectation_map]

end Qatlib.Papers.CollisionProb97.MainResults.SearchReceipt
