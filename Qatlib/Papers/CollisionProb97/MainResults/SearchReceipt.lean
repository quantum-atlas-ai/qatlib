/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.ReadOnlySearch
import Qatlib.Papers.CollisionProb97.MainResults.ReturningStages
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal Classical
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib.Concepts.AmplitudeSearch.InterruptMin
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
namespace Qatlib.Papers.CollisionProb97.MainResults.SearchReceipt

def fromReal {α : Type} (f : α → ℝ) (hn : ∀ a, 0 ≤ f a) (hs : HasSum f 1) : PMF α :=
  ⟨fun a => ENNReal.ofReal (f a), by
    have ht : ∑' a, ENNReal.ofReal (f a) = 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg hn hs.summable, hs.tsum_eq]
      norm_num
    rw [← ht]
    exact ENNReal.summable.hasSum⟩

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

def traceLaw (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3)
    (hA : 0 < (ActualSearch.marked F K (ReadOnlyTable.values L)).card) :
    PMF (TerminalTrace X (SourceSizes (Fintype.card X) l)) :=
  fromReal (ReadOnlySearch.terminalMass F K L _)
    (fun tr => (ReadOnlySearch.terminal_law hN F K L l hl hl4 hA).2 tr |>.1)
    (ReadOnlySearch.terminal_law hN F K L l hl hl4 hA).1

def receipt (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3)
    (hA : 0 < (ActualSearch.marked F K (ReadOnlyTable.values L)).card) : CostedLaw X :=
  (traceLaw hN F K L l hl hl4 hA).map fun tr =>
    (TerminalOutput tr, ReadOnlySearch.terminalQueries (S := S) (R := R) K k _ tr)

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

def recordReceipt (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3)
    (hA : 0 < (ActualSearch.marked F K (ReadOnlyTable.values L)).card) : CostedLaw (X × R) :=
  (receipt hN F K L l hl hl4 hA).map fun z => ((z.1,F z.1),z.2)

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

theorem recordReceipt_expected (hN : 0 < Fintype.card X) (F : X → R) (K : Finset X) {k : ℕ}
    (L : ReadOnlyTable.Memory (X := S) (R := R) k) (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3)
    (hA : 0 < (ActualSearch.marked F K (ReadOnlyTable.values L)).card) :
    expectedCost (recordReceipt hN F K L l hl hl4 hA) =
      expectedCost (receipt hN F K L l hl hl4 hA) := by
  unfold recordReceipt expectedCost
  rw [expectation_map]

end Qatlib.Papers.CollisionProb97.MainResults.SearchReceipt
