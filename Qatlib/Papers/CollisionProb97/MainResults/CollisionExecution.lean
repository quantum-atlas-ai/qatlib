/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.SearchReceipt
import Qatlib.Papers.CollisionProb97.MainResults.TableRecords
import Qatlib.Papers.CollisionProb97.MainResults.CollisionCounting
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal Classical
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
namespace Qatlib.Papers.CollisionProb97.MainResults.CollisionExecution
variable {X R : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [AddCommGroup R] [Fintype R] [DecidableEq R]

def table (F : X → R) (K : Finset X) := TablePreparation.loaded F (TablePreparation.inputs K)

def early (F : X → R) (K : Finset X) := TableLookup.internal (TableRecords.rows (table F K))

omit [Nonempty X] [AddCommGroup R] [Fintype R] in

theorem marked_card (F : X → R) (r : ℕ) (hF : RToOne F r) (K : Finset X)
    (he : early F K = none) :
    (ActualSearch.marked F K (ReadOnlyTable.values (table F K))).card = (r-1)*K.card := by
  have hi := TableRecords.no_early_injective F K he
  have hm : ActualSearch.marked F K (ReadOnlyTable.values (table F K)) = collisionCandidates F K := by
    simp only [table, TablePreparation.loaded_values, ActualSearch.marked, collisionCandidates]
  rw [hm]
  exact collisionCandidates_card F r hF K hi

omit [Nonempty X] [AddCommGroup R] [Fintype R] in

theorem marked_pos (F : X → R) (r : ℕ) (hr : 2 ≤ r) (hF : RToOne F r)
    (K : Finset X) (hK : K.Nonempty) (he : early F K = none) :
    0 < (ActualSearch.marked F K (ReadOnlyTable.values (table F K))).card := by
  rw [marked_card F r hF K he]
  exact Nat.mul_pos (by omega) (Finset.card_pos.mpr hK)

def run (F : X → R) (r : ℕ) (hr : 2 ≤ r) (hF : RToOne F r)
    (K : Finset X) (hK : K.Nonempty) (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3) :
    CostedLaw (Option (X × X)) :=
  CostedLaw.charge K.card <|
    if he : early F K = none then
      (SearchReceipt.recordReceipt Fintype.card_pos F K (table F K) l hl hl4
        (marked_pos F r hr hF K hK he)).map fun z =>
          (TableLookup.recover (TableRecords.rows (table F K)) z.1,z.2)
    else CostedLaw.ret (early F K)

omit [Nonempty X] [AddCommGroup R] in

theorem initialization_count (K : Finset X) :
    Qatlib.Foundations.QueryWordCore.Circuit.QueryCount
      (TablePreparation.buildWord (X := X) (R := R) (List.finRange (Fintype.card K))) = K.card := by
  simpa using
    (TablePreparation.buildWord_resources (X := X) (R := R) (List.finRange (Fintype.card K))).1

theorem run_correct (F : X → R) (r : ℕ) (hr : 2 ≤ r) (hF : RToOne F r)
    (K : Finset X) (hK : K.Nonempty) (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3)
    (out : Option (X × X)) (c : ℕ) (hm : run F r hr hF K hK l hl hl4 (out,c) ≠ 0) :
    ∃ s t, out = some (s,t) ∧ s ≠ t ∧ F s = F t := by
  change (out,c) ∈ (CostedLaw.charge K.card _).support at hm
  obtain ⟨z,hz,heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
  have hout : z.1 = out := congrArg Prod.fst heq
  by_cases he : early F K = none
  · simp only [dif_pos he] at hz
    change (z.1,z.2) ∈ ((SearchReceipt.recordReceipt Fintype.card_pos F K (table F K) l hl hl4
      (marked_pos F r hr hF K hK he)).map _).support at hz
    obtain ⟨w,hw,hwz⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
    obtain ⟨hvalue,hmarked⟩ := SearchReceipt.recordReceipt_valid Fintype.card_pos F K (table F K)
      l hl hl4 (marked_pos F r hr hF K hK he) w.1 w.2 hw
    have hp : w.1.1 ∉ K ∧ w.1.2 ∈ ReadOnlyTable.values (table F K) := by
      simpa only [ActualSearch.marked, Finset.mem_filter, Finset.mem_univ, true_and, hvalue] using
          hmarked
    obtain ⟨s,hs,hmrow⟩ := TableRecords.recover_exists (table F K) w.1 hp.2
    obtain ⟨hsK,hsvalue⟩ := (TableRecords.loaded_mem F K s w.1.2).mp hmrow
    refine ⟨s,w.1.1,?_,?_,hsvalue.symm.trans hvalue⟩
    · have hh := congrArg Prod.fst hwz
      exact hout.symm.trans (hh.symm.trans hs)
    · intro hst
      exact hp.1 (hst ▸ hsK)
  · have hz' : z.1 = early F K := by
      have hmem : z ∈ (PMF.pure (early F K,0)).support := by
        simpa only [dif_neg he, CostedLaw.ret] using hz
      exact congrArg Prod.fst ((PMF.mem_support_pure_iff _ _).mp hmem)
    cases hv : early F K with
    | none => exact False.elim (he hv)
    | some p =>
      obtain ⟨s,t⟩ := p
      obtain ⟨_,_,hst,hval⟩ := TableRecords.early_correct F K s t hv
      exact ⟨s,t,hout.symm.trans (hz'.trans hv),hst,hval⟩

theorem run_expected (F : X → R) (r : ℕ) (hr : 2 ≤ r) (hF : RToOne F r)
    (K : Finset X) (hK : K.Nonempty) (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3) :
    expectedCost (run F r hr hF K hK l hl hl4) ≤ (K.card : ℝ≥0∞) +
      ENNReal.ofReal ((1+4*SourcePhaseConstant l)*
        Real.sqrt ((Fintype.card X : ℝ)/(((r-1)*K.card : ℕ):ℝ))) := by
  rw [run, expectedCost_charge]
  apply add_le_add le_rfl
  split_ifs with he
  · obtain ⟨q,hq,_,hqb⟩ := SearchReceipt.receipt_expected Fintype.card_pos F K (table F K)
      l hl hl4 (marked_pos F r hr hF K hK he)
    have hc : expectedCost ((SearchReceipt.recordReceipt Fintype.card_pos F K (table F K)
        l hl hl4 (marked_pos F r hr hF K hK he)).map (fun z =>
          (TableLookup.recover (TableRecords.rows (table F K)) z.1,z.2))) =
        expectedCost (SearchReceipt.receipt Fintype.card_pos F K (table F K)
          l hl hl4 (marked_pos F r hr hF K hK he)) := by
      unfold expectedCost
      rw [expectation_map]
      exact SearchReceipt.recordReceipt_expected _ _ _ _ _ _ _ _
    rw [hc,hq]
    apply ENNReal.ofReal_le_ofReal
    simpa only [marked_card F r hF K he] using hqb
  · simp only [expectedCost_ret, zero_le]

end Qatlib.Papers.CollisionProb97.MainResults.CollisionExecution
