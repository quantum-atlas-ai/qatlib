/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.ClawExecution
import Qatlib.Papers.CollisionProb97.MainResults.CollisionExecution
import Qatlib.Papers.CollisionProb97.MainResults.OraclePairLaw
import Qatlib.Papers.CollisionProb97.MainResults.Theorem4ClawBijection
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal Classical
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
namespace Qatlib.Papers.CollisionProb97.MainResults.BijectiveClaw
variable {S X R : Type} [Fintype S] [DecidableEq S] [Fintype X] [DecidableEq X] [Nonempty X]
    [AddCommGroup R] [Fintype R] [DecidableEq R]

omit [DecidableEq X] [Nonempty X] [AddCommGroup R] in

theorem image_univ (G : X → R) (hG : Function.Surjective G) : Finset.univ.image G = Finset.univ := by
  ext z
  simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
  exact hG z

omit [Fintype S] [Nonempty X] [AddCommGroup R] in

theorem marked_card (F : S → R) (hF : Function.Injective F)
    (G : X → R) (hG : Function.Bijective G) (K : Finset S) :
    (ActualSearch.marked G ∅ (ReadOnlyTable.values (CollisionExecution.table F K))).card = K.card := by
  rw [ClawExecution.marked_card G 1 (rToOne_one_of_injective G hG.1) _
    (by rw [image_univ G hG.2]; exact Finset.subset_univ _),
    CollisionExecution.table, TablePreparation.loaded_values, Finset.card_image_of_injective _ hF,
    mul_one]

omit [Fintype S] [Nonempty X] [AddCommGroup R] in

theorem marked_pos (F : S → R) (hF : Function.Injective F)
    (G : X → R) (hG : Function.Bijective G) (K : Finset S) (hK : K.Nonempty) :
    0 < (ActualSearch.marked G ∅ (ReadOnlyTable.values (CollisionExecution.table F K))).card := by
  rw [marked_card F hF G hG K]
  exact Finset.card_pos.mpr hK

def run (F : S → R) (hF : Function.Injective F) (G : X → R) (hG : Function.Bijective G)
    (K : Finset S) (hK : K.Nonempty) (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3) :
    PMF (Option (S × X) × (ℕ × ℕ)) :=
  OraclePairLaw.join (CostedLaw.charge K.card (CostedLaw.ret ())) fun _ =>
    ClawExecution.search G (CollisionExecution.table F K) l hl hl4 (marked_pos F hF G hG K hK)

theorem run_correct (F : S → R) (hF : Function.Injective F) (G : X → R) (hG : Function.Bijective G)
    (K : Finset S) (hK : K.Nonempty) (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3)
    (out : Option (S × X)) (a b : ℕ) (hm : run F hF G hG K hK l hl hl4 (out,(a,b)) ≠ 0) :
    ∃ s x, out = some (s,x) ∧ F s = G x := by
  obtain ⟨_,_,hs⟩ := OraclePairLaw.support _ _ out a b hm
  exact ClawExecution.search_correct F G _ (fun _ => rfl) l hl hl4 _ out b hs

theorem run_Fmean (F : S → R) (hF : Function.Injective F) (G : X → R) (hG : Function.Bijective G)
    (K : Finset S) (hK : K.Nonempty) (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3) :
    expectation (run F hF G hG K hK l hl hl4) (fun z => (z.2.1 : ℝ≥0∞)) = K.card := by
  rw [run, OraclePairLaw.first_mean, expectedCost_charge, expectedCost_ret, add_zero]

theorem run_Gbound (F : S → R) (hF : Function.Injective F) (G : X → R) (hG : Function.Bijective G)
    (K : Finset S) (hK : K.Nonempty) (l : ℝ) (hl : 1 < l) (hl4 : l < 4/3) :
    expectation (run F hF G hG K hK l hl hl4) (fun z => (z.2.2 : ℝ≥0∞)) ≤
      ENNReal.ofReal ((1+4*SourcePhaseConstant l)*Real.sqrt ((Fintype.card X:ℝ)/K.card)) := by
  apply OraclePairLaw.second_bound
  intro _
  simpa only [marked_card F hF G hG K] using
    ClawExecution.search_expected G (CollisionExecution.table F K) l hl hl4 (marked_pos F hF G hG K hK)

end Qatlib.Papers.CollisionProb97.MainResults.BijectiveClaw
