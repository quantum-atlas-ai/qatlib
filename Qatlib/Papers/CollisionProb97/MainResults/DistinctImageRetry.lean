/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.FairRandomBits.GeometricRetry
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic
set_option warningAsError false
set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal Classical
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution
open Qatlib.Concepts.FairRandomBits.GeometricRetry
namespace Qatlib.Papers.CollisionProb97.MainResults.DistinctImageRetry
variable {X R : Type} [Fintype X] [Nonempty X] [DecidableEq R]

def newImageCoin (F : X → R) (T : Finset R) : PMF Bool :=
 (PMF.uniformOfFintype' X).map (fun x => decide (F x ∉ T))

def paidFetchNext (F : X → R) (T : Finset R) : Unit → PMF ((Bool ⊕ Unit) × ℕ) :=
 fun _ => (PMF.uniformOfFintype' X).map (fun x =>
   let value := F x
   (if value ∉ T then Sum.inl true else Sum.inr (), 1))

theorem paidFetchNext_eq (F : X → R) (T : Finset R) :
 paidFetchNext F T = branchRetryNext (newImageCoin F T) 1 1 := by
 funext u
 simp [paidFetchNext, branchRetryNext, newImageCoin, PMF.map_comp, Function.comp_def]
omit [Nonempty X] in

theorem count_fiber_set (F : X → R) (r : ℕ)
 (hF : ∀ y ∈ Finset.univ.image F,
    (Finset.univ.filter (fun x => F x = y)).card = r)
 (T : Finset R) (hT : T ⊆ Finset.univ.image F) :
 (Finset.univ.filter (fun x => F x ∈ T)).card = T.card * r := by
 rw [← Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset X) T F]
 rw [Finset.sum_congr rfl (fun y hy => hF y (hT hy))]
 exact Finset.sum_const_nat (fun _ _ => rfl)
omit [Nonempty X] in

theorem domain_card (F : X → R) (r : ℕ)
 (hF : ∀ y ∈ Finset.univ.image F,
    (Finset.univ.filter (fun x => F x = y)).card = r) :
 Fintype.card X = (Finset.univ.image F).card * r := by
 have h := count_fiber_set F r hF (Finset.univ.image F) (Finset.Subset.refl _)
 have he : (Finset.univ.filter (fun x : X => F x ∈ Finset.univ.image F)) = Finset.univ := by
  ext x
  simp
 simpa only [he, Finset.card_univ] using h
omit [Nonempty X] in

theorem new_input_card (F : X → R) (r : ℕ)
 (hF : ∀ y ∈ Finset.univ.image F,
    (Finset.univ.filter (fun x => F x = y)).card = r)
 (T : Finset R) (hT : T ⊆ Finset.univ.image F) :
 (Finset.univ.filter (fun x => F x ∉ T)).card =
   ((Finset.univ.image F).card - T.card) * r := by
 have he : (Finset.univ.filter (fun x : X => F x ∉ T)) =
   Finset.univ.filter (fun x => F x ∈ Finset.univ.image F \ T) := by
  ext x
  simp
 rw [he, count_fiber_set F r hF _ (Finset.sdiff_subset), Finset.card_sdiff_of_subset hT]

theorem newImageCoin_card (F : X → R) (T : Finset R) :
 newImageCoin F T true = ENNReal.ofReal
  (((Finset.univ.filter (fun x => F x ∉ T)).card : ℝ) / Fintype.card X) := by
 rw [newImageCoin, PMF.map_apply, tsum_fintype]
 have hdec (x : X) : (true = decide (F x ∉ T)) ↔ F x ∉ T := by simp
 simp only [PMF.uniformOfFintype'_apply, hdec]
 rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
 rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < Fintype.card X by exact_mod_cast Fintype.card_pos),
   ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
 rfl

theorem newImageCoin_exact (F : X → R) (r : ℕ) (hr : 0 < r)
 (hF : ∀ y ∈ Finset.univ.image F,
    (Finset.univ.filter (fun x => F x = y)).card = r)
 (T : Finset R) (hT : T ⊆ Finset.univ.image F) :
 newImageCoin F T true = ENNReal.ofReal
  ((((Finset.univ.image F).card - T.card : ℕ) : ℝ) /
    (Finset.univ.image F).card) := by
 rw [newImageCoin_card, new_input_card F r hF T hT, domain_card F r hF]
 congr 1
 push_cast
 have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
 field_simp

theorem new_image_retry_receipt (F : X → R) (r : ℕ) (hr : 0 < r)
 (hF : ∀ y ∈ Finset.univ.image F,
    (Finset.univ.filter (fun x => F x = y)).card = r)
 (T : Finset R) (hT : T ⊆ Finset.univ.image F)
 (hhalf : 2 * T.card ≤ (Finset.univ.image F).card) :
 generalNeverMass (branchClockNext (paidFetchNext F T)) (branchClockEmbed (.inr ())) = 0 ∧
 generalUnboundedTime (branchClockNext (paidFetchNext F T)) (branchClockEmbed (.inr ())) =
  ENNReal.ofReal (((Finset.univ.image F).card : ℝ) /
    (((Finset.univ.image F).card - T.card : ℕ) : ℝ)) ∧
 generalUnboundedTime (branchClockNext (paidFetchNext F T)) (branchClockEmbed (.inr ())) ≤ 2 := by
 let m := (Finset.univ.image F).card
 let j := T.card
 have hm : 0 < m := Finset.card_pos.mpr (Finset.image_nonempty.mpr Finset.univ_nonempty)
 have hgap : 0 < m-j := by dsimp [m,j] at *; omega
 have hmR : (0 : ℝ) < m := by exact_mod_cast hm
 have hgR : (0 : ℝ) < (m-j : ℕ) := by exact_mod_cast hgap
 have hp := newImageCoin_exact F r hr hF T hT
 change newImageCoin F T true = ENNReal.ofReal (((m-j : ℕ) : ℝ) / m) at hp
 have hpos : 0 < newImageCoin F T true := by
  rw [hp]
  exact ENNReal.ofReal_pos.mpr (div_pos hgR hmR)
 have hrec := branch_cost_geometric_retry_expected_paid_cost (newImageCoin F T) 1 1
   (by norm_num) (by norm_num) hpos
 simp only [Nat.cast_one] at hrec
 have htotal : newImageCoin F T true + newImageCoin F T false = 1 := by
  simpa only [tsum_bool, add_comm] using (newImageCoin F T).tsum_coe
 have hself : newImageCoin F T true / newImageCoin F T true = 1 :=
  ENNReal.div_self hpos.ne' ((newImageCoin F T).apply_ne_top true)
 have he : (1 : ℝ≥0∞) + 1 * newImageCoin F T false / newImageCoin F T true =
   ENNReal.ofReal ((m:ℝ) / ((m-j : ℕ):ℝ)) := by
  rw [one_mul, ← hself, ← ENNReal.add_div, htotal, one_div, hp,
      ← ENNReal.ofReal_inv_of_pos (div_pos hgR hmR)]
  congr 1
  field_simp
 have hmean := hrec.2.trans he
 have hbound : ((m:ℝ) / ((m-j : ℕ):ℝ)) ≤ 2 := by
  apply (div_le_iff₀ hgR).2
  have hjm : j ≤ m := by dsimp [j,m]; exact Finset.card_le_card hT
  rw [Nat.cast_sub hjm]
  have hhalfR : (2:ℝ) * j ≤ m := by exact_mod_cast hhalf
  linarith
 rw [paidFetchNext_eq]
 exact ⟨hrec.1, hmean,
     hmean.le.trans (by simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hbound)⟩
end Qatlib.Papers.CollisionProb97.MainResults.DistinctImageRetry
