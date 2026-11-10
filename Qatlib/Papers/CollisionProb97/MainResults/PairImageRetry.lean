/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Papers.CollisionProb97.MainResults.AcceptedImageRetry
import Qatlib.Papers.CollisionProb97.MainResults.ReturningStages
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal Classical
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline
namespace Qatlib.Papers.CollisionProb97.MainResults.PairImageRetry
open RetryClockTransport
variable {X R : Type} [Fintype X] [Nonempty X] [Nonempty R] [DecidableEq R]

def nextPair (F : X → R) (T : Finset R) : Unit → PMF (((X × R) ⊕ Unit) × ℕ) :=
  fun _ => (PMF.uniformOfFintype' X).map fun x =>
    let value := F x
    (if value ∉ T then Sum.inl (x,value) else Sum.inr (), 1)

omit [Nonempty R] in

theorem pair_erasure (F : X → R) (T : Finset R) (s : Unit) :
    AcceptedImageRetry.nextRecord F T s = (nextPair F T s).map (mapReceipt Prod.fst id) := by
  simp only [nextPair, AcceptedImageRetry.nextRecord, PMF.map_comp, Function.comp_def]
  congr 1
  funext x
  by_cases hx : F x ∉ T <;> simp [hx, mapReceipt, mapConfig]

def Valid (F : X → R) (T : Finset R) (p : X × R) : Prop := p.2 = F p.1 ∧ p.2 ∉ T

omit [Nonempty R] in

theorem nextPair_positive (F : X → R) (T : Finset R) :
    ∀ s cfg c, nextPair F T s (cfg,c) ≠ 0 → 1 ≤ c := by
  intro s cfg c hm
  change (cfg,c) ∈ (nextPair F T s).support at hm
  obtain ⟨x,_,hx⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
  have hc := congrArg Prod.snd hx
  dsimp at hc
  omega

omit [Nonempty R] in

theorem bad_run (F : X → R) (T : Finset R) (p : X × R) (hp : ¬ Valid F T p)
    (fuel c : ℕ) : branchCostRun (nextPair F T) fuel (.inr ()) (.inl p,c) = 0 := by
  induction fuel generalizing c with
  | zero => simp [branchCostRun, CostedLaw.ret, PMF.pure_apply]
  | succ fuel ih =>
    rw [branchCostRun]
    change (PMF.bind (nextPair F T ()) fun z =>
      CostedLaw.charge z.2 (branchCostRun (nextPair F T) fuel z.1)) (.inl p,c) = 0
    rw [nextPair, PMF.bind_map, PMF.bind_apply]
    apply ENNReal.tsum_eq_zero.mpr
    intro x
    dsimp only [Function.comp_def]
    by_cases hx : F x ∉ T
    · simp only [if_pos hx]
      rw [branchCostRun_halted]
      simp only [CostedLaw.charge, PMF.pure_map, Nat.add_zero]
      have hne : (x,F x) ≠ p := by
        intro he
        apply hp
        rw [← he]
        exact ⟨rfl, hx⟩
      simp [PMF.pure_apply, Ne.symm hne]
    · simp only [if_neg hx]
      rw [Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution.charge_point_mass]
      split_ifs <;> simp [ih]

omit [Nonempty R] in

theorem bad_unbounded (F : X → R) (T : Finset R) (p : X × R) (hp : ¬ Valid F T p) (c : ℕ) :
    generalUnboundedLaw (branchClockNext (nextPair F T)) (branchClockEmbed (.inr ())) (some (p,c)) = 0 := by
  rw [generalUnboundedLaw_apply, generalUnboundedMass_some,
    branchClock_bridge (nextPair F T) (nextPair_positive F T)]
  exact bad_run F T p hp c c

omit [Nonempty R] in

theorem retry_receipt (F : X → R) (r : ℕ) (hr : 0 < r)
    (hF : ∀ y ∈ Finset.univ.image F, (Finset.univ.filter (fun x => F x = y)).card = r)
    (T : Finset R) (hT : T ⊆ Finset.univ.image F)
    (hhalf : 2*T.card ≤ (Finset.univ.image F).card) :
    generalNeverMass (branchClockNext (nextPair F T)) (branchClockEmbed (.inr ())) = 0 ∧
    generalUnboundedTime (branchClockNext (nextPair F T)) (branchClockEmbed (.inr ())) =
      ENNReal.ofReal (((Finset.univ.image F).card : ℝ) / (((Finset.univ.image F).card - T.card : ℕ) : ℝ)) ∧
    generalUnboundedTime (branchClockNext (nextPair F T)) (branchClockEmbed (.inr ())) ≤ 2 := by
  have ht := branch_never_mean_transport Prod.fst (nextPair F T) (AcceptedImageRetry.nextRecord F T)
    (pair_erasure F T) (.inr ())
  have hb := AcceptedImageRetry.record_retry_receipt F r hr hF T hT hhalf
  exact ⟨ht.1.trans hb.1, ht.2.trans hb.2.1, ht.2.le.trans hb.2.2⟩

def returning (F : X → R) (T : Finset R) : CostedLaw (X × R) :=
  ReturningStages.returnLaw (branchClockNext (nextPair F T)) (branchClockEmbed (.inr ()))

theorem returning_valid (F : X → R) (r : ℕ) (hr : 0 < r)
    (hF : ∀ y ∈ Finset.univ.image F, (Finset.univ.filter (fun x => F x = y)).card = r)
    (T : Finset R) (hT : T ⊆ Finset.univ.image F)
    (hhalf : 2*T.card ≤ (Finset.univ.image F).card) (p : X × R) (c : ℕ)
    (hm : returning F T (p,c) ≠ 0) : Valid F T p := by
  have hn := (retry_receipt F r hr hF T hT hhalf).1
  have hs := ReturningStages.returnLaw_nonzero_some (branchClockNext (nextPair F T))
    (branchClockEmbed (.inr ())) hn p c hm
  by_contra hp
  exact hs (bad_unbounded F T p hp c)

theorem returning_expected (F : X → R) (r : ℕ) (hr : 0 < r)
    (hF : ∀ y ∈ Finset.univ.image F, (Finset.univ.filter (fun x => F x = y)).card = r)
    (T : Finset R) (hT : T ⊆ Finset.univ.image F)
    (hhalf : 2*T.card ≤ (Finset.univ.image F).card) :
    CostedLaw.expectedCost (returning F T) =
      ENNReal.ofReal (((Finset.univ.image F).card : ℝ) / (((Finset.univ.image F).card - T.card : ℕ) : ℝ)) ∧
    CostedLaw.expectedCost (returning F T) ≤ 2 := by
  have hr' := retry_receipt F r hr hF T hT hhalf
  have he := ReturningStages.returnLaw_expectedCost (branchClockNext (nextPair F T))
    (branchClockEmbed (.inr ())) hr'.1
  exact ⟨he.trans hr'.2.1, he.le.trans hr'.2.2⟩

end Qatlib.Papers.CollisionProb97.MainResults.PairImageRetry
