/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Papers.CollisionProb97.MainResults.DistinctImageRetry
import Qatlib.Papers.CollisionProb97.MainResults.RetryClockTransport

/-!
# Retry sampling for a new image value

This module models repeated uniform input sampling until the function value lies outside an
existing image set. The costed transition `nextRecord` retains the accepted input, and the
analysis supplies a sampling step for the collision and claw constructions associated with
[BrassardHoyerTapp1998Collision].

## Main statements

* `returned_record_new`: every returned record has a new image value.
* `record_retry_receipt`: under uniform positive fiber size and a half-image bound,
  nontermination mass is zero and mean query cost is at most two.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Collision]
-/

set_option warningAsError false
set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal Classical
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution
open Qatlib.Concepts.FairRandomBits.GeometricRetry
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline
namespace Qatlib.Papers.CollisionProb97.MainResults.AcceptedImageRetry
open Qatlib.Papers.CollisionProb97.MainResults.RetryClockTransport
open Qatlib.Papers.CollisionProb97.MainResults.DistinctImageRetry
variable {X R : Type} [Fintype X] [Nonempty X] [DecidableEq R]

/-- One uniform sample from `X`, charged one query, returning the sampled input if its image is
outside `T` and otherwise requesting another sample. -/
def nextRecord (F : X → R) (T : Finset R) : Unit → PMF ((X ⊕ Unit) × ℕ) :=
 fun _ => (PMF.uniformOfFintype' X).map (fun x =>
   (if F x ∉ T then Sum.inl x else Sum.inr (), 1))

/-- The paid-fetch transition is obtained from `nextRecord` by the stated receipt-erasure map. -/
theorem record_erasure (F : X → R) (T : Finset R) (s : Unit) :
 paidFetchNext F T s = (nextRecord F T s).map (mapReceipt (fun _ : X => true) id) := by
 simp only [paidFetchNext, nextRecord, PMF.map_comp, Function.comp_def]
 congr 1
 funext x
 by_cases hx : F x ∉ T <;> simp [hx, mapReceipt, mapConfig]

/-- Every transition of `nextRecord` with nonzero mass incurs a cost of at least one. -/
theorem nextRecord_positive (F : X → R) (T : Finset R) :
 ∀ s cfg k, nextRecord F T s (cfg,k) ≠ 0 → 1 ≤ k := by
 intro s cfg k hm
 change (cfg,k) ∈ (nextRecord F T s).support at hm
 obtain ⟨x,_,hx⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
 have hk := congrArg Prod.snd hx
 dsimp at hk
 omega

/-- A finite retry execution has zero mass on a returned input whose image already belongs to
`T`, for every fuel and cost. -/
theorem nextRecord_bad_run (F : X → R) (T : Finset R) (x : X) (hx : F x ∈ T)
 (fuel k : ℕ) : branchCostRun (nextRecord F T) fuel (.inr ()) (.inl x,k) = 0 := by
 induction fuel generalizing k with
 | zero => simp [branchCostRun, CostedLaw.ret, PMF.pure_apply]
 | succ fuel ih =>
   rw [branchCostRun]
   change (PMF.bind (nextRecord F T ()) (fun z =>
     CostedLaw.charge z.2 (branchCostRun (nextRecord F T) fuel z.1))) (.inl x,k) = 0
   rw [nextRecord, PMF.bind_map, PMF.bind_apply]
   apply ENNReal.tsum_eq_zero.mpr
   intro y
   dsimp only [Function.comp_def]
   by_cases hy : F y ∉ T
   · simp only [if_pos hy]
     rw [branchCostRun_halted]
     simp only [CostedLaw.charge, PMF.pure_map, Nat.add_zero]
     have hxy : y ≠ x := by intro h; subst y; exact hy hx
     simp [PMF.pure_apply, Ne.symm hxy]
   · simp only [if_neg hy]
     rw [Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution.charge_point_mass]
     split_ifs <;> simp [ih]

/-- The unbounded retry law assigns zero mass to any returned record whose image already belongs
to `T`. -/
theorem unbounded_bad_record_zero (F : X → R) (T : Finset R) (x : X) (hx : F x ∈ T)
 (k : ℕ) :
 generalUnboundedLaw (branchClockNext (nextRecord F T)) (branchClockEmbed (.inr ()))
   (some (x,k)) = 0 := by
 rw [generalUnboundedLaw_apply, generalUnboundedMass_some,
   branchClock_bridge (nextRecord F T) (nextRecord_positive F T)]
 exact nextRecord_bad_run F T x hx k k

/-- Every record returned with nonzero mass by the unbounded retry law has an image outside `T`. -/
theorem returned_record_new (F : X → R) (T : Finset R) (x : X) (k : ℕ)
 (hm : generalUnboundedLaw (branchClockNext (nextRecord F T)) (branchClockEmbed (.inr ()))
   (some (x,k)) ≠ 0) : F x ∉ T := by
 intro hx
 exact hm (unbounded_bad_record_zero F T x hx k)

/-- For a function with uniform positive fiber size and an excluded image set occupying at most
half the image, retries terminate with zero nontermination mass and mean cost `|image
F|/(|image F|-|T|) ≤ 2`. -/
theorem record_retry_receipt (F : X → R) (r : ℕ) (hr : 0 < r)
 (hF : ∀ y ∈ Finset.univ.image F,
    (Finset.univ.filter (fun x => F x = y)).card = r)
 (T : Finset R) (hT : T ⊆ Finset.univ.image F)
 (hhalf : 2 * T.card ≤ (Finset.univ.image F).card) :
 generalNeverMass (branchClockNext (nextRecord F T)) (branchClockEmbed (.inr ())) = 0 ∧
 generalUnboundedTime (branchClockNext (nextRecord F T)) (branchClockEmbed (.inr ())) =
  ENNReal.ofReal (((Finset.univ.image F).card : ℝ) /
    (((Finset.univ.image F).card - T.card : ℕ) : ℝ)) ∧
 generalUnboundedTime (branchClockNext (nextRecord F T)) (branchClockEmbed (.inr ())) ≤ 2 := by
 have ht := branch_never_mean_transport (fun _ : X => true)
   (nextRecord F T) (paidFetchNext F T) (record_erasure F T) (.inr ())
 have hb := new_image_retry_receipt F r hr hF T hT hhalf
 exact ⟨ht.1.trans hb.1, ht.2.trans hb.2.1, ht.2.le.trans hb.2.2⟩
end Qatlib.Papers.CollisionProb97.MainResults.AcceptedImageRetry
