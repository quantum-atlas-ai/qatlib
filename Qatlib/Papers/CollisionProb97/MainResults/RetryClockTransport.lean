/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.StoppingCore.BranchCostCore.BranchCostExecution
import Mathlib.Tactic
set_option warningAsError false
set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal Classical
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open Qatlib.Concepts.LinearLearning.ConcisePipeline
namespace Qatlib.Papers.CollisionProb97.MainResults.RetryClockTransport
variable {S1 S2 O1 O2 : Type}

def mapConfig (f : O1 → O2) (h : S1 → S2) : O1 ⊕ S1 → O2 ⊕ S2 := Sum.map f h

def mapReceipt (f : O1 → O2) (h : S1 → S2) (z : (O1 ⊕ S1) × ℕ) : (O2 ⊕ S2) × ℕ :=
 (mapConfig f h z.1, z.2)

theorem tick_transport (f : O1 → O2) (h : S1 → S2)
 (n1 : S1 → PMF (O1 ⊕ S1)) (n2 : S2 → PMF (O2 ⊕ S2))
 (hn : ∀ s, n2 (h s) = (n1 s).map (mapConfig f h)) (cfg : O1 ⊕ S1) :
 (tick n1 cfg).map (mapReceipt f h) = tick n2 (mapConfig f h cfg) := by
 cases cfg with
 | inl o => simp [tick, mapReceipt, mapConfig, CostedLaw.ret, PMF.pure_map]
 | inr s => simp [tick, mapReceipt, mapConfig, hn, PMF.map_comp, Function.comp_def]

theorem runFor_transport (f : O1 → O2) (h : S1 → S2)
 (n1 : S1 → PMF (O1 ⊕ S1)) (n2 : S2 → PMF (O2 ⊕ S2))
 (hn : ∀ s, n2 (h s) = (n1 s).map (mapConfig f h))
 (fuel : ℕ) (cfg : O1 ⊕ S1) :
 (runFor n1 fuel cfg).map (mapReceipt f h) = runFor n2 fuel (mapConfig f h cfg) := by
 induction fuel generalizing cfg with
 | zero => simp [runFor, CostedLaw.ret, PMF.pure_map, mapReceipt]
 | succ fuel ih =>
   rw [runFor, runFor, CostedLaw.bind, PMF.map_bind]
   have hc (z : (O1 ⊕ S1) × ℕ) :
     (CostedLaw.charge z.2 (runFor n1 fuel z.1)).map (mapReceipt f h) =
      CostedLaw.charge z.2 (runFor n2 fuel (mapConfig f h z.1)) := by
     rw [← ih z.1]
     simp only [CostedLaw.charge, PMF.map_comp, Function.comp_def, mapReceipt]
   simp_rw [hc]
   rw [← tick_transport f h n1 n2 hn cfg, CostedLaw.bind, PMF.bind_map]
   rfl

theorem pending_transport (f : O1 → O2) (h : S1 → S2)
 (n1 : S1 → PMF (O1 ⊕ S1)) (n2 : S2 → PMF (O2 ⊕ S2))
 (hn : ∀ s, n2 (h s) = (n1 s).map (mapConfig f h))
 (fuel : ℕ) (cfg : O1 ⊕ S1) :
 generalPendingMass n1 cfg fuel = generalPendingMass n2 (mapConfig f h cfg) fuel := by
 unfold generalPendingMass
 rw [← runFor_transport f h n1 n2 hn fuel cfg,
     Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_map]
 apply Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw.event_congr
 rintro ⟨c,k⟩
 cases c <;> simp [mapReceipt, mapConfig]

theorem never_mean_transport (f : O1 → O2) (h : S1 → S2)
 (n1 : S1 → PMF (O1 ⊕ S1)) (n2 : S2 → PMF (O2 ⊕ S2))
 (hn : ∀ s, n2 (h s) = (n1 s).map (mapConfig f h)) (cfg : O1 ⊕ S1) :
 generalNeverMass n1 cfg = generalNeverMass n2 (mapConfig f h cfg) ∧
 generalUnboundedTime n1 cfg = generalUnboundedTime n2 (mapConfig f h cfg) := by
 constructor
 · unfold generalNeverMass
   simp_rw [pending_transport f h n1 n2 hn]
 · unfold generalUnboundedTime
   simp_rw [pending_transport f h n1 n2 hn]

def mapClockState {S : Type} (f : O1 → O2) : BranchClock S O1 → BranchClock S O2
 | .inl s => .inl s
 | .inr z => .inr (mapConfig f id z.1, z.2)

theorem mapClock_embed {S : Type} (f : O1 → O2) (cfg : O1 ⊕ S) :
 mapConfig f (mapClockState f) (branchClockEmbed cfg) = branchClockEmbed (mapConfig f id cfg) := by
 cases cfg <;> rfl

theorem mapClock_delay {S : Type} (f : O1 → O2) (cfg : O1 ⊕ S) (k : ℕ) :
 mapConfig f (mapClockState f) (branchClockDelay cfg k) = branchClockDelay (mapConfig f id cfg) k := by
 cases cfg <;> by_cases hk : k=0 <;>
  simp [branchClockDelay, hk, mapClockState, mapConfig, branchClockEmbed]

theorem clock_next_transport {S : Type} (f : O1 → O2)
 (n1 : S → PMF ((O1 ⊕ S) × ℕ)) (n2 : S → PMF ((O2 ⊕ S) × ℕ))
 (hn : ∀ s, n2 s = (n1 s).map (mapReceipt f id)) (s : BranchClock S O1) :
 branchClockNext n2 (mapClockState f s) =
  (branchClockNext n1 s).map (mapConfig f (mapClockState f)) := by
 cases s with
 | inl s =>
   simp only [mapClockState, branchClockNext, hn, PMF.map_comp, Function.comp_def]
   congr 1
   funext z
   exact (mapClock_delay f z.1 (z.2-1)).symm
 | inr z =>
   simp only [mapClockState, branchClockNext, PMF.pure_map]
   exact congrArg PMF.pure (mapClock_delay f z.1 (z.2-1)).symm

theorem branch_never_mean_transport {S : Type} (f : O1 → O2)
 (n1 : S → PMF ((O1 ⊕ S) × ℕ)) (n2 : S → PMF ((O2 ⊕ S) × ℕ))
 (hn : ∀ s, n2 s = (n1 s).map (mapReceipt f id)) (cfg : O1 ⊕ S) :
 generalNeverMass (branchClockNext n1) (branchClockEmbed cfg) =
  generalNeverMass (branchClockNext n2) (branchClockEmbed (mapConfig f id cfg)) ∧
 generalUnboundedTime (branchClockNext n1) (branchClockEmbed cfg) =
  generalUnboundedTime (branchClockNext n2) (branchClockEmbed (mapConfig f id cfg)) := by
 have h := never_mean_transport f (mapClockState f) (branchClockNext n1) (branchClockNext n2)
   (clock_next_transport f n1 n2 hn) (branchClockEmbed cfg)
 simpa only [mapClock_embed] using h
end Qatlib.Papers.CollisionProb97.MainResults.RetryClockTransport
