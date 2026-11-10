/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstructionDefs
import Mathlib.Tactic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QPowerSimon97.StandardDefs

open Qatlib.Concepts.PauliClifford.ExactRank
open Qatlib.Papers.QPowerSimon97.Recovery
open Qatlib.Concepts.HspRecovery.ReductionCore

def zeroMaskCounter (x : BooleanVec 3) : BooleanVec 3 :=
  ![x 2, if x 2 = 0 then x 1 else x 0, 0]

theorem zeroMaskCounter_strict : SimonStrictTwoToOne 0 zeroMaskCounter := by
  constructor
  · intro x
    simp
  · simp only [Nat.card_eq_fintype_card]
    decide

theorem zeroMaskCounter_no_period :
    ∀ s : BooleanVec 3, s ≠ 0 → ¬ ∀ x, zeroMaskCounter x = zeroMaskCounter (x + s) := by
  decide

theorem zeroMaskCounter_not_injective : ¬ Function.Injective zeroMaskCounter := by
  decide

theorem zeroMaskCounter_no_secret :
    ¬ ∃ s : BooleanVec 3, BooleanSimonPromise zeroMaskCounter s := by
  unfold BooleanSimonPromise
  decide

theorem zeroMaskCounter_twoToOne_mass :
    simonTwoToOneDist (0 : BooleanVec 3) zeroMaskCounter ≠ 0 := by
  classical
  let witness : {f : BooleanVec 3 → BooleanVec 3 // SimonStrictTwoToOne 0 f} :=
    ⟨zeroMaskCounter, zeroMaskCounter_strict⟩
  have hne : Nonempty {f : BooleanVec 3 → BooleanVec 3 // SimonStrictTwoToOne 0 f} :=
    ⟨witness⟩
  let law := PMF.map
    (fun g : {f : BooleanVec 3 → BooleanVec 3 // SimonStrictTwoToOne 0 f} => g.val)
    (@PMF.uniformOfFintype' _ (Fintype.ofFinite _) hne)
  have hlink : simonTwoToOneDist (0 : BooleanVec 3) = law := by
    unfold simonTwoToOneDist
    rw [dif_pos hne]
    simp [law, PMF.map, Function.comp_def, PMF.monad_map_eq_map]
  rw [hlink]
  apply (PMF.mem_support_iff law zeroMaskCounter).mp
  exact (PMF.mem_support_map_iff
    (fun g : {f : BooleanVec 3 → BooleanVec 3 // SimonStrictTwoToOne 0 f} => g.val)
    (@PMF.uniformOfFintype' _ (Fintype.ofFinite _) hne) zeroMaskCounter).mpr
      (by exact ⟨witness, @PMF.mem_support_uniformOfFintype' _ (Fintype.ofFinite _) hne witness, rfl⟩)

theorem zeroMaskCounter_construction_mass :
    simonOracleConstruction 3 (true, zeroMaskCounter) ≠ 0 := by
  classical
  apply (PMF.mem_support_iff _ _).mp
  unfold simonOracleConstruction
  apply (PMF.mem_support_bind_iff _ _ _).mpr
  refine ⟨0, PMF.mem_support_uniformOfFintype' _, ?_⟩
  apply (PMF.mem_support_bind_iff _ _ _).mpr
  refine ⟨true, PMF.mem_support_uniformOfFintype' _, ?_⟩
  simp only [↓reduceIte]
  exact (PMF.mem_support_map_iff _ _ _).mpr
    ⟨zeroMaskCounter, zeroMaskCounter_twoToOne_mass, rfl⟩

theorem printedConstruction_not_all_promised :
    ¬ ∀ f : BooleanVec 3 → BooleanVec 3,
      simonOracleConstruction 3 (true, f) ≠ 0 →
        ∃ s : BooleanVec 3, BooleanSimonPromise f s := by
  intro h
  exact zeroMaskCounter_no_secret (h zeroMaskCounter zeroMaskCounter_construction_mass)

end Qatlib.Papers.QPowerSimon97.StandardDefs
