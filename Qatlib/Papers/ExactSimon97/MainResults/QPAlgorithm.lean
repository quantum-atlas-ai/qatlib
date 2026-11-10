/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExactSimon97.MainResults.BasisGenerators
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ExactSimon97.MainResults

theorem linIndep_card_le {n k : ℕ} (v : Fin k → BoolVec n) (hv : LinIndep v) :
    k ≤ n := by
  have hk := hv.fintype_card_le_finrank
  rw [Module.finrank_fin_fun] at hk
  simpa using hk

theorem theorem5_generating_set_card_le {n : ℕ}
    (H0 : Submodule (ZMod 2) (BoolVec n)) :
    ∃ Y : Finset (BoolVec n), Y.card ≤ n ∧
      (∀ y ∈ Y, y ∈ H0) ∧
      Submodule.span (ZMod 2) (Y : Set (BoolVec n)) = H0 := by
  classical
  obtain ⟨k, v, hv, hgen⟩ := exists_linIndep_generates H0
  refine ⟨Finset.univ.image v, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hv.injective]
    simpa using linIndep_card_le v hv
  · intro y hy
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    have hvmem : v i ∈ Submodule.span (ZMod 2) (Set.range v) :=
      Submodule.subset_span ⟨i, rfl⟩
    rwa [hgen] at hvmem
  · have hcoee : ((Finset.univ.image v : Finset (BoolVec n)) : Set (BoolVec n)) =
        Set.range v := by
      ext y
      simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rw [hcoee, hgen]

end Qatlib.Papers.ExactSimon97.MainResults
