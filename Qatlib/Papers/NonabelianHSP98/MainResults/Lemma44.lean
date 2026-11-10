/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Counting
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.NonabelianHSP98.MainResults.Lemma44

open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup
open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup.Wreath
open Qatlib.Papers.NonabelianHSP98.MainResults.Pairing
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Orthogonal
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Counting
open Finset

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

theorem lemma_4_4 (U : Subgroup (Wreath n)) (y : Wreath n)
    (hcard : 4 ≤ Fintype.card U)
    (hy : ¬ ∀ u : U, mu (u : Wreath n) y = 0) :
    (∑ u : U, mu (u : Wreath n) y) = 0 := by
  rw [sum_mu_eq_sum_dot]
  have hne : ∃ w ∈ phiSub U, dot (phi y) w ≠ 0 := by
    obtain ⟨u, hu⟩ := not_forall.mp hy
    refine ⟨phi u, mem_phiSub.mpr u.2, ?_⟩
    rw [dot_comm, ← phi_mu]
    exact hu
  have h4 : 4 ∣ Fintype.card (phiSub U) := by
    rw [card_phiSub]
    exact four_dvd_card_subgroup U hcard
  exact sum_dot_eq_zero (phiSub U) (phi y) hne h4

end Qatlib.Papers.NonabelianHSP98.MainResults.Lemma44
