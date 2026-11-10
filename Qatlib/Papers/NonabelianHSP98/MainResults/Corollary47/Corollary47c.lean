/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonabelianHSP98.MainResults.Corollary47.Basic
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.NonabelianHSP98.MainResults.Corollary47

open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup
open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup.Wreath
open Qatlib.Papers.NonabelianHSP98.MainResults.Pairing
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Orthogonal
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.PerpGroup

variable {n : ℕ}

def subspaceSubgroup (V : Submodule (ZMod 2) (Vec n))
    (hV : ∀ v ∈ V, swapV v ∈ V) : Subgroup (Wreath n) where
  carrier := {g | phi g ∈ V}
  mul_mem' := by
    intro g h hg hh
    change phi (g * h) ∈ V
    rw [phi_mul]
    split_ifs with ha
    · exact V.add_mem hg hh
    · exact V.add_mem hg (hV (phi h) hh)
  one_mem' := by
    show phi (1 : Wreath n) ∈ V
    rw [phi_one]
    exact V.zero_mem
  inv_mem' := by
    intro g hg
    change phi (g⁻¹) ∈ V
    rcases zmod2_eq_zero_or_one g.a with ha | ha
    · rw [inv_eq_base g ha]
      exact hg
    · rw [inv_eq g ha, phi_swapFun]
      exact hV (phi g) hg

@[simp] lemma mem_subspaceSubgroup {V : Submodule (ZMod 2) (Vec n)}
    {hV : ∀ v ∈ V, swapV v ∈ V} {g : Wreath n} :
    g ∈ subspaceSubgroup V hV ↔ phi g ∈ V := Iff.rfl

theorem phiSub_subspaceSubgroup (V : Submodule (ZMod 2) (Vec n))
    (hV : ∀ v ∈ V, swapV v ∈ V) :
    phiSub (subspaceSubgroup V hV) = V := by
  ext v
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hg
  · intro hv
    exact ⟨phiInv v, by simpa [phiInv_phi] using hv, phiInv_phi v⟩

theorem subspaceSubgroup_balanced (V : Submodule (ZMod 2) (Vec n))
    (hV : ∀ v ∈ V, swapV v ∈ V) :
    conjSub (subspaceSubgroup V hV) = subspaceSubgroup V hV := by
  apply conjSub_eq_of_balanced
  intro g hg
  rw [mem_subspaceSubgroup] at hg ⊢
  rw [phi_swapFun]
  exact hV (phi g) hg

theorem phiSub_balanced_of_conjSub (U : Subgroup (Wreath n)) (hU : conjSub U = U) :
    ∀ v ∈ phiSub U, swapV v ∈ phiSub U :=
  (phiSub_balanced_iff U).mp (balanced_of_conjSub_eq U hU)

theorem subspaceSubgroup_phiSub (U : Subgroup (Wreath n)) (hU : conjSub U = U) :
    subspaceSubgroup (phiSub U) (phiSub_balanced_of_conjSub U hU) = U := by
  ext g
  simp only [mem_subspaceSubgroup, mem_phiSub]

theorem corollary_4_7_c_bijection :
    (∀ U : Subgroup (Wreath n), conjSub U = U →
        ∀ v ∈ phiSub U, swapV v ∈ phiSub U) ∧
    (∀ U V : Subgroup (Wreath n), conjSub U = U → conjSub V = V →
        phiSub U = phiSub V → U = V) ∧
    (∀ V : Submodule (ZMod 2) (Vec n), (∀ v ∈ V, swapV v ∈ V) →
        ∃ U : Subgroup (Wreath n), conjSub U = U ∧ phiSub U = V) := by
  refine ⟨phiSub_balanced_of_conjSub, ?_, ?_⟩
  · intro U V _ _ h
    ext g
    rw [← mem_phiSub (U := U), ← mem_phiSub (U := V), h]
  · intro V hV
    exact ⟨subspaceSubgroup V hV, subspaceSubgroup_balanced V hV,
      phiSub_subspaceSubgroup V hV⟩

end Qatlib.Papers.NonabelianHSP98.MainResults.Corollary47
