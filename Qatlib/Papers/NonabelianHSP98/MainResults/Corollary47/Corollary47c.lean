/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonabelianHSP98.MainResults.Corollary47.Basic

/-!
# Swap-invariant subspaces and wreath-product subgroups

`subspaceSubgroup` pulls a subspace of `Vec n` closed under `swapV` back along `phi` to a
wreath-product subgroup. The constructions `phiSub` and `subspaceSubgroup` are inverse on
subgroups fixed by `conjSub` and subspaces closed under swapping. This development accompanies
[RoettelerBeth1998].

## Main statements

* `phiSub_subspaceSubgroup`: recovering the original subspace.
* `subspaceSubgroup_phiSub`: recovering a swap-invariant subgroup.
* `corollary_4_7_c_bijection`: stability, injectivity, and surjectivity of the correspondence.

## References

* [Roetteler and Beth, 1998][RoettelerBeth1998]
-/

set_option autoImplicit false

namespace Qatlib.Papers.NonabelianHSP98.MainResults.Corollary47

open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup
open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup.Wreath
open Qatlib.Papers.NonabelianHSP98.MainResults.Pairing
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Orthogonal
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.PerpGroup

variable {n : ℕ}

/-- The wreath-product subgroup whose `phi` coordinates lie in a subspace closed under `swapV`. -/
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

/-- Membership in `subspaceSubgroup V hV` is equivalent to membership of the `phi` image in `V`. -/
@[simp] lemma mem_subspaceSubgroup {V : Submodule (ZMod 2) (Vec n)}
    {hV : ∀ v ∈ V, swapV v ∈ V} {g : Wreath n} :
    g ∈ subspaceSubgroup V hV ↔ phi g ∈ V := Iff.rfl

/-- Applying `phiSub` to the subgroup associated with a swap-invariant subspace recovers that
subspace. -/
theorem phiSub_subspaceSubgroup (V : Submodule (ZMod 2) (Vec n))
    (hV : ∀ v ∈ V, swapV v ∈ V) :
    phiSub (subspaceSubgroup V hV) = V := by
  ext v
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hg
  · intro hv
    exact ⟨phiInv v, by simpa [phiInv_phi] using hv, phiInv_phi v⟩

/-- The subgroup associated with a swap-invariant subspace is fixed by `conjSub`. -/
theorem subspaceSubgroup_balanced (V : Submodule (ZMod 2) (Vec n))
    (hV : ∀ v ∈ V, swapV v ∈ V) :
    conjSub (subspaceSubgroup V hV) = subspaceSubgroup V hV := by
  apply conjSub_eq_of_balanced
  intro g hg
  rw [mem_subspaceSubgroup] at hg ⊢
  rw [phi_swapFun]
  exact hV (phi g) hg

/-- The vector subspace associated with a subgroup fixed by `conjSub` is closed under `swapV`. -/
theorem phiSub_balanced_of_conjSub (U : Subgroup (Wreath n)) (hU : conjSub U = U) :
    ∀ v ∈ phiSub U, swapV v ∈ phiSub U :=
  (phiSub_balanced_iff U).mp (balanced_of_conjSub_eq U hU)

/-- Pulling back the vector subspace of a subgroup fixed by `conjSub` recovers the original
subgroup. -/
theorem subspaceSubgroup_phiSub (U : Subgroup (Wreath n)) (hU : conjSub U = U) :
    subspaceSubgroup (phiSub U) (phiSub_balanced_of_conjSub U hU) = U := by
  ext g
  simp only [mem_subspaceSubgroup, mem_phiSub]

/-- The map `phiSub` sends subgroups fixed by `conjSub` to swap-invariant subspaces, is
injective on these subgroups, and reaches every swap-invariant subspace. See Corollary
4.7(c) of [RoettelerBeth1998]. -/
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
