/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Orthogonal

/-!
# Subgroup structure of balanced orthogonal complements

For a subgroup closed under `swapFun`, its orthogonal-complement set contains the identity and
is closed under multiplication and inversion. `perpGroup` bundles this structure. The module
also proves that closure under swapping is equivalent to being fixed by `conjSub`. This
development accompanies [RoettelerBeth1998].

## Main statements

* `perpGroup`: the orthogonal complement bundled as a subgroup under swap closure.
* `perp_balanced`: orthogonal complementation preserves swap closure.
* `conjSub_eq_of_balanced` and `balanced_of_conjSub_eq`: equivalent forms of swap invariance.

## References

* [Roetteler and Beth, 1998][RoettelerBeth1998]
-/

set_option autoImplicit false

namespace Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.PerpGroup

open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup
open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup.Wreath
open Qatlib.Papers.NonabelianHSP98.MainResults.Pairing
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Orthogonal
open Finset

variable {n : ℕ}

/-- The vector image of `g` is orthogonal to `phiSet U` exactly when `g` is in `perpSub U`. -/
theorem phi_mem_orthV {U : Subgroup (Wreath n)} {g : Wreath n} :
    phi g ∈ orthV (phiSet U) ↔ g ∈ perpSub U := by
  rw [mem_perpSub]
  constructor
  · intro H u hu
    have h := H (phi u) ⟨u, hu, rfl⟩
    rwa [← phi_mu] at h
  · intro H s hs
    obtain ⟨u, hu, rfl⟩ := hs
    rw [← phi_mu]
    exact H u hu

/-- The set `perpSub U` is the inverse image under `phi` of the vector orthogonal complement of
`phiSet U`. -/
theorem perpSub_eq_preimage (U : Subgroup (Wreath n)) :
    perpSub U = phi ⁻¹' (orthV (phiSet U)) := by
  ext g
  rw [Set.mem_preimage]
  exact phi_mem_orthV.symm

/-- The identity element belongs to the orthogonal complement of every subgroup. -/
theorem one_mem_perpSub (U : Subgroup (Wreath n)) : (1 : Wreath n) ∈ perpSub U := by
  rw [mem_perpSub]
  intro u _
  rw [phi_mu, phi_one]
  simp [dot]

/-- If `U` is closed under `swapFun`, its orthogonal-complement set is closed under
multiplication. -/
theorem mul_mem_perpSub (U : Subgroup (Wreath n))
    (hbal : ∀ g ∈ U, swapFun g ∈ U) {g h : Wreath n}
    (hg : g ∈ perpSub U) (hh : h ∈ perpSub U) : g * h ∈ perpSub U := by
  rw [mem_perpSub] at hg hh ⊢
  have hgu : phi g ∈ orthV (phiSet U) := phi_mem_orthV.mpr hg
  have hhu : phi h ∈ orthV (phiSet U) := phi_mem_orthV.mpr hh
  have hS : ∀ s ∈ phiSet U, swapV s ∈ phiSet U := (phiSub_balanced_iff U).mp hbal
  have horth := orthV_balanced hS
  have hstep : phi (g * h) ∈ orthV (phiSet U) := by
    rw [phi_mul]
    split_ifs with h0
    · exact orthV_add hgu hhu
    · exact orthV_add hgu (horth (phi h) hhu)
  intro u hu
  have h := hstep (phi u) ⟨u, hu, rfl⟩
  rwa [← phi_mu] at h

/-- If `U` is closed under `swapFun`, its orthogonal-complement set is closed under inversion. -/
theorem inv_mem_perpSub (U : Subgroup (Wreath n))
    (hbal : ∀ g ∈ U, swapFun g ∈ U) {g : Wreath n}
    (hg : g ∈ perpSub U) : g⁻¹ ∈ perpSub U := by
  rw [mem_perpSub] at hg ⊢
  have hgu : phi g ∈ orthV (phiSet U) := phi_mem_orthV.mpr hg
  have hS : ∀ s ∈ phiSet U, swapV s ∈ phiSet U := (phiSub_balanced_iff U).mp hbal
  have horth := orthV_balanced hS
  have hstep : phi (g⁻¹) ∈ orthV (phiSet U) := by
    rcases zmod2_eq_zero_or_one g.a with h0 | h1
    · rw [inv_eq_base g h0]; exact hgu
    · rw [inv_eq g h1, phi_swapFun]; exact horth (phi g) hgu
  intro u hu
  have h := hstep (phi u) ⟨u, hu, rfl⟩
  rwa [← phi_mu] at h

/-- The subgroup with carrier `perpSub U`, constructed when `U` is closed under `swapFun`. -/
def perpGroup (U : Subgroup (Wreath n))
    (hbal : ∀ g ∈ U, swapFun g ∈ U) : Subgroup (Wreath n) where
  carrier := perpSub U
  mul_mem' := mul_mem_perpSub U hbal
  one_mem' := one_mem_perpSub U
  inv_mem' := inv_mem_perpSub U hbal

/-- The underlying set of `perpGroup U hbal` is `perpSub U`. -/
lemma coe_perpGroup (U : Subgroup (Wreath n)) (hbal : ∀ g ∈ U, swapFun g ∈ U) :
    (perpGroup U hbal : Set (Wreath n)) = perpSub U := rfl

/-- The orthogonal complement of a set closed under `swapFun` is closed under `swapFun`. -/
theorem perp_balanced {S : Set (Wreath n)} (hS : ∀ s ∈ S, swapFun s ∈ S) :
    ∀ g ∈ perp S, swapFun g ∈ perp S := by
  intro g hg s hs
  have h := (mu_swapFun_swapFun (swapFun g) s).symm
  rw [h]
  exact hg (swapFun s) (hS s hs)

/-- A subgroup closed under `swapFun` is fixed by `conjSub`. -/
theorem conjSub_eq_of_balanced (U : Subgroup (Wreath n))
    (hbal : ∀ g ∈ U, swapFun g ∈ U) : conjSub U = U := by
  ext g
  constructor
  · intro hg
    obtain ⟨u, hu, rfl⟩ := mem_conjSub.mp hg
    exact hbal u hu
  · intro hg
    exact mem_conjSub.mpr ⟨swapFun g, hbal g hg, swapFun_swapFun g⟩

/-- A subgroup fixed by `conjSub` is closed under `swapFun`. -/
theorem balanced_of_conjSub_eq (U : Subgroup (Wreath n)) (h : conjSub U = U) :
    ∀ g ∈ U, swapFun g ∈ U := by
  intro g hg
  have hg' : g ∈ conjSub U := by rw [h]; exact hg
  obtain ⟨u, hu, heq⟩ := mem_conjSub.mp hg'
  rw [← heq, swapFun_swapFun]
  exact hu

end Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.PerpGroup
