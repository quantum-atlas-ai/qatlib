/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Qatlib.Papers.NonabelianHSP98.MainResults.Pairing

/-!
# Orthogonality through binary vector coordinates

`phi_mu` identifies the wreath-product pairing with the binary dot product, while `phi_mul`
describes multiplication through a possible block swap. Subgroups map to binary subspaces under
`phiSub`. The constructions `orthV` and `perp` correspond under `phi`, reverse inclusions, and
satisfy double-complement identities for subspaces and subgroups. This development accompanies
[RoettelerBeth1998].

## Main statements

* `phi_mu`: the pairing becomes the vector dot product.
* `phiSub`: the vector subspace associated with a wreath-product subgroup.
* `orthV_orthV`: double vector orthogonal complementation.
* `perpSub_perpSub`: double orthogonal complementation recovers a subgroup.

## References

* [Roetteler and Beth, 1998][RoettelerBeth1998]
-/

set_option autoImplicit false

namespace Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Orthogonal

open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup
open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup.Wreath
open Qatlib.Papers.NonabelianHSP98.MainResults.Pairing
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel
open Finset

variable {n : ℕ}

/-- When `g.a = 1`, the vector coordinates of `g` are its swapped blocks followed by one. -/
@[simp] lemma phi_of_a_one_eq {g : Wreath n} (h : g.a = 1) :
    phi g = (g.y, g.x, 1) := phi_of_a_one (by simp [h])

macro "zring" : tactic => `(tactic| (ring_nf <;> reduce_mod_char))

/-- The vector operation that swaps the two length-`n` blocks and preserves the final
coordinate. -/
def swapV (v : Vec n) : Vec n := (v.2.1, v.1, v.2.2)

/-- Applying `swapV` twice gives the original vector. -/
@[simp] lemma swapV_swapV (v : Vec n) : swapV (swapV v) = v := rfl

/-- The map `phi` intertwines `swapFun` with `swapV`. -/
@[simp] lemma phi_swapFun (g : Wreath n) : phi (swapFun g) = swapV (phi g) := by
  rcases zmod2_eq_zero_or_one g.a with h | h
  · have h' : (swapFun g).a = 0 := by simp [h]
    rw [phi_of_a_zero h, phi_of_a_zero h']
    rfl
  · have h' : (swapFun g).a ≠ 0 := by simp [h]
    rw [phi_of_a_one_eq h, phi_of_a_one h']
    rfl

/-- The element `t n` maps to the vector with zero blocks and final coordinate one. -/
@[simp] lemma phi_t : phi (t n) = ((0 : Fin n → ZMod 2), (0 : Fin n → ZMod 2), (1 : ZMod 2)) := by
  have h : (t n).a ≠ 0 := by simp
  rw [phi_of_a_one h]
  simp [t]

/-- The wreath-product pairing equals the dot product of the two `phi` images. -/
theorem phi_mu (g h : Wreath n) : mu g h = dot (phi g) (phi h) := by
  rcases zmod2_eq_zero_or_one g.a with hg | hg <;>
    rcases zmod2_eq_zero_or_one h.a with hh | hh
  · rw [mu_zero_zero g h hg hh, phi_of_a_zero hg, phi_of_a_zero hh]
    simp [dot]
  · rw [mu_zero_one g h hg hh, phi_of_a_zero hg, phi_of_a_one_eq hh]
    simp only [dot, mul_zero, zero_mul, add_zero]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => (mul_comm (g.y i) (h.x i)).symm)
  · rw [mu_one_zero g h hg hh, phi_of_a_one_eq hg, phi_of_a_zero hh]
    simp only [dot, mul_zero, add_zero]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => mul_comm (h.x i) (g.y i))
  · rw [mu_one_one g h hg hh, phi_of_a_one_eq hg, phi_of_a_one_eq hh]
    simp only [dot, mul_one, add_zero]
    ac_rfl

/-- The wreath-product pairing is symmetric. -/
theorem mu_comm (g h : Wreath n) : mu g h = mu h g := by
  rw [phi_mu, phi_mu, dot_comm]

/-- When the left factor has final coordinate zero, `phi` sends its product with `h` to the sum
of their vector images. -/
theorem phi_mul_of_a_zero (u h : Wreath n) (hu : u.a = 0) :
    phi (u * h) = phi u + phi h := by
  rcases zmod2_eq_zero_or_one h.a with hh | hh
  · have hua : (u * h).a = 0 := by
      change (mulW u h).a = 0
      rw [mulW_a, hu, hh]
      simp
    rw [phi_of_a_zero hua, phi_of_a_zero hu, phi_of_a_zero hh]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext i
      change (mulW u h).x i = u.x i + h.x i
      rw [mulW_x, hh]; zring
    · funext i
      change (mulW u h).y i = u.y i + h.y i
      rw [mulW_y, hh]; zring
    · simp [hua, hu, hh]
  · have hua : (u * h).a ≠ 0 := by
      change (mulW u h).a ≠ 0
      rw [mulW_a, hu, hh]
      simp
    rw [phi_of_a_one hua, phi_of_a_zero hu, phi_of_a_one_eq hh]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext i
      change (mulW u h).y i = u.x i + h.y i
      rw [mulW_y, hh]; zring
    · funext i
      change (mulW u h).x i = u.y i + h.x i
      rw [mulW_x, hh]; zring
    · simp [hua, hu, hh]

/-- When the left factor has final coordinate one, the product image is `phi g + swapV (phi h)`. -/
theorem phi_mul_of_a_one (g h : Wreath n) (hg : g.a = 1) :
    phi (g * h) = phi g + swapV (phi h) := by
  rcases zmod2_eq_zero_or_one h.a with hh | hh
  · have hga : (g * h).a ≠ 0 := by
      change (mulW g h).a ≠ 0
      rw [mulW_a, hg, hh]
      simp
    rw [phi_of_a_one hga, phi_of_a_one_eq hg, phi_of_a_zero hh]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext i
      change (mulW g h).y i = g.y i + h.y i
      rw [mulW_y, hh]; zring
    · funext i
      change (mulW g h).x i = g.x i + h.x i
      rw [mulW_x, hh]; zring
    · simp only [swapV, Prod.snd_add]
      zring
  · have hga : (g * h).a = 0 := by
      change (mulW g h).a = 0
      rw [mulW_a, hg, hh]
      zring
    rw [phi_of_a_zero hga, phi_of_a_one_eq hg, phi_of_a_one_eq hh]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext i
      change (mulW g h).x i = g.y i + h.x i
      rw [mulW_x, hh]; zring
    · funext i
      change (mulW g h).y i = g.x i + h.y i
      rw [mulW_y, hh]; zring
    · simp only [swapV, Prod.snd_add]
      zring

/-- The image of a product is `phi g` plus either `phi h` or its block swap, according to the
final coordinate of `g`. -/
theorem phi_mul (g h : Wreath n) :
    phi (g * h) = phi g + (if g.a = 0 then phi h else swapV (phi h)) := by
  rcases zmod2_eq_zero_or_one g.a with hg | hg
  · rw [if_pos hg, phi_mul_of_a_zero g h hg]
  · rw [if_neg (by simp [hg]), phi_mul_of_a_one g h hg]

/-- Right multiplication by `t n` adds `phi (t n)` to the vector image. -/
theorem phi_mul_t (g : Wreath n) : phi (g * t n) = phi g + phi (t n) := by
  rcases zmod2_eq_zero_or_one g.a with hg | hg
  · exact phi_mul_of_a_zero g (t n) hg
  · simpa using! phi_mul_of_a_one g (t n) hg

/-- Right multiplication by `t n` adds the vector with zero blocks and final coordinate one. -/
theorem phi_mul_t' (g : Wreath n) :
    phi (g * t n) = phi g + ((0 : Fin n → ZMod 2), (0 : Fin n → ZMod 2), (1 : ZMod 2)) := by
  rw [phi_mul_t, phi_t]

/-- The inverse of an element with final coordinate one is its block swap. -/
theorem inv_eq (g : Wreath n) (hg : g.a = 1) : g⁻¹ = swapFun g := by
  change invW g = swapFun g
  apply Wreath.ext
  · funext i
    simp only [invW_x, swapFun_x, hg]
    zring
  · funext i
    simp only [invW_y, swapFun_y, hg]
    zring
  · simp only [invW_a, swapFun_a]

/-- An element with final coordinate zero equals its inverse. -/
theorem inv_eq_base (g : Wreath n) (hg : g.a = 0) : g⁻¹ = g := by
  change invW g = g
  apply Wreath.ext
  · funext i
    simp only [invW_x, hg]
    zring
  · funext i
    simp only [invW_y, hg]
    zring
  · simp only [invW_a]

/-- Simultaneous swapping of both arguments preserves the pairing. -/
theorem mu_swap (g h : Wreath n) : mu (swapFun g) (swapFun h) = mu g h :=
  mu_swapFun_swapFun g h

/-- The dot product is additive in its right argument. -/
theorem dot_add_right (u v w : Vec n) : dot u (v + w) = dot u v + dot u w := by
  simp only [dot, Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]
  abel

/-- The dot product is additive in its left argument. -/
theorem dot_add_left (u v w : Vec n) : dot (u + v) w = dot u w + dot v w := by
  simp only [dot, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]
  abel

/-- The image set of a subgroup under `phi`. -/
def phiSet (U : Subgroup (Wreath n)) : Set (Vec n) := phi '' (U : Set (Wreath n))

/-- A subgroup containing an element with final coordinate one is closed under `swapFun`. -/
theorem balanced_of_exists_a_one (U : Subgroup (Wreath n))
    (h : ∃ g ∈ U, g.a = 1) : ∀ g ∈ U, swapFun g ∈ U := by
  obtain ⟨g₀, hg₀, hg₀a⟩ := h
  intro g hg
  rcases zmod2_eq_zero_or_one g.a with hg0 | hg1
  · have hconj : g₀⁻¹ * g * g₀ = swapFun g := by
      rw [inv_eq g₀ hg₀a]
      change mulW (mulW (swapFun g₀) g) g₀ = swapFun g
      apply Wreath.ext
      · funext i
        simp only [mulW_x, mulW_y, swapFun_x, swapFun_y, hg0, hg₀a]
        zring
      · funext i
        simp only [mulW_x, mulW_y, swapFun_x, swapFun_y, hg0, hg₀a]
        zring
      · simp only [mulW_a, swapFun_a, hg0, hg₀a]
        zring
    rw [← hconj]
    exact U.mul_mem (U.mul_mem (U.inv_mem hg₀) hg) hg₀
  · rw [← cube_of_a_one hg1]
    exact U.mul_mem (U.mul_mem hg hg) hg

/-- Closure of a subgroup under `swapFun` is equivalent to closure of its `phi` image under
`swapV`. -/
theorem phiSub_balanced_iff (U : Subgroup (Wreath n)) :
    (∀ g ∈ U, swapFun g ∈ U) ↔ (∀ v ∈ phiSet U, swapV v ∈ phiSet U) := by
  constructor
  · intro h v hv
    obtain ⟨g, hg, rfl⟩ := hv
    exact ⟨swapFun g, h g hg, phi_swapFun g⟩
  · intro h g hg
    have hv : phi g ∈ phiSet U := ⟨g, hg, rfl⟩
    have := h (phi g) hv
    rw [← phi_swapFun] at this
    obtain ⟨w, hw, hweq⟩ := this
    exact (phi_inj hweq.symm) ▸ hw

/-- The `phi` image of a subgroup is closed under vector addition. -/
theorem phiSet_add_mem (U : Subgroup (Wreath n)) {u v : Vec n}
    (hu : u ∈ phiSet U) (hv : v ∈ phiSet U) : u + v ∈ phiSet U := by
  obtain ⟨u₁, hu₁, rfl⟩ := hu
  obtain ⟨u₂, hu₂, rfl⟩ := hv
  rcases zmod2_eq_zero_or_one u₁.a with h1 | h1
  · rw [← phi_mul_of_a_zero u₁ u₂ h1]
    exact ⟨u₁ * u₂, U.mul_mem hu₁ hu₂, rfl⟩
  · have hbal := balanced_of_exists_a_one U ⟨u₁, hu₁, h1⟩
    have hprod : phi u₁ + phi u₂ = phi (u₁ * swapFun u₂) := by
      rw [phi_mul_of_a_one u₁ (swapFun u₂) h1, phi_swapFun, swapV_swapV]
    rw [hprod]
    exact ⟨u₁ * swapFun u₂, U.mul_mem hu₁ (hbal u₂ hu₂), rfl⟩

/-- The zero vector belongs to the `phi` image of every subgroup. -/
theorem phiSet_zero_mem (U : Subgroup (Wreath n)) : (0 : Vec n) ∈ phiSet U := by
  refine ⟨1, U.one_mem, ?_⟩
  simp

/-- The `phi` image of a subgroup is closed under binary scalar multiplication. -/
theorem phiSet_smul_mem (U : Subgroup (Wreath n)) (c : ZMod 2) {v : Vec n}
    (hv : v ∈ phiSet U) : c • v ∈ phiSet U := by
  rcases zmod2_eq_zero_or_one c with h | h
  · subst h
    simpa using phiSet_zero_mem U
  · subst h
    simpa using hv

/-- The binary subspace whose carrier is the `phi` image of the subgroup `U`. -/
def phiSub (U : Subgroup (Wreath n)) : Submodule (ZMod 2) (Vec n) where
  carrier := phiSet U
  zero_mem' := phiSet_zero_mem U
  add_mem' := phiSet_add_mem U
  smul_mem' := phiSet_smul_mem U

/-- The underlying set of `phiSub U` is `phiSet U`. -/
lemma phiSub_coe (U : Subgroup (Wreath n)) : (phiSub U : Set (Vec n)) = phiSet U := rfl

/-- The vector `phi g` belongs to `phiSub U` exactly when `g` belongs to `U`. -/
theorem mem_phiSub {U : Subgroup (Wreath n)} {g : Wreath n} :
    phi g ∈ phiSub U ↔ g ∈ U := by
  constructor
  · intro h
    obtain ⟨u, hu, heq⟩ := h
    rwa [phi_inj heq] at hu
  · intro h
    exact ⟨g, h, rfl⟩

/-- The set of vectors whose dot product with every vector in `S` is zero. -/
def orthV (S : Set (Vec n)) : Set (Vec n) := {z | ∀ s ∈ S, dot z s = 0}

/-- Membership in `orthV S` means that the dot product with every element of `S` is zero. -/
theorem mem_orthV {S : Set (Vec n)} {z : Vec n} :
    z ∈ orthV S ↔ ∀ s ∈ S, dot z s = 0 := Iff.rfl

/-- The vector orthogonal complement of a set is closed under addition. -/
theorem orthV_add {S : Set (Vec n)} {a b : Vec n}
    (ha : a ∈ orthV S) (hb : b ∈ orthV S) : a + b ∈ orthV S := by
  intro s hs
  rw [dot_add_left, ha s hs, hb s hs, add_zero]

/-- The orthogonal complement of a set closed under `swapV` is also closed under `swapV`. -/
theorem orthV_balanced {S : Set (Vec n)} (hS : ∀ s ∈ S, swapV s ∈ S) :
    ∀ z ∈ orthV S, swapV z ∈ orthV S := by
  intro z hz s hs
  have hswap : swapV s ∈ S := hS s hs
  have h := hz (swapV s) hswap

  have key : dot (swapV z) s = dot z (swapV s) := by
    simp only [dot, swapV]
    ac_rfl
  rw [key]
  exact h

/-- The orthogonal complement of a wreath-product set is the inverse image under `phi` of the
vector orthogonal complement of its image. -/
theorem phi_preimage_orth (S : Set (Wreath n)) :
    perp S = phi ⁻¹' (orthV (phi '' S)) := by
  ext g
  simp only [Set.mem_preimage, mem_orthV, mem_perp]
  constructor
  · intro H s hs
    obtain ⟨u, hu, rfl⟩ := hs
    rw [← phi_mu]
    exact H u hu
  · intro H u hu
    have h := H (phi u) ⟨u, hu, rfl⟩
    rwa [← phi_mu] at h

/-- The `phi` image of a wreath-product orthogonal complement is the vector orthogonal
complement of the image. -/
theorem phi_image_perp (S : Set (Wreath n)) :
    phi '' (perp S) = orthV (phi '' S) := by
  ext z
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [phi_preimage_orth S] at hg
    simpa using hg
  · intro hz
    refine ⟨phiInv z, ?_, phiInv_phi z⟩
    rw [phi_preimage_orth S]
    simpa [phiInv_phi] using hz

/-- For a subspace, `orthV` agrees with the orthogonal subspace defined by `blin`. -/
theorem orthV_eq_orthogonal (W : Submodule (ZMod 2) (Vec n)) :
    orthV (W : Set (Vec n)) = (blin.orthogonal W : Set (Vec n)) := by
  ext z
  constructor
  · intro hz
    show z ∈ blin.orthogonal W
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    show blin w z = 0
    rw [blin_apply, dot_comm]
    exact hz w hw
  · intro hz w hw
    change z ∈ blin.orthogonal W at hz
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hz
    have h := hz w hw
    change blin w z = 0 at h
    rw [blin_apply] at h
    rwa [dot_comm] at h

/-- Taking the vector orthogonal complement twice recovers the underlying set of a subspace. -/
theorem orthV_orthV (W : Submodule (ZMod 2) (Vec n)) :
    orthV (orthV (W : Set (Vec n))) = (W : Set (Vec n)) := by
  rw [orthV_eq_orthogonal]
  rw [show orthV ((blin.orthogonal W : Submodule (ZMod 2) (Vec n)) : Set (Vec n))
      = (blin.orthogonal (blin.orthogonal W) : Set (Vec n)) from orthV_eq_orthogonal _]
  rw [LinearMap.BilinForm.orthogonal_orthogonal blin_nondegenerate blin_isRefl]

/-- Taking `perp` twice recovers the underlying set of a wreath-product subgroup. -/
theorem perpSet_perpSet (U : Subgroup (Wreath n)) :
    perp (perp (U : Set (Wreath n))) = (U : Set (Wreath n)) := by
  rw [phi_preimage_orth, phi_image_perp]
  rw [show phi '' (U : Set (Wreath n)) = (phiSub U : Set (Vec n)) from rfl]
  rw [orthV_orthV]
  ext g
  exact mem_phiSub

/-- The orthogonal complement of `perpSub U` is the underlying set of `U`. -/
theorem perpSub_perpSub (U : Subgroup (Wreath n)) :
    perp (perpSub U) = (U : Set (Wreath n)) :=
  perpSet_perpSet U

/-- Inclusion of wreath-product sets reverses under `perp`. -/
theorem perp_mono {S T : Set (Wreath n)} (h : S ⊆ T) : perp T ⊆ perp S := by
  intro g hg s hs
  exact hg s (h hs)

/-- Inclusion of vector sets reverses under `orthV`. -/
theorem orthV_mono {S T : Set (Vec n)} (h : S ⊆ T) : orthV T ⊆ orthV S := by
  intro z hz s hs
  exact hz s (h hs)

end Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Orthogonal
