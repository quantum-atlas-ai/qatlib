/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Qatlib.Papers.NonabelianHSP98.MainResults.Pairing
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Orthogonal

open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup
open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup.Wreath
open Qatlib.Papers.NonabelianHSP98.MainResults.Pairing
open Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel
open Finset

variable {n : ℕ}

@[simp] lemma phi_of_a_one_eq {g : Wreath n} (h : g.a = 1) :
    phi g = (g.y, g.x, 1) := phi_of_a_one (by simp [h])

macro "zring" : tactic => `(tactic| (ring_nf <;> reduce_mod_char))

def swapV (v : Vec n) : Vec n := (v.2.1, v.1, v.2.2)

@[simp] lemma swapV_swapV (v : Vec n) : swapV (swapV v) = v := rfl

@[simp] lemma phi_swapFun (g : Wreath n) : phi (swapFun g) = swapV (phi g) := by
  rcases zmod2_eq_zero_or_one g.a with h | h
  · have h' : (swapFun g).a = 0 := by simp [h]
    rw [phi_of_a_zero h, phi_of_a_zero h']
    rfl
  · have h' : (swapFun g).a ≠ 0 := by simp [h]
    rw [phi_of_a_one_eq h, phi_of_a_one h']
    rfl

@[simp] lemma phi_t : phi (t n) = ((0 : Fin n → ZMod 2), (0 : Fin n → ZMod 2), (1 : ZMod 2)) := by
  have h : (t n).a ≠ 0 := by simp
  rw [phi_of_a_one h]
  simp [t]

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

theorem mu_comm (g h : Wreath n) : mu g h = mu h g := by
  rw [phi_mu, phi_mu, dot_comm]

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

theorem phi_mul (g h : Wreath n) :
    phi (g * h) = phi g + (if g.a = 0 then phi h else swapV (phi h)) := by
  rcases zmod2_eq_zero_or_one g.a with hg | hg
  · rw [if_pos hg, phi_mul_of_a_zero g h hg]
  · rw [if_neg (by simp [hg]), phi_mul_of_a_one g h hg]

theorem phi_mul_t (g : Wreath n) : phi (g * t n) = phi g + phi (t n) := by
  rcases zmod2_eq_zero_or_one g.a with hg | hg
  · exact phi_mul_of_a_zero g (t n) hg
  · simpa using! phi_mul_of_a_one g (t n) hg

theorem phi_mul_t' (g : Wreath n) :
    phi (g * t n) = phi g + ((0 : Fin n → ZMod 2), (0 : Fin n → ZMod 2), (1 : ZMod 2)) := by
  rw [phi_mul_t, phi_t]

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

theorem mu_swap (g h : Wreath n) : mu (swapFun g) (swapFun h) = mu g h :=
  mu_swapFun_swapFun g h

theorem dot_add_right (u v w : Vec n) : dot u (v + w) = dot u v + dot u w := by
  simp only [dot, Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]
  abel

theorem dot_add_left (u v w : Vec n) : dot (u + v) w = dot u w + dot v w := by
  simp only [dot, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]
  abel

def phiSet (U : Subgroup (Wreath n)) : Set (Vec n) := phi '' (U : Set (Wreath n))

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

theorem phiSet_zero_mem (U : Subgroup (Wreath n)) : (0 : Vec n) ∈ phiSet U := by
  refine ⟨1, U.one_mem, ?_⟩
  simp

theorem phiSet_smul_mem (U : Subgroup (Wreath n)) (c : ZMod 2) {v : Vec n}
    (hv : v ∈ phiSet U) : c • v ∈ phiSet U := by
  rcases zmod2_eq_zero_or_one c with h | h
  · subst h
    simpa using phiSet_zero_mem U
  · subst h
    simpa using hv

def phiSub (U : Subgroup (Wreath n)) : Submodule (ZMod 2) (Vec n) where
  carrier := phiSet U
  zero_mem' := phiSet_zero_mem U
  add_mem' := phiSet_add_mem U
  smul_mem' := phiSet_smul_mem U

lemma phiSub_coe (U : Subgroup (Wreath n)) : (phiSub U : Set (Vec n)) = phiSet U := rfl

theorem mem_phiSub {U : Subgroup (Wreath n)} {g : Wreath n} :
    phi g ∈ phiSub U ↔ g ∈ U := by
  constructor
  · intro h
    obtain ⟨u, hu, heq⟩ := h
    rwa [phi_inj heq] at hu
  · intro h
    exact ⟨g, h, rfl⟩

def orthV (S : Set (Vec n)) : Set (Vec n) := {z | ∀ s ∈ S, dot z s = 0}

theorem mem_orthV {S : Set (Vec n)} {z : Vec n} :
    z ∈ orthV S ↔ ∀ s ∈ S, dot z s = 0 := Iff.rfl

theorem orthV_add {S : Set (Vec n)} {a b : Vec n}
    (ha : a ∈ orthV S) (hb : b ∈ orthV S) : a + b ∈ orthV S := by
  intro s hs
  rw [dot_add_left, ha s hs, hb s hs, add_zero]

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

theorem orthV_orthV (W : Submodule (ZMod 2) (Vec n)) :
    orthV (orthV (W : Set (Vec n))) = (W : Set (Vec n)) := by
  rw [orthV_eq_orthogonal]
  rw [show orthV ((blin.orthogonal W : Submodule (ZMod 2) (Vec n)) : Set (Vec n))
      = (blin.orthogonal (blin.orthogonal W) : Set (Vec n)) from orthV_eq_orthogonal _]
  rw [LinearMap.BilinForm.orthogonal_orthogonal blin_nondegenerate blin_isRefl]

theorem perpSet_perpSet (U : Subgroup (Wreath n)) :
    perp (perp (U : Set (Wreath n))) = (U : Set (Wreath n)) := by
  rw [phi_preimage_orth, phi_image_perp]
  rw [show phi '' (U : Set (Wreath n)) = (phiSub U : Set (Vec n)) from rfl]
  rw [orthV_orthV]
  ext g
  exact mem_phiSub

theorem perpSub_perpSub (U : Subgroup (Wreath n)) :
    perp (perpSub U) = (U : Set (Wreath n)) :=
  perpSet_perpSet U

theorem perp_mono {S T : Set (Wreath n)} (h : S ⊆ T) : perp T ⊆ perp S := by
  intro g hg s hs
  exact hg s (h hs)

theorem orthV_mono {S T : Set (Vec n)} (h : S ⊆ T) : orthV T ⊆ orthV S := by
  intro z hz s hs
  exact hz s (h hs)

end Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel.Orthogonal
