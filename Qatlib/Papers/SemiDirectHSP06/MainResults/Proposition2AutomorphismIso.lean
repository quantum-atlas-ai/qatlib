/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemiDirectHSP06.MainResults.Proposition1UnitOrder
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.OrderOfElement
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP06.MainResults

open SemidirectProduct

variable {p r : ℕ}

lemma mulAutOfUnit_mul (n : ℕ) (u v : (ZMod n)ˣ) :
    mulAutOfUnit n u * mulAutOfUnit n v = mulAutOfUnit n (u * v) := by
  ext x
  simp [mulAutOfUnit_apply, mul_assoc]

lemma shiftAut_pow (hp : p.Prime) (hr : 2 ≤ r) (k : ℕ) :
    shiftAut p r hp hr ^ k =
      mulAutOfUnit (2 * p ^ r) (shiftUnit p r hp hr ^ k) := by
  induction k with
  | zero =>
      ext x
      simp [mulAutOfUnit_apply]
  | succ k ih =>
      rw [pow_succ, ih, shiftAut, mulAutOfUnit_mul, ← pow_succ]

lemma shiftAut_ne_one (hp : p.Prime) (hr : 2 ≤ r) :
    shiftAut p r hp hr ≠ 1 := by
  intro h
  have h1 : mulAutOfUnit (2 * p ^ r) (shiftUnit p r hp hr) = 1 := h
  have h2 := congrArg
    (fun f : MulAut (Multiplicative (ZMod (2 * p ^ r))) =>
      f (Multiplicative.ofAdd (1 : ZMod (2 * p ^ r)))) h1
  simp only [mulAutOfUnit_apply, toAdd_ofAdd, mul_one, MulAut.one_apply] at h2
  have h3 : ((shiftUnit p r hp hr : (ZMod (2 * p ^ r))ˣ) : ZMod (2 * p ^ r)) = 1 := by
    have := Multiplicative.ofAdd.injective h2
    simpa using this
  exact shiftUnit_ne_one hp hr (Units.ext h3)

theorem orderOf_shiftAut_eq_p (hp : p.Prime) (hr : 2 ≤ r) :
    orderOf (shiftAut p r hp hr) = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  apply orderOf_eq_prime
  · rw [shiftAut_pow, shiftUnit_pow_eq_one hp hr]
    ext x
    simp [mulAutOfUnit_apply]
  · exact shiftAut_ne_one hp hr

lemma zpowers_pow_eq_zpowers {G : Type*} [Group G] (g : G) {k : ℕ}
    (hk : Nat.Coprime k (orderOf g)) :
    Subgroup.zpowers (g ^ k) = Subgroup.zpowers g := by
  apply le_antisymm
  · rw [Subgroup.zpowers_le]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers g) k
  · rw [Subgroup.zpowers_le]
    exact mem_zpowers_pow_iff.mpr hk

theorem sdp_iso_of_injective_same_range {N P : Type*} [Group N] [Group P]
    {φ ψ : P →* MulAut N}
    (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hrange : φ.range = ψ.range) :
    Nonempty (SemidirectProduct N P φ ≃* SemidirectProduct N P ψ) := by
  let eφ := MonoidHom.ofInjective hφ
  let eψ := MonoidHom.ofInjective hψ
  let r : φ.range ≃* ψ.range := MulEquiv.subgroupCongr hrange
  let α : P ≃* P := eφ.trans (r.trans eψ.symm)
  have hα : ∀ g : P, ψ (α g) = φ g := by
    intro g
    have h1 : (eψ (α g) : MulAut N) = (eφ g : MulAut N) := by
      have h2 : eψ (α g) = r (eφ g) := by
        simp [α, eψ]
      rw [h2]
      exact MulEquiv.subgroupCongr_apply hrange (eφ g)
    rw [← MonoidHom.ofInjective_apply hψ, h1, MonoidHom.ofInjective_apply hφ]
  refine ⟨SemidirectProduct.congr (MulEquiv.refl N) α ?_⟩
  intro g
  simpa using! (hα g).symm

lemma orderOf_ofAdd_one_eq_p (hp : p.Prime) :
    orderOf (Multiplicative.ofAdd (1 : ZMod p)) = p := by
  simpa using orderOf_ofAdd_eq_p (p := p) (b := 1) hp (by norm_num)
    (by have := hp.two_le; omega)

lemma zpowers_ofAdd_one_eq_top (hp : p.Prime) :
    Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod p)) = ⊤ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Finite (Multiplicative (ZMod p)) := inferInstance
  apply Subgroup.eq_top_of_card_eq
  rw [Nat.card_zpowers, orderOf_ofAdd_one_eq_p hp,
    Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

lemma injective_of_gen_image (hp : p.Prime) (hr : 2 ≤ r)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r))))
    {i : ℕ} (hi : 1 ≤ i) (hip : i ≤ p - 1)
    (hφ : φ (Multiplicative.ofAdd 1) = shiftAut p r hp hr ^ i) :
    Function.Injective φ := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro g1 g2 hg
  set d := g1 * g2⁻¹ with hd_def
  set n := d.toAdd.val with hn_def
  have hgen : orderOf (Multiplicative.ofAdd (1 : ZMod p)) = p := orderOf_ofAdd_one_eq_p hp
  have hcop : Nat.Coprime (orderOf (shiftAut p r hp hr)) i := by
    rw [orderOf_shiftAut_eq_p hp hr]
    exact (hp.coprime_iff_not_dvd).mpr (fun hd => by
      have := Nat.le_of_dvd hi hd; omega)
  have hAi : orderOf (shiftAut p r hp hr ^ i) = p := by
    rw [Nat.Coprime.orderOf_pow hcop, orderOf_shiftAut_eq_p hp hr]
  have hd : φ d = 1 := by
    rw [hd_def, map_mul, hg, map_inv, mul_inv_cancel]
  have hd_eq : d = (Multiplicative.ofAdd (1 : ZMod p)) ^ n := by
    rw [hn_def, ofAdd_one_pow]
    exact (congrArg Multiplicative.ofAdd (ZMod.natCast_zmod_val d.toAdd)).symm
  have hpow : (φ (Multiplicative.ofAdd (1 : ZMod p))) ^ n = 1 := by
    rw [← map_pow, ← hd_eq, hd]
  rw [hφ] at hpow
  have hdvd : p ∣ n := by
    have := (orderOf_dvd_iff_pow_eq_one (x := shiftAut p r hp hr ^ i) (n := n)).mpr hpow
    rwa [hAi] at this
  have hgz : (Multiplicative.ofAdd (1 : ZMod p)) ^ n = 1 := by
    apply (orderOf_dvd_iff_pow_eq_one (x := Multiplicative.ofAdd (1 : ZMod p)) (n := n)).mp
    rwa [hgen]
  have hd1 : d = 1 := by rw [hd_eq, hgz]
  rw [hd_def] at hd1
  exact mul_inv_eq_one.mp hd1

lemma range_eq_zpowers_gen (hp : p.Prime) (hr : 2 ≤ r)
    (φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod (2 * p ^ r))))
    {i : ℕ} (hφ : φ (Multiplicative.ofAdd 1) = shiftAut p r hp hr ^ i) :
    φ.range = Subgroup.zpowers (shiftAut p r hp hr ^ i) := by
  rw [MonoidHom.range_eq_map, ← zpowers_ofAdd_one_eq_top hp, MonoidHom.map_zpowers, hφ]

theorem proposition2_automorphism_iso
    {p r : ℕ} (hp : p.Prime) (hr : 2 ≤ r)
    (φ ψ : Multiplicative (ZMod p) →*
      MulAut (Multiplicative (ZMod (2 * p ^ r))))
    {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (hip : i ≤ p - 1) (hjp : j ≤ p - 1)
    (hφ : φ (Multiplicative.ofAdd 1) = shiftAut p r hp hr ^ i)
    (hψ : ψ (Multiplicative.ofAdd 1) = shiftAut p r hp hr ^ j) :
    Nonempty (SDP p r φ ≃* SDP p r ψ) := by
  apply sdp_iso_of_injective_same_range
  · exact injective_of_gen_image hp hr φ hi hip hφ
  · exact injective_of_gen_image hp hr ψ hj hjp hψ
  · rw [range_eq_zpowers_gen hp hr φ hφ, range_eq_zpowers_gen hp hr ψ hψ]
    have ci : Nat.Coprime i (orderOf (shiftAut p r hp hr)) := by
      rw [orderOf_shiftAut_eq_p hp hr]
      exact ((hp.coprime_iff_not_dvd).mpr (fun hd => by
        have := Nat.le_of_dvd hi hd; omega)).symm
    have cj : Nat.Coprime j (orderOf (shiftAut p r hp hr)) := by
      rw [orderOf_shiftAut_eq_p hp hr]
      exact ((hp.coprime_iff_not_dvd).mpr (fun hd => by
        have := Nat.le_of_dvd hj hd; omega)).symm
    rw [zpowers_pow_eq_zpowers (shiftAut p r hp hr) ci,
      zpowers_pow_eq_zpowers (shiftAut p r hp hr) cj]

end Qatlib.Papers.SemiDirectHSP06.MainResults
