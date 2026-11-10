/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExtraSpecHSP07.MainResults.Defs
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.ExtraSpecHSP07.MainResults

structure WeylData (G : Type*) [Group G] (p : ℕ) where

  prime : p.Prime

  odd : p ≠ 2

  z : G

  z_order : orderOf z = p

  comm_eq : commutator G = Subgroup.zpowers z

  z_central : z ∈ Subgroup.center G

  exponent : ∀ g : G, g ^ p = 1

  phi : (ZMod p)ˣ →* MulAut G

  phi_mod : ∀ (j : (ZMod p)ˣ) (g : G),
    phi j g * (g ^ (j : ZMod p).val)⁻¹ ∈ commutator G

  phi_z : ∀ j : (ZMod p)ˣ, phi j z = z ^ (((j : ZMod p) ^ 2).val)

namespace WeylData

variable {G : Type*} [Group G] {p : ℕ} (W : WeylData G p)

theorem z_pow : W.z ^ p = 1 := by
  have h := pow_orderOf_eq_one W.z
  rwa [W.z_order] at h

theorem commute_z (g : G) : Commute W.z g :=
  (Subgroup.mem_center_iff.mp W.z_central g).symm

theorem z_pow_congr {A B : ℕ} (h : (A : ZMod p) = (B : ZMod p)) :
    W.z ^ A = W.z ^ B :=
  pow_eq_pow_of_modEq ((ZMod.natCast_eq_natCast_iff A B p).mp h) W.z_pow

theorem zpow_eq_pow_val (k : ℤ) : W.z ^ k = W.z ^ ((k : ZMod p).val) := by
  haveI : NeZero p := ⟨W.prime.ne_zero⟩
  have hpos : (0 : ℤ) < (p : ℤ) := by exact_mod_cast W.prime.pos
  have hnonneg : 0 ≤ k % (p : ℤ) := Int.emod_nonneg k (ne_of_gt hpos)
  have h1 : W.z ^ k = W.z ^ ((k % (p : ℤ)).toNat) := by
    conv_lhs =>
      rw [← zpow_mod_orderOf, W.z_order,
        ← Int.toNat_of_nonneg hnonneg, zpow_natCast]
  rw [h1]
  refine W.z_pow_congr ?_
  have hcast : (((k % (p : ℤ)).toNat : ℕ) : ZMod p) = (k : ZMod p) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnonneg,
      ZMod.intCast_eq_intCast_iff]
    exact Int.mod_modEq k (p : ℤ)
  rw [hcast, ZMod.natCast_zmod_val]

theorem exists_zpow_decomp (h : G) (j : (ZMod p)ˣ) :
    ∃ s : ZMod p, W.phi j h = h ^ (j : ZMod p).val * W.z ^ s.val := by
  classical
  have hm : W.phi j h * (h ^ (j : ZMod p).val)⁻¹ ∈ Subgroup.zpowers W.z := by
    rw [← W.comm_eq]
    exact W.phi_mod j h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hm
  refine ⟨(k : ZMod p), ?_⟩
  rw [W.zpow_eq_pow_val k] at hk
  have hcomm : Commute (W.z ^ ((k : ZMod p).val)) (h ^ (j : ZMod p).val) :=
    ((W.commute_z h).pow_left _).pow_right _
  calc W.phi j h = (W.phi j h * (h ^ (j : ZMod p).val)⁻¹) *
        (h ^ (j : ZMod p).val) := by group
    _ = W.z ^ ((k : ZMod p).val) * (h ^ (j : ZMod p).val) := by rw [← hk]
    _ = h ^ (j : ZMod p).val * W.z ^ ((k : ZMod p).val) := hcomm.eq

theorem sub_sq_ne_zero (W : WeylData G p) {j : (ZMod p)ˣ} (hj : (j : ZMod p) ≠ 1) :
    (j : ZMod p) - (j : ZMod p) ^ 2 ≠ 0 := by
  haveI : Fact p.Prime := ⟨W.prime⟩
  intro h
  have h2 : (j : ZMod p) * (1 - (j : ZMod p)) = 0 := by
    have h' : (j : ZMod p) = (j : ZMod p) ^ 2 := sub_eq_zero.mp h
    rw [mul_sub, mul_one, sub_eq_zero]
    simpa [pow_two] using h'
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact Units.ne_zero j h3
  · exact hj (sub_eq_zero.mp h3).symm

theorem phi_eq_pow_mul_zpow (h : G) :
    ∃ ℓ : ZMod p, ∀ j : (ZMod p)ˣ,
      W.phi j h =
        h ^ (j : ZMod p).val * W.z ^ (((j : ZMod p) - (j : ZMod p) ^ 2) * ℓ).val := by
  classical
  haveI : Fact p.Prime := ⟨W.prime⟩
  haveI : NeZero p := ⟨W.prime.ne_zero⟩
  haveI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime W.prime
  obtain ⟨j₀, hj₀⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hcard : Fintype.card (ZMod p)ˣ = p - 1 := ZMod.card_units p
  have hord : orderOf j₀ = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hj₀, Nat.card_eq_fintype_card, hcard]
  have hp3 : 3 ≤ p := by
    rcases Nat.lt_or_eq_of_le W.prime.two_le with hlt | heq
    · omega
    · exact absurd heq.symm W.odd
  have hj₀ne : (j₀ : ZMod p) ≠ 1 := by
    intro h1
    have hunit : j₀ = 1 := Units.ext h1
    rw [hunit, orderOf_one] at hord
    omega
  have hden : (j₀ : ZMod p) - (j₀ : ZMod p) ^ 2 ≠ 0 :=
    sub_sq_ne_zero W hj₀ne
  obtain ⟨s, hs⟩ := W.exists_zpow_decomp h j₀
  refine ⟨s * ((j₀ : ZMod p) - (j₀ : ZMod p) ^ 2)⁻¹, ?_⟩
  set ℓ : ZMod p := s * ((j₀ : ZMod p) - (j₀ : ZMod p) ^ 2)⁻¹ with hℓ
  set k : G := h * W.z ^ ℓ.val with hk
  have hs_eq : ((j₀ : ZMod p) - (j₀ : ZMod p) ^ 2) * ℓ = s := by
    rw [hℓ, ← mul_assoc, mul_comm ((j₀ : ZMod p) - (j₀ : ZMod p) ^ 2) s,
      mul_assoc, mul_inv_cancel₀ hden, mul_one]
  have hk0 : W.phi j₀ k = k ^ (j₀ : ZMod p).val := by
    have hcommk : Commute h (W.z ^ ℓ.val) := (W.commute_z h).symm.pow_right _
    have hphiz : W.phi j₀ (W.z ^ ℓ.val) =
        W.z ^ (((j₀ : ZMod p) ^ 2).val * ℓ.val) := by
      rw [map_pow, W.phi_z, pow_mul]
    have hzcombine : W.z ^ s.val * W.z ^ (((j₀ : ZMod p) ^ 2).val * ℓ.val) =
        W.z ^ (ℓ.val * (j₀ : ZMod p).val) := by
      rw [← pow_add]
      refine W.z_pow_congr ?_
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
        ZMod.natCast_zmod_val, ← hs_eq]
      ring
    calc W.phi j₀ k = W.phi j₀ h * W.phi j₀ (W.z ^ ℓ.val) := by rw [hk, map_mul]
      _ = (h ^ (j₀ : ZMod p).val * W.z ^ s.val) *
            W.z ^ (((j₀ : ZMod p) ^ 2).val * ℓ.val) := by rw [hs, hphiz]
      _ = h ^ (j₀ : ZMod p).val *
            (W.z ^ s.val * W.z ^ (((j₀ : ZMod p) ^ 2).val * ℓ.val)) := by rw [mul_assoc]
      _ = h ^ (j₀ : ZMod p).val * W.z ^ (ℓ.val * (j₀ : ZMod p).val) := by rw [hzcombine]
      _ = (h * W.z ^ ℓ.val) ^ (j₀ : ZMod p).val := by rw [hcommk.mul_pow, pow_mul]
  have hunit_pow : ∀ j : (ZMod p)ˣ, ∃ m : ℕ, j₀ ^ m = j := by
    intro j
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hj₀ j)
    have hpos : (0 : ℤ) < (orderOf j₀ : ℤ) := by
      rw [hord]; omega
    refine ⟨(n % (orderOf j₀ : ℤ)).toNat, ?_⟩
    conv_rhs =>
      rw [← hn, ← zpow_mod_orderOf,
        ← Int.toNat_of_nonneg (Int.emod_nonneg n (ne_of_gt hpos)), zpow_natCast]
  have hpow : ∀ (j : (ZMod p)ˣ), W.phi j k = k ^ (j : ZMod p).val := by
    intro j
    obtain ⟨m, hm⟩ := hunit_pow j
    rw [← hm, map_pow]
    have aut : ∀ m : ℕ, ((W.phi j₀) ^ m) k = k ^ (((j₀ : ZMod p).val) ^ m) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          rw [pow_succ, MulAut.mul_apply, hk0, map_pow, ih, ← pow_mul, pow_succ]
    rw [aut]
    refine pow_eq_pow_of_modEq ?_ (W.exponent k)
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val, ← Units.val_pow_eq_pow_val, hm,
      ZMod.natCast_zmod_val]
  intro j
  have hsplit : W.phi j h = W.phi j k * (W.phi j (W.z ^ ℓ.val))⁻¹ := by
    rw [hk, map_mul, mul_inv_cancel_right]
  have hzrel : W.z ^ (ℓ.val * (j : ZMod p).val) =
      W.z ^ (((j : ZMod p) - (j : ZMod p) ^ 2) * ℓ).val *
        W.z ^ (((j : ZMod p) ^ 2).val * ℓ.val) := by
    rw [← pow_add]
    refine W.z_pow_congr ?_
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val]
    ring
  have hcommf : Commute h (W.z ^ ℓ.val) := (W.commute_z h).symm.pow_right _
  rw [hsplit, hpow, map_pow, W.phi_z, hk, hcommf.mul_pow, ← pow_mul, ← pow_mul,
    mul_assoc, hzrel]
  group

end WeylData

end Qatlib.Papers.ExtraSpecHSP07.MainResults
