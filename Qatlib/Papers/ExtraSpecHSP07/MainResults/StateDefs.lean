/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExtraSpecHSP07.MainResults.Defs
import Qatlib.Papers.ExtraSpecHSP07.MainResults.WeylDefs
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
set_option warningAsError false

set_option autoImplicit false

open scoped Classical
open scoped BigOperators
open scoped commutatorElement

namespace Qatlib.Papers.ExtraSpecHSP07.MainResults

structure SheetData (G : Type*) [Group G] (p : ℕ) where

  prime : p.Prime

  H : Subgroup G

  z : G

  z_order : orderOf z = p

  z_central : z ∈ Subgroup.center G

  H_inter : H ⊓ Subgroup.zpowers z = ⊥

  comm_le_z : commutator G ≤ Subgroup.zpowers z

def SheetData.ofWeyl {G : Type*} [Group G] {p : ℕ} (W : WeylData G p)
    (H : Subgroup G) (hInter : H ⊓ Subgroup.zpowers W.z = ⊥) : SheetData G p where
  prime := W.prime
  H := H
  z := W.z
  z_order := W.z_order
  z_central := W.z_central
  H_inter := hInter
  comm_le_z := le_of_eq W.comm_eq

namespace SheetData

variable {G : Type*} [Group G] {p : ℕ} (S : SheetData G p)

theorem z_pow : S.z ^ p = 1 := by
  have h := pow_orderOf_eq_one S.z
  rwa [S.z_order] at h

theorem commute_z (g : G) : Commute S.z g :=
  (Subgroup.mem_center_iff.mp S.z_central g).symm

theorem z_pow_congr {A B : ℕ} (h : (A : ZMod p) = (B : ZMod p)) :
    S.z ^ A = S.z ^ B :=
  pow_eq_pow_of_modEq ((ZMod.natCast_eq_natCast_iff A B p).mp h) S.z_pow

theorem zpow_eq_pow_val (k : ℤ) : S.z ^ k = S.z ^ ((k : ZMod p).val) := by
  haveI : NeZero p := ⟨S.prime.ne_zero⟩
  have hpos : (0 : ℤ) < (p : ℤ) := by
    have : 0 < p := S.prime.pos
    exact_mod_cast this
  have hnonneg : 0 ≤ k % (p : ℤ) := Int.emod_nonneg k (ne_of_gt hpos)
  have h1 : S.z ^ k = S.z ^ ((k % (p : ℤ)).toNat) := by
    conv_lhs =>
      rw [← zpow_mod_orderOf, S.z_order,
        ← Int.toNat_of_nonneg hnonneg, zpow_natCast]
  rw [h1]
  refine S.z_pow_congr ?_
  have hcast : (((k % (p : ℤ)).toNat : ℕ) : ZMod p) = (k : ZMod p) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnonneg,
      ZMod.intCast_eq_intCast_iff]
    exact Int.mod_modEq k (p : ℤ)
  rw [hcast, ZMod.natCast_zmod_val]

theorem mul_zpow_decomp (h₁ h₂ : G) (k₁ k₂ : ℤ) :
    (h₁ * S.z ^ k₁) * (h₂ * S.z ^ k₂) = (h₁ * h₂) * S.z ^ (k₁ + k₂) := by
  have hc : Commute (S.z ^ k₁) h₂ := (S.commute_z h₂).zpow_left k₁
  calc (h₁ * S.z ^ k₁) * (h₂ * S.z ^ k₂)
      = h₁ * (S.z ^ k₁ * (h₂ * S.z ^ k₂)) := by simp only [mul_assoc]
    _ = h₁ * (h₂ * (S.z ^ k₁ * S.z ^ k₂)) := by
      have hstep : S.z ^ k₁ * (h₂ * S.z ^ k₂) = h₂ * (S.z ^ k₁ * S.z ^ k₂) := by
        rw [← mul_assoc]
        rw [hc.eq]
        rw [mul_assoc]
      rw [hstep]
    _ = h₁ * (h₂ * S.z ^ (k₁ + k₂)) := by rw [← zpow_add]
    _ = (h₁ * h₂) * S.z ^ (k₁ + k₂) := by simp only [mul_assoc]

theorem inv_mul_zpow (x : G) (k : ℤ) : (x * S.z ^ k)⁻¹ = x⁻¹ * S.z ^ (-k) := by
  rw [mul_inv_rev, ← zpow_neg]
  exact (((S.commute_z x).zpow_left (-k)).inv_right).eq

def HZ : Subgroup G where
  carrier := {x | ∃ h : G, h ∈ S.H ∧ ∃ k : ℤ, x = h * S.z ^ k}
  one_mem' := ⟨1, S.H.one_mem, 0, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hha, ka, rfl⟩ ⟨hb, hhb, kb, rfl⟩
    exact ⟨ha * hb, S.H.mul_mem hha hhb, ka + kb, S.mul_zpow_decomp ha hb ka kb⟩
  inv_mem' := by
    rintro a ⟨ha, hha, ka, rfl⟩
    exact ⟨ha⁻¹, S.H.inv_mem hha, -ka, S.inv_mul_zpow ha ka⟩

theorem mem_HZ_iff {x : G} :
    x ∈ S.HZ ↔ ∃ h : G, h ∈ S.H ∧ ∃ k : ℤ, x = h * S.z ^ k :=
  Iff.rfl

theorem H_le_HZ : S.H ≤ S.HZ := fun x hx => ⟨x, hx, 0, by simp⟩

theorem zpowers_le_HZ : Subgroup.zpowers S.z ≤ S.HZ := by
  intro x hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact ⟨1, S.H.one_mem, k, by simp⟩

theorem z_mem_HZ : S.z ∈ S.HZ :=
  S.zpowers_le_HZ (Subgroup.mem_zpowers S.z)

theorem comm_le : commutator G ≤ S.HZ :=
  fun _ hx => S.zpowers_le_HZ (S.comm_le_z hx)

def leftCoset (a : G) : Set G := {x | a⁻¹ * x ∈ S.H}

theorem mem_leftCoset {a x : G} : x ∈ S.leftCoset a ↔ a⁻¹ * x ∈ S.H :=
  Iff.rfl

def leftCosetN (a : G) : Set G := {x | a⁻¹ * x ∈ S.HZ}

theorem mem_leftCosetN {a x : G} : x ∈ S.leftCosetN a ↔ a⁻¹ * x ∈ S.HZ :=
  Iff.rfl

theorem leftCosetN_mul_iff {a x s : G} (hs : s ∈ S.HZ) :
    x ∈ S.leftCosetN (a * s) ↔ x ∈ S.leftCosetN a := by
  rw [mem_leftCosetN, mem_leftCosetN, mul_inv_rev]
  constructor
  · intro h
    have hm : s * (s⁻¹ * a⁻¹ * x) ∈ S.HZ := S.HZ.mul_mem hs h
    have he : s * (s⁻¹ * a⁻¹ * x) = a⁻¹ * x := by group
    rwa [he] at hm
  · intro h
    have hm : s⁻¹ * (a⁻¹ * x) ∈ S.HZ := S.HZ.mul_mem (S.HZ.inv_mem hs) h
    have he : s⁻¹ * (a⁻¹ * x) = s⁻¹ * a⁻¹ * x := by group
    rwa [he] at hm

theorem exists_sheet {a x : G} (hx : x ∈ S.leftCosetN a) :
    ∃ i : ZMod p, a⁻¹ * (x * S.z ^ (-((i.val : ℕ) : ℤ))) ∈ S.H := by
  haveI : NeZero p := ⟨S.prime.ne_zero⟩
  obtain ⟨h, hh, k, hk⟩ := hx
  refine ⟨(k : ZMod p), ?_⟩
  have hz : S.z ^ (k - (((k : ZMod p).val : ℕ) : ℤ)) = 1 := by
    rw [zpow_sub, S.zpow_eq_pow_val k, S.zpow_eq_pow_val (((k : ZMod p).val : ℕ) : ℤ)]
    push_cast
    simp
  have he : a⁻¹ * (x * S.z ^ (-(((k : ZMod p).val : ℕ) : ℤ))) = h := by
    calc a⁻¹ * (x * S.z ^ (-(((k : ZMod p).val : ℕ) : ℤ)))
        = (a⁻¹ * x) * S.z ^ (-(((k : ZMod p).val : ℕ) : ℤ)) := by group
      _ = (h * S.z ^ k) * S.z ^ (-(((k : ZMod p).val : ℕ) : ℤ)) := by rw [hk]
      _ = h * (S.z ^ k * S.z ^ (-(((k : ZMod p).val : ℕ) : ℤ))) := by rw [mul_assoc]
      _ = h * S.z ^ (k - (((k : ZMod p).val : ℕ) : ℤ)) := by rw [← zpow_add, sub_eq_add_neg]
      _ = h * 1 := by rw [hz]
      _ = h := by simp
  rw [he]
  exact hh

theorem exists_ez {x : G} (hx : x ∈ S.HZ) :
    ∃ k : ZMod p, ∃ h : G, h ∈ S.H ∧ x = h * S.z ^ (((k.val : ℕ) : ℤ)) := by
  obtain ⟨h, hh, k, hk⟩ := hx
  refine ⟨(k : ZMod p), h, hh, ?_⟩
  rw [hk, S.zpow_eq_pow_val]
  simp [zpow_natCast]

noncomputable def ezOf (x : G) : ZMod p := by
  classical
  exact if h : x ∈ S.HZ then Classical.choose (S.exists_ez h) else 0

theorem ezOf_spec {x : G} (hx : x ∈ S.HZ) :
    ∃ h : G, h ∈ S.H ∧ x = h * S.z ^ (((S.ezOf x).val : ℕ) : ℤ) := by
  unfold ezOf
  rw [dif_pos hx]
  exact Classical.choose_spec (S.exists_ez hx)

theorem ezOf_eq_of_decomp {x h : G} (hh : h ∈ S.H) {k : ℤ}
    (hx : x = h * S.z ^ k) : S.ezOf x = (k : ZMod p) := by
  haveI : NeZero p := ⟨S.prime.ne_zero⟩
  have hxN : x ∈ S.HZ := ⟨h, hh, k, hx⟩
  obtain ⟨h', hh', hx'⟩ := S.ezOf_spec hxN

  have hmem : S.z ^ ((((S.ezOf x).val : ℕ) : ℤ) - k) ∈ S.H := by
    have heq : h' * S.z ^ (((S.ezOf x).val : ℕ) : ℤ) = h * S.z ^ k := by
      rw [← hx', hx]
    have h1 : h'⁻¹ * h = S.z ^ ((((S.ezOf x).val : ℕ) : ℤ) - k) := by
      have hA : S.z ^ (((S.ezOf x).val : ℕ) : ℤ) = (h'⁻¹ * h) * S.z ^ k := by
        have h2 : h'⁻¹ * (h' * S.z ^ (((S.ezOf x).val : ℕ) : ℤ)) =
            h'⁻¹ * (h * S.z ^ k) := by rw [heq]
        simpa only [inv_mul_cancel_left, mul_assoc] using h2
      have hB : h'⁻¹ * h = S.z ^ ((((S.ezOf x).val : ℕ) : ℤ) + -k) := by
        have h2 : (h'⁻¹ * h) * S.z ^ k = S.z ^ (((S.ezOf x).val : ℕ) : ℤ) := hA.symm
        have h3 := congrArg (fun t => t * S.z ^ (-k)) h2
        simpa only [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one] using h3
      rw [hB]
      congr 1
    rw [← h1]
    exact S.H.mul_mem (S.H.inv_mem hh') hh
  have hbot : S.z ^ ((((S.ezOf x).val : ℕ) : ℤ) - k) ∈ (⊥ : Subgroup G) := by
    rw [← S.H_inter]
    exact Subgroup.mem_inf.mpr ⟨hmem, Subgroup.mem_zpowers_iff.mpr ⟨_, rfl⟩⟩
  have hz1 : S.z ^ ((((S.ezOf x).val : ℕ) : ℤ) - k) = 1 :=
    Subgroup.mem_bot.mp hbot
  have hmod : ((((S.ezOf x).val : ℕ) : ℤ) - k) ≡ 0 [ZMOD (p : ℤ)] := by
    have h := (zpow_eq_one_iff_modEq (x := S.z)).mp hz1
    rwa [S.z_order] at h
  have hdvd : (p : ℤ) ∣ k - (((S.ezOf x).val : ℕ) : ℤ) := by
    have h := Int.modEq_iff_dvd.mp hmod
    rwa [zero_sub, neg_sub] at h
  have hcast : ((((S.ezOf x).val : ℕ) : ℤ) : ZMod p) = ((k : ℤ) : ZMod p) := by
    rw [ZMod.intCast_eq_intCast_iff]
    exact Int.modEq_iff_dvd.mpr hdvd
  rw [← hcast]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem phi_maps_HZ {W : WeylData G p} (hz : S.z = W.z) (j : (ZMod p)ˣ)
    {y : G} (hy : y ∈ S.HZ) : W.phi j y ∈ S.HZ := by
  obtain ⟨h, hh, k, rfl⟩ := hy
  have hle : commutator G ≤ S.HZ := S.comm_le
  have h1 : W.phi j h ∈ S.HZ := by
    have hc := W.phi_mod j h
    have hm : (W.phi j h * (h ^ (j : ZMod p).val)⁻¹) * h ^ (j : ZMod p).val ∈ S.HZ :=
      S.HZ.mul_mem (hle hc) (S.H_le_HZ (S.H.pow_mem hh _))
    have he : (W.phi j h * (h ^ (j : ZMod p).val)⁻¹) * h ^ (j : ZMod p).val = W.phi j h := by
      group
    rwa [he] at hm
  have h2 : W.phi j (S.z ^ k) ∈ S.HZ := by
    rw [map_zpow, hz, W.phi_z, ← zpow_natCast, ← zpow_mul, ← hz]
    exact S.zpowers_le_HZ (Subgroup.mem_zpowers_iff.mpr ⟨_, rfl⟩)
  rw [map_mul]
  exact S.HZ.mul_mem h1 h2

theorem HZ_normal : S.HZ.Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨h, hh, k, rfl⟩ := S.mem_HZ_iff.mp hn
  have hdecomp : g * (h * S.z ^ k) * g⁻¹ = (g * h * g⁻¹) * S.z ^ k := by
    have hc : S.z ^ k * g⁻¹ = g⁻¹ * S.z ^ k := (S.commute_z g⁻¹).zpow_left k |>.eq
    calc g * (h * S.z ^ k) * g⁻¹ = (g * h) * (S.z ^ k * g⁻¹) := by group
      _ = (g * h) * (g⁻¹ * S.z ^ k) := by rw [hc]
      _ = (g * h * g⁻¹) * S.z ^ k := by group
  rw [hdecomp]
  have hcomm : g * h * g⁻¹ = ⁅g, h⁆ * h := by
    rw [commutatorElement_def]; group
  rw [hcomm]
  exact S.HZ.mul_mem
    (S.HZ.mul_mem
      (S.comm_le (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h)))
      (S.H_le_HZ hh))
    (S.HZ.zpow_mem S.z_mem_HZ k)

theorem conj_mem {n : G} (hn : n ∈ S.HZ) (g : G) : g * n * g⁻¹ ∈ S.HZ :=
  S.HZ_normal.conj_mem n hn g

theorem inv_mul_mem_iff {g₁ g₂ : G} :
    g₁⁻¹ * g₂ ∈ S.HZ ↔ g₁ * g₂⁻¹ ∈ S.HZ := by
  constructor
  · intro h
    have h1 : (g₁⁻¹ * g₂)⁻¹ ∈ S.HZ := S.HZ.inv_mem h
    have h2 := S.conj_mem h1 g₁
    have he : g₁ * (g₁⁻¹ * g₂)⁻¹ * g₁⁻¹ = g₁ * g₂⁻¹ := by group
    rwa [he] at h2
  · intro h
    have h1 : (g₁ * g₂⁻¹)⁻¹ ∈ S.HZ := S.HZ.inv_mem h
    have h2 := S.conj_mem h1 g₁⁻¹
    have he : g₁⁻¹ * (g₁ * g₂⁻¹)⁻¹ * (g₁⁻¹)⁻¹ = g₁⁻¹ * g₂ := by group
    rwa [he] at h2

theorem ezOf_one : S.ezOf 1 = 0 := by
  have h := S.ezOf_eq_of_decomp (x := (1 : G)) (h := (1 : G)) S.H.one_mem (k := 0) (by simp)
  simpa using h

theorem ezOf_mem_H {h : G} (hh : h ∈ S.H) : S.ezOf h = 0 := by
  have h := S.ezOf_eq_of_decomp (x := h) (h := h) hh (k := 0) (by simp)
  simpa using h

theorem ezOf_mul {x y : G} (hx : x ∈ S.HZ) (hy : y ∈ S.HZ) :
    S.ezOf (x * y) = S.ezOf x + S.ezOf y := by
  obtain ⟨h₁, hh₁, k₁, rfl⟩ := S.mem_HZ_iff.mp hx
  obtain ⟨h₂, hh₂, k₂, rfl⟩ := S.mem_HZ_iff.mp hy
  have hxy := S.mul_zpow_decomp h₁ h₂ k₁ k₂
  rw [S.ezOf_eq_of_decomp (x := (h₁ * S.z ^ k₁) * (h₂ * S.z ^ k₂))
        (h := h₁ * h₂) (S.H.mul_mem hh₁ hh₂) (k := k₁ + k₂) hxy,
      S.ezOf_eq_of_decomp (x := h₁ * S.z ^ k₁) (h := h₁) hh₁ (k := k₁) rfl,
      S.ezOf_eq_of_decomp (x := h₂ * S.z ^ k₂) (h := h₂) hh₂ (k := k₂) rfl]
  push_cast
  ring

theorem ezOf_inv {x : G} (hx : x ∈ S.HZ) : S.ezOf x⁻¹ = -S.ezOf x := by
  have h := S.ezOf_mul (S.HZ.inv_mem hx) hx
  rw [inv_mul_cancel, S.ezOf_one] at h
  exact eq_neg_iff_add_eq_zero.mpr h.symm

theorem ezOf_zpow_nat (n : ℕ) : S.ezOf (S.z ^ n) = (n : ZMod p) := by
  have h := S.ezOf_eq_of_decomp (x := S.z ^ n) (h := (1 : G)) S.H.one_mem (k := (n : ℤ))
    (by rw [zpow_natCast]; simp)
  rw [h]; push_cast; ring

theorem ezOf_zpow_self (k : ℤ) : S.ezOf (S.z ^ k) = (k : ZMod p) := by
  have h := S.ezOf_eq_of_decomp (x := S.z ^ k) (h := (1 : G)) S.H.one_mem (k := k) (by simp)
  simpa using h

noncomputable def sheetOf (a x : G) : ZMod p :=
  S.ezOf (a⁻¹ * x)

theorem sheetOf_eq_ezOf {a x : G} (_hx : x ∈ S.leftCosetN a) :
    S.sheetOf a x = S.ezOf (a⁻¹ * x) := rfl

theorem sheetOf_spec {a x : G} (hx : x ∈ S.leftCosetN a) :
    a⁻¹ * (x * S.z ^ (-(((S.sheetOf a x).val : ℕ) : ℤ))) ∈ S.H := by
  obtain ⟨h, hh, he⟩ := S.ezOf_spec (x := a⁻¹ * x) hx
  have hm : S.sheetOf a x = S.ezOf (a⁻¹ * x) := rfl
  have hz : (h * S.z ^ (((S.ezOf (a⁻¹ * x)).val : ℕ) : ℤ)) *
      S.z ^ (-(((S.ezOf (a⁻¹ * x)).val : ℕ) : ℤ)) = h := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  have hgen : ∀ t : ℤ, (a⁻¹ * x) * S.z ^ t =
      (h * S.z ^ (((S.ezOf (a⁻¹ * x)).val : ℕ) : ℤ)) * S.z ^ t := by
    intro t
    conv_lhs => rw [he]
  have hfin : a⁻¹ * (x * S.z ^ (-(((S.sheetOf a x).val : ℕ) : ℤ))) = h := by
    calc a⁻¹ * (x * S.z ^ (-(((S.sheetOf a x).val : ℕ) : ℤ)))
        = (a⁻¹ * x) * S.z ^ (-(((S.ezOf (a⁻¹ * x)).val : ℕ) : ℤ)) := by rw [hm]; group
      _ = (h * S.z ^ (((S.ezOf (a⁻¹ * x)).val : ℕ) : ℤ)) *
            S.z ^ (-(((S.ezOf (a⁻¹ * x)).val : ℕ) : ℤ)) := hgen _
      _ = h := hz
  rw [hfin]
  exact hh

noncomputable def state (u : ZMod p) (a : G) : G → Option (ZMod p) := by
  classical
  exact fun x => if x ∈ S.leftCosetN a then some (-(u * S.sheetOf a x)) else none

theorem state_apply {u : ZMod p} {a x : G} :
    S.state u a x =
      if x ∈ S.leftCosetN a then some (-(u * S.sheetOf a x)) else none := by
  classical
  unfold state
  rfl

theorem state_apply_some {u : ZMod p} {a x : G} (hx : x ∈ S.leftCosetN a) :
    S.state u a x = some (-(u * S.sheetOf a x)) := by
  classical
  rw [S.state_apply, if_pos hx]

theorem state_ne_none_iff {u : ZMod p} {a x : G} :
    S.state u a x ≠ none ↔ x ∈ S.leftCosetN a := by
  classical
  by_cases hx : x ∈ S.leftCosetN a
  · rw [S.state_apply_some hx]; simp [hx]
  · rw [S.state_apply, if_neg hx]; simp [hx]

def shift (φ : G → Option (ZMod p)) (b : G) : G → Option (ZMod p) :=
  fun x => φ (x * b⁻¹)

theorem shift_state {u : ZMod p} {a b : G} (hb : b ∈ S.HZ) :
    shift (S.state u a) b =
      fun x => (S.state u a x).map (fun e => e + u * S.ezOf b) := by
  funext x
  classical
  by_cases hx : x ∈ S.leftCosetN a
  · have hxb : x * b⁻¹ ∈ S.leftCosetN a := by
      rw [mem_leftCosetN] at hx ⊢
      have he : a⁻¹ * (x * b⁻¹) = (a⁻¹ * x) * b⁻¹ := by group
      rw [he]
      exact S.HZ.mul_mem hx (S.HZ.inv_mem hb)
    rw [show shift (S.state u a) b x = S.state u a (x * b⁻¹) from rfl,
      S.state_apply_some hxb, S.state_apply_some hx]
    simp only [Option.map_some]
    congr 1
    have hs1 : S.sheetOf a (x * b⁻¹) = S.ezOf (a⁻¹ * (x * b⁻¹)) := S.sheetOf_eq_ezOf hxb
    have hs2 : S.sheetOf a x = S.ezOf (a⁻¹ * x) := S.sheetOf_eq_ezOf hx
    have hmul : S.ezOf (a⁻¹ * (x * b⁻¹)) = S.ezOf (a⁻¹ * x) + S.ezOf b⁻¹ := by
      have he : a⁻¹ * (x * b⁻¹) = (a⁻¹ * x) * b⁻¹ := by group
      rw [he]
      exact S.ezOf_mul hx (S.HZ.inv_mem hb)
    have hinv : S.ezOf b⁻¹ = -S.ezOf b := S.ezOf_inv hb
    rw [hs1, hs2, hmul, hinv]
    ring
  · have hxb : x * b⁻¹ ∉ S.leftCosetN a := by
      intro h
      apply hx
      rw [mem_leftCosetN] at h ⊢
      have he : a⁻¹ * x = (a⁻¹ * (x * b⁻¹)) * b := by group
      rw [he]
      exact S.HZ.mul_mem h hb
    rw [show shift (S.state u a) b x = S.state u a (x * b⁻¹) from rfl,
      S.state_apply, if_neg hxb, S.state_apply, if_neg hx]
    simp

theorem ezOf_phi_zpow {W : WeylData G p} (hz : S.z = W.z) (j : (ZMod p)ˣ) (n : ℤ) :
    S.ezOf (W.phi j (S.z ^ n)) = (j : ZMod p) ^ 2 * (n : ZMod p) := by
  haveI : NeZero p := ⟨S.prime.ne_zero⟩
  have h : W.phi j (S.z ^ n) = S.z ^ ((((j : ZMod p) ^ 2).val : ℕ) * n) := by
    rw [map_zpow, hz, W.phi_z, ← zpow_natCast, ← zpow_mul, ← hz]
  rw [h, S.ezOf_zpow_self]
  simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem ezOf_phi_h {W : WeylData G p} (hz : S.z = W.z) {h : G} (hh : h ∈ S.H)
    (j : (ZMod p)ˣ) {ℓ : ZMod p}
    (hℓ : W.phi j h =
      h ^ (j : ZMod p).val * W.z ^ ((((j : ZMod p) - (j : ZMod p) ^ 2) * ℓ).val)) :
    S.ezOf (W.phi j h) = ((j : ZMod p) - (j : ZMod p) ^ 2) * ℓ := by
  haveI : NeZero p := ⟨S.prime.ne_zero⟩
  have hmem : h ^ (j : ZMod p).val ∈ S.H := S.H.pow_mem hh _
  have hk : W.phi j h = h ^ (j : ZMod p).val *
      S.z ^ (((((j : ZMod p) - (j : ZMod p) ^ 2) * ℓ).val : ℕ) : ℤ) := by
    rw [hℓ, ← hz, zpow_natCast]
  have hres := S.ezOf_eq_of_decomp (x := W.phi j h) (h := h ^ (j : ZMod p).val) hmem
    (k := ((((j : ZMod p) - (j : ZMod p) ^ 2) * ℓ).val : ℤ)) hk
  rw [hres]
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]

theorem shift_state_phi_z {W : WeylData G p} (hz : S.z = W.z) {u : ZMod p} {a : G}
    (j : (ZMod p)ˣ) :
    shift (S.state u a) (W.phi j W.z) =
      fun x => (S.state u a x).map (fun e => e + u * ((j : ZMod p) ^ 2)) := by
  have hb : W.phi j W.z ∈ S.HZ := S.phi_maps_HZ hz j (by rw [← hz]; exact S.z_mem_HZ)
  rw [S.shift_state hb]
  have hez : S.ezOf (W.phi j W.z) = (j : ZMod p) ^ 2 := by
    have h := S.ezOf_phi_zpow hz j 1
    simpa [hz] using h
  simp only [hez]

theorem shift_state_phi_h {W : WeylData G p} (hz : S.z = W.z) {u : ZMod p} {a : G}
    {h : G} (hh : h ∈ S.H) (j : (ZMod p)ˣ) :
    ∃ ℓ : ZMod p, shift (S.state u a) (W.phi j h) =
      fun x => (S.state u a x).map
        (fun e => e + u * (((j : ZMod p) - (j : ZMod p) ^ 2) * ℓ)) := by
  obtain ⟨ℓ, hℓ⟩ := W.phi_eq_pow_mul_zpow h
  refine ⟨ℓ, ?_⟩
  have hb : W.phi j h ∈ S.HZ := S.phi_maps_HZ hz j (S.H_le_HZ hh)
  rw [S.shift_state hb]
  have hez : S.ezOf (W.phi j h) = ((j : ZMod p) - (j : ZMod p) ^ 2) * ℓ :=
    S.ezOf_phi_h hz hh j (hℓ j)
  simp only [hez]

theorem phi_inv_apply {W : WeylData G p} (j : (ZMod p)ˣ) (y : G) :
    W.phi j⁻¹ (W.phi j y) = y := by
  have heq : (W.phi j⁻¹ * W.phi j) y = y := by
    rw [← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  rwa [MulAut.mul_apply] at heq

theorem phi_mul_inv {W : WeylData G p} (j : (ZMod p)ˣ) (g₁ g₂ : G) :
    W.phi j g₁ * (W.phi j g₂)⁻¹ = W.phi j (g₁ * g₂⁻¹) := by
  rw [← map_inv, ← map_mul]

theorem phi_mem_HZ_iff {W : WeylData G p} (hz : S.z = W.z) (j : (ZMod p)ˣ) {y : G} :
    W.phi j y ∈ S.HZ ↔ y ∈ S.HZ := by
  constructor
  · intro hy
    have h := S.phi_maps_HZ hz (j⁻¹) hy
    rwa [phi_inv_apply (W := W) j y] at h
  · exact S.phi_maps_HZ hz j

noncomputable def PsiParam (a : Fin 4 → G) (u : Fin 4 → ZMod p) (b : Fin 4 → G) :
    (Fin 4 → G) → Option (ZMod p) := by
  classical
  exact fun x => if (∀ i, S.state (u i) (a i) (x i * (b i)⁻¹) ≠ none) then
    some (∑ i, -(u i * S.sheetOf (a i) (x i * (b i)⁻¹)))
  else none

theorem PsiParam_apply {a : Fin 4 → G} {u : Fin 4 → ZMod p} {b : Fin 4 → G}
    {x : Fin 4 → G} :
    S.PsiParam a u b x =
      if (∀ i, S.state (u i) (a i) (x i * (b i)⁻¹) ≠ none) then
        some (∑ i, -(u i * S.sheetOf (a i) (x i * (b i)⁻¹)))
      else none := by
  classical
  unfold PsiParam
  rfl

theorem PsiParam_mul {a : Fin 4 → G} {u : Fin 4 → ZMod p} {b b' : Fin 4 → G}
    (hs : ∀ i, b' i * (b i)⁻¹ ∈ S.HZ)
    (hsum : ∑ i, u i * S.ezOf (b i * (b' i)⁻¹) = 0) :
    S.PsiParam a u b' = S.PsiParam a u b := by
  funext x
  classical
  have hb'i : ∀ i, b i * (b' i)⁻¹ ∈ S.HZ := by
    intro i
    have := S.HZ.inv_mem (hs i)
    rwa [mul_inv_rev, inv_inv] at this
  have hsupp : ∀ i, (S.state (u i) (a i) (x i * (b' i)⁻¹) ≠ none ↔
      S.state (u i) (a i) (x i * (b i)⁻¹) ≠ none) := by
    intro i
    rw [S.state_ne_none_iff, S.state_ne_none_iff, mem_leftCosetN, mem_leftCosetN]
    constructor
    · intro h
      have he : (a i)⁻¹ * (x i * (b i)⁻¹) =
          ((a i)⁻¹ * (x i * (b' i)⁻¹)) * (b' i * (b i)⁻¹) := by group
      rw [he]
      exact S.HZ.mul_mem h (hs i)
    · intro h
      have he : (a i)⁻¹ * (x i * (b' i)⁻¹) =
          ((a i)⁻¹ * (x i * (b i)⁻¹)) * (b i * (b' i)⁻¹) := by group
      rw [he]
      exact S.HZ.mul_mem h (hb'i i)
  have hall : (∀ i, S.state (u i) (a i) (x i * (b' i)⁻¹) ≠ none) ↔
      ∀ i, S.state (u i) (a i) (x i * (b i)⁻¹) ≠ none :=
    ⟨fun h i => (hsupp i).mp (h i), fun h i => (hsupp i).mpr (h i)⟩
  rw [S.PsiParam_apply, S.PsiParam_apply]
  by_cases hx : ∀ i, S.state (u i) (a i) (x i * (b i)⁻¹) ≠ none
  · have hx' : ∀ i, S.state (u i) (a i) (x i * (b' i)⁻¹) ≠ none := hall.mpr hx
    rw [if_pos hx', if_pos hx]
    congr 1
    have hterm : ∀ i, -(u i * S.sheetOf (a i) (x i * (b' i)⁻¹)) =
        -(u i * S.sheetOf (a i) (x i * (b i)⁻¹)) - u i * S.ezOf (b i * (b' i)⁻¹) := by
      intro i
      have hy : x i * (b i)⁻¹ ∈ S.leftCosetN (a i) := S.state_ne_none_iff.mp (hx i)
      have hy' : x i * (b' i)⁻¹ ∈ S.leftCosetN (a i) := S.state_ne_none_iff.mp (hx' i)
      have hs1 : S.sheetOf (a i) (x i * (b' i)⁻¹) = S.ezOf ((a i)⁻¹ * (x i * (b' i)⁻¹)) :=
        S.sheetOf_eq_ezOf hy'
      have hs2 : S.sheetOf (a i) (x i * (b i)⁻¹) = S.ezOf ((a i)⁻¹ * (x i * (b i)⁻¹)) :=
        S.sheetOf_eq_ezOf hy
      have hfac : (a i)⁻¹ * (x i * (b' i)⁻¹) =
          ((a i)⁻¹ * (x i * (b i)⁻¹)) * (b i * (b' i)⁻¹) := by group
      rw [hs1, hs2, hfac, S.ezOf_mul hy (hb'i i)]
      ring
    calc ∑ i, -(u i * S.sheetOf (a i) (x i * (b' i)⁻¹))
        = ∑ i, (-(u i * S.sheetOf (a i) (x i * (b i)⁻¹)) -
            u i * S.ezOf (b i * (b' i)⁻¹)) :=
          Finset.sum_congr rfl (fun i _ => hterm i)
      _ = (∑ i, -(u i * S.sheetOf (a i) (x i * (b i)⁻¹))) -
            ∑ i, u i * S.ezOf (b i * (b' i)⁻¹) :=
          Finset.sum_sub_distrib (s := Finset.univ)
            (f := fun i => -(u i * S.sheetOf (a i) (x i * (b i)⁻¹)))
            (g := fun i => u i * S.ezOf (b i * (b' i)⁻¹))
      _ = ∑ i, -(u i * S.sheetOf (a i) (x i * (b i)⁻¹)) := by rw [hsum, sub_zero]
  · have hx' : ¬ ∀ i, S.state (u i) (a i) (x i * (b' i)⁻¹) ≠ none :=
      fun h => hx (hall.mp h)
    rw [if_neg hx', if_neg hx]

theorem PsiParam_ne {a : Fin 4 → G} {u : Fin 4 → ZMod p} {b b' : Fin 4 → G}
    (h : ∃ i, b i * (b' i)⁻¹ ∉ S.HZ) :
    S.PsiParam a u b ≠ S.PsiParam a u b' := by
  classical
  obtain ⟨i₀, hi₀⟩ := h
  intro heq
  let x : Fin 4 → G := fun i => a i * b i
  have hsupp_b : ∀ i, S.state (u i) (a i) (x i * (b i)⁻¹) ≠ none := by
    intro i
    rw [S.state_ne_none_iff, mem_leftCosetN]
    have hx : (a i)⁻¹ * (x i * (b i)⁻¹) = 1 := by dsimp [x]; group
    rw [hx]
    exact S.HZ.one_mem
  have hval_b : S.PsiParam a u b x ≠ none := by
    rw [S.PsiParam_apply, if_pos hsupp_b]
    simp
  have hsupp_b' : ¬ ∀ i, S.state (u i) (a i) (x i * (b' i)⁻¹) ≠ none := by
    intro hall
    have hi := hall i₀
    rw [S.state_ne_none_iff, mem_leftCosetN] at hi
    apply hi₀
    have hx : (a i₀)⁻¹ * (x i₀ * (b' i₀)⁻¹) = b i₀ * (b' i₀)⁻¹ := by dsimp [x]; group
    rwa [hx] at hi
  rw [heq] at hval_b
  rw [S.PsiParam_apply, if_neg hsupp_b'] at hval_b
  exact hval_b rfl

noncomputable def Psi (W : WeylData G p) (a : Fin 4 → G) (u : Fin 4 → ZMod p)
    (j : Fin 4 → (ZMod p)ˣ) (g : G) : (Fin 4 → G) → Option (ZMod p) :=
  S.PsiParam a u (fun i => W.phi (j i) g)

theorem hiding_of_appropriate {W : WeylData G p} (hz : S.z = W.z)
    {a : Fin 4 → G} {u : Fin 4 → ZMod p} {j : Fin 4 → (ZMod p)ˣ}
    (happ : ∀ g ∈ S.HZ, ∑ i, u i * S.ezOf (W.phi (j i) g) = 0) :
    IsHidingFamily S.HZ (fun g => S.Psi W a u j g) := by
  intro g₁ g₂
  constructor
  · intro heq
    by_contra hmem
    have hg : g₁ * g₂⁻¹ ∉ S.HZ := fun h => hmem (S.inv_mul_mem_iff.mpr h)
    have hne : W.phi (j 0) g₁ * (W.phi (j 0) g₂)⁻¹ ∉ S.HZ := by
      intro h
      rw [phi_mul_inv (W := W) (j 0) g₁ g₂] at h
      exact hg ((S.phi_mem_HZ_iff hz (j 0)).mp h)
    refine S.PsiParam_ne (a := a) (u := u)
      (b := fun i => W.phi (j i) g₁) (b' := fun i => W.phi (j i) g₂)
      ⟨0, ?_⟩ heq
    simpa using hne
  · intro hmem
    have hg' : g₁ * g₂⁻¹ ∈ S.HZ := S.inv_mul_mem_iff.mp hmem
    have hg'' : g₂ * g₁⁻¹ ∈ S.HZ := by
      have h0 := S.HZ.inv_mem hg'
      rwa [mul_inv_rev, inv_inv] at h0
    have hs : ∀ i, W.phi (j i) g₂ * (W.phi (j i) g₁)⁻¹ ∈ S.HZ := by
      intro i
      rw [phi_mul_inv (W := W) (j i) g₂ g₁]
      exact S.phi_maps_HZ hz (j i) hg''
    have hsum : ∑ i, u i * S.ezOf (W.phi (j i) g₁ * (W.phi (j i) g₂)⁻¹) = 0 := by
      have hstep : ∀ i, W.phi (j i) g₁ * (W.phi (j i) g₂)⁻¹ =
          W.phi (j i) (g₁ * g₂⁻¹) := fun i => phi_mul_inv (W := W) (j i) g₁ g₂
      simp only [hstep]
      exact happ (g₁ * g₂⁻¹) hg'
    exact (S.PsiParam_mul (a := a) (u := u) (b := fun i => W.phi (j i) g₁)
      (b' := fun i => W.phi (j i) g₂) hs hsum).symm

theorem appropriate_of_witness {W : WeylData G p} (hz : S.z = W.z)
    {u : Fin 4 → ZMod p} {j : Fin 4 → (ZMod p)ˣ} (hwit : IsWitness p u j) :
    ∀ g ∈ S.HZ, ∑ i, u i * S.ezOf (W.phi (j i) g) = 0 := by
  haveI : NeZero p := ⟨S.prime.ne_zero⟩
  obtain ⟨hw1, hw2⟩ := hwit
  intro g hg
  obtain ⟨h, hh, he⟩ := S.ezOf_spec hg
  obtain ⟨ℓ, hℓ⟩ := W.phi_eq_pow_mul_zpow h
  have hterm : ∀ i, u i * S.ezOf (W.phi (j i) g) =
      ℓ * (u i * ((j i : ZMod p) - (j i : ZMod p) ^ 2)) +
        S.ezOf g * (u i * (j i : ZMod p) ^ 2) := by
    intro i
    have h1N : W.phi (j i) h ∈ S.HZ := S.phi_maps_HZ hz (j i) (S.H_le_HZ hh)
    have h2N : W.phi (j i) (S.z ^ (((S.ezOf g).val : ℕ) : ℤ)) ∈ S.HZ :=
      S.phi_maps_HZ hz (j i) (S.HZ.zpow_mem S.z_mem_HZ _)
    have hdecomp : W.phi (j i) g =
        W.phi (j i) h * W.phi (j i) (S.z ^ (((S.ezOf g).val : ℕ) : ℤ)) := by
      conv_lhs => rw [he]
      rw [map_mul]
    have h1 : S.ezOf (W.phi (j i) h) =
        ((j i : ZMod p) - (j i : ZMod p) ^ 2) * ℓ :=
      S.ezOf_phi_h hz hh (j i) (hℓ (j i))
    have h2 : S.ezOf (W.phi (j i) (S.z ^ (((S.ezOf g).val : ℕ) : ℤ))) =
        (j i : ZMod p) ^ 2 * S.ezOf g := by
      have h := S.ezOf_phi_zpow hz (j i) (((S.ezOf g).val : ℕ) : ℤ)
      rw [h]
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [hdecomp, S.ezOf_mul h1N h2N, h1, h2]
    ring
  calc ∑ i, u i * S.ezOf (W.phi (j i) g)
      = ∑ i, (ℓ * (u i * ((j i : ZMod p) - (j i : ZMod p) ^ 2)) +
          S.ezOf g * (u i * (j i : ZMod p) ^ 2)) :=
        Finset.sum_congr rfl (fun i _ => hterm i)
    _ = ℓ * (∑ i, u i * ((j i : ZMod p) - (j i : ZMod p) ^ 2)) +
          S.ezOf g * (∑ i, u i * (j i : ZMod p) ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = 0 := by rw [hw1, hw2, mul_zero, mul_zero, add_zero]

end SheetData

end Qatlib.Papers.ExtraSpecHSP07.MainResults
