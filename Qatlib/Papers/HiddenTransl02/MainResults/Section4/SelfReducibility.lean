/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

set_option autoImplicit false

open scoped Pointwise

namespace Qatlib.Papers.HiddenTransl02.MainResults.Section4

variable {G Γ : Type*}

section NormalCorrection

variable [Group G]

theorem correction_mem_smul_inter (N H : Subgroup G) {z u h h' n n' : G}
    (hn : n ∈ N) (hn' : n' ∈ N) (hh : h ∈ H) (hh' : h' ∈ H)
    (hz : z * n = u * h) (hz' : z * n' = u * h') :
    h' ∈ (fun x => h * x) '' ((H ⊓ N : Subgroup G) : Set G) := by
  have hh_eq : h = u⁻¹ * (z * n) := by rw [hz]; group
  have hh'_eq : h' = u⁻¹ * (z * n') := by rw [hz']; group
  have hcalc : h⁻¹ * h' = n⁻¹ * n' := by rw [hh_eq, hh'_eq]; group
  refine ⟨h⁻¹ * h', ⟨H.mul_mem (H.inv_mem hh) hh', ?_⟩, by group⟩
  rw [hcalc]
  exact N.mul_mem (N.inv_mem hn) hn'

theorem biUnion_correction_eq (N H : Subgroup G) (u : G) (σ τ : G → G)
    (hσ : ∀ z, σ z ∈ N) (hτ : ∀ z, τ z ∈ H)
    (hpair : ∀ z, z ∈ ({u} : Set G) * (H : Set G) * (N : Set G) →
      z * σ z = u * τ z) :
    {x : G | ∃ z ∈ (({u} : Set G) * (H : Set G) * (N : Set G)),
      ∃ k ∈ (H ⊓ N : Subgroup G), τ z * k = x} = (H : Set G) := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, _hz, k, hk, hkx⟩
    rw [← hkx]
    exact H.mul_mem (hτ z) hk.1
  · intro hx
    have hmem : u * x ∈ ({u} : Set G) * (H : Set G) * (N : Set G) := by
      have h1 : u * x ∈ ({u} : Set G) * (H : Set G) := by
        rw [Set.mem_mul]
        exact ⟨u, Set.mem_singleton u, x, hx, rfl⟩
      rw [Set.mem_mul]
      exact ⟨u * x, h1, 1, N.one_mem, by rw [mul_one]⟩
    have huniq := correction_mem_smul_inter N H
      (z := u * x) (u := u) (h := τ (u * x)) (h' := x)
      (n := σ (u * x)) (n' := 1)
      (hσ (u * x)) (Subgroup.one_mem N) (hτ (u * x)) hx
      (hpair (u * x) hmem) (by rw [mul_one])
    obtain ⟨k, hk, hkx⟩ := huniq
    exact ⟨u * x, hmem, k, hk, hkx⟩

end NormalCorrection

section TranslatingCoset

variable [Group G] [MulAction G Γ]

def normalTranslatingSet (N : Subgroup G) (φ₀ φ₁ : Γ) (z : G) : Set G :=
  {v : G | v ∈ N ∧ v • φ₁ = z⁻¹ • φ₀}

theorem normalTranslatingSet_eq_coset (N H : Subgroup G) {φ₀ φ₁ : Γ} {u z n h : G}
    (hH : H = MulAction.stabilizer G φ₁)
    (hu : u • φ₁ = φ₀) (hz : z * n = u * h) (hn : n ∈ N) (hh : h ∈ H) :
    normalTranslatingSet (Γ := Γ) N φ₀ φ₁ z =
      (fun k => n * k) '' ((H ⊓ N : Subgroup G) : Set G) := by
  have hhphi : h • φ₁ = φ₁ := by
    have := hh; rw [hH] at this; exact this
  have hzinv : z⁻¹ * u = n * h⁻¹ := by
    calc z⁻¹ * u = z⁻¹ * (u * h) * h⁻¹ := by group
      _ = z⁻¹ * (z * n) * h⁻¹ := by rw [← hz]
      _ = n * h⁻¹ := by group
  ext v
  constructor
  · rintro ⟨hvN, hv⟩
    have hstab : v⁻¹ * (z⁻¹ * u) ∈ H := by
      rw [hH]
      show (v⁻¹ * (z⁻¹ * u)) • φ₁ = φ₁
      rw [mul_smul, mul_smul, hu, ← hv, inv_smul_smul]
    have hvN' : v⁻¹ * n ∈ H := by
      have heq : v⁻¹ * n = (v⁻¹ * (z⁻¹ * u)) * h := by rw [hzinv]; group
      rw [heq]
      exact H.mul_mem hstab hh
    have hmemH : n⁻¹ * v ∈ H := by
      have := H.inv_mem hvN'
      simpa [mul_inv_rev, inv_inv] using this
    refine ⟨n⁻¹ * v, ⟨hmemH, N.mul_mem (N.inv_mem hn) hvN⟩, by group⟩
  · rintro ⟨k, hk, rfl⟩
    have hkphi : k • φ₁ = φ₁ := by
      have := hk.1; rw [hH] at this; exact this
    refine ⟨N.mul_mem hn hk.2, ?_⟩
    have hn_phi : n • φ₁ = z⁻¹ • φ₀ := by
      have hz' : n = z⁻¹ * (u * h) := by rw [← hz]; group
      rw [hz', mul_smul, mul_smul, hhphi, hu]
    rw [mul_smul, hkphi]
    exact hn_phi

end TranslatingCoset

end Qatlib.Papers.HiddenTransl02.MainResults.Section4
