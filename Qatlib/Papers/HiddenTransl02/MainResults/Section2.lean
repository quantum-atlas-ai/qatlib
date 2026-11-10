/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option warningAsError false

namespace Qatlib.Papers.HiddenTransl02.MainResults.Section2

variable {G Γ : Type*} [Group G] [MulAction G Γ]

def stabilizer (φ : Γ) : Subgroup G where
  carrier := {x | x • φ = φ}
  one_mem' := one_smul G φ
  mul_mem' := by
    intro a b ha hb
    show (a * b) • φ = φ
    rw [mul_smul, hb, ha]
  inv_mem' := by
    intro a ha
    show a⁻¹ • φ = φ
    calc a⁻¹ • φ = a⁻¹ • (a • φ) := by rw [ha]
      _ = φ := inv_smul_smul a φ

@[simp]
theorem mem_stabilizer {φ : Γ} {x : G} : x ∈ stabilizer φ ↔ x • φ = φ := Iff.rfl

theorem conj_mem_stabilizer {u x : G} {φ : Γ} (hx : x • φ = φ) :
    (u * x * u⁻¹) • (u • φ) = u • φ := by
  rw [mul_smul, mul_smul, inv_smul_smul, hx]

theorem mem_stabilizer_smul_iff {u x : G} {φ : Γ} :
    x ∈ stabilizer (u • φ) ↔ u⁻¹ * x * u ∈ stabilizer φ := by
  simp only [mem_stabilizer]
  constructor
  · intro h
    calc (u⁻¹ * x * u) • φ = (u⁻¹ * x) • (u • φ) := by rw [mul_smul]
      _ = u⁻¹ • (x • (u • φ)) := by rw [mul_smul]
      _ = u⁻¹ • (u • φ) := by rw [h]
      _ = φ := inv_smul_smul u φ
  · intro h
    calc x • (u • φ) = (x * u) • φ := by rw [mul_smul]
      _ = (u * (u⁻¹ * x * u)) • φ := by group
      _ = u • ((u⁻¹ * x * u) • φ) := by rw [mul_smul]
      _ = u • φ := by rw [h]

def translatingCoset (φ₀ φ₁ : Γ) : Set G := {u | u • φ₁ = φ₀}

def leftCoset (u : G) (H : Subgroup G) : Set G := {g | u⁻¹ * g ∈ H}

theorem translatingCoset_eq_leftCoset {φ₀ φ₁ : Γ} {u : G} (hu : u • φ₁ = φ₀) :
    translatingCoset φ₀ φ₁ = leftCoset u (stabilizer φ₁) := by
  ext v
  simp only [translatingCoset, leftCoset, Set.mem_setOf_eq, mem_stabilizer]
  constructor
  · intro hv
    have h : (u⁻¹ * v) • φ₁ = φ₁ := by
      rw [mul_smul, hv, ← hu, inv_smul_smul]
    exact h
  · intro hv
    calc v • φ₁ = (u * (u⁻¹ * v)) • φ₁ := by rw [mul_inv_cancel_left]
      _ = u • ((u⁻¹ * v) • φ₁) := by rw [mul_smul]
      _ = u • φ₁ := by rw [hv]
      _ = φ₀ := hu

theorem translatingCoset_empty_or_coset {φ₀ φ₁ : Γ}
    (h : (translatingCoset (G := G) φ₀ φ₁).Nonempty) :
    ∃ u : G, translatingCoset (G := G) φ₀ φ₁ = leftCoset u (stabilizer (G := G) φ₁) := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u, translatingCoset_eq_leftCoset hu⟩

section Functions

variable {S : Type*}

def translateAction (x : G) (f : G → S) : G → S := fun g => f (g * x)

instance translateActionMulAction : MulAction G (G → S) where
  smul := translateAction
  one_smul := by
    intro f
    funext g
    show f (g * 1) = f g
    rw [mul_one]
  mul_smul := by
    intro x y f
    funext g
    show f (g * (x * y)) = f ((g * x) * y)
    rw [mul_assoc]

theorem stabilizer_translate_eq (f : G → S) :
    stabilizer (G := G) (Γ := G → S) f = {x : G | ∀ g, f (g * x) = f g} := by
  ext x
  constructor
  · intro h g
    exact congrFun h g
  · intro h
    exact funext h

theorem translatingCoset_singleton {f₀ f₁ : G → S} {u : G}
    (htrans : ∀ g, f₀ g = f₁ (g * u)) (hinj : Function.Injective f₁) :
    translatingCoset (G := G) (Γ := G → S) f₀ f₁ = {u} := by
  ext v
  constructor
  · intro hv
    simp only [Set.mem_singleton_iff]
    have hv1 : f₁ (1 * v) = f₀ 1 := congrFun hv 1
    have h1 : f₁ v = f₁ u := by
      rw [one_mul] at hv1
      rw [hv1, htrans 1, one_mul]
    exact hinj h1
  · intro hv
    simp only [Set.mem_singleton_iff] at hv
    subst v
    show (fun g => f₁ (g * u)) = f₀
    funext g
    exact (htrans g).symm

theorem translatingCoset_singleton' {f₀ f₁ : G → S} {u : G}
    (htrans : ∀ g, f₀ g = f₁ (g * u)) (hinj : Function.Injective f₁) :
    translatingCoset (Γ := G → S) f₀ f₁ = {u} :=
  translatingCoset_singleton htrans hinj

end Functions

end Qatlib.Papers.HiddenTransl02.MainResults.Section2
