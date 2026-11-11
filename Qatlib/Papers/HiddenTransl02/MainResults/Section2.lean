/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic

/-!
# Stabilizers and translating cosets of group actions

This module defines `stabilizer` and `translatingCoset` for group actions and identifies a
nonempty translating set with a left coset of the source stabilizer. For the translation action
on functions, `translatingCoset_singleton` proves that an injective source function has a unique
specified translation.

The development follows [FriedlEtAl2014].

## Main statements

* `mem_stabilizer_smul_iff`: An element `x` fixes `u • φ` exactly when its conjugate `u⁻¹ * x *
  u` fixes `φ`.
* `translatingCoset_eq_leftCoset`: If `u` sends `φ₁` to `φ₀`, the translating set equals the
  left coset of the stabilizer of `φ₁` represented by `u`.
* `translatingCoset_singleton`: If the injective function `f₁` gives `f₀` by right translation
  by `u`, their translating set is the singleton containing `u`.

## References

* [Friedl et al., 2014][FriedlEtAl2014]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option warningAsError false

namespace Qatlib.Papers.HiddenTransl02.MainResults.Section2

variable {G Γ : Type*} [Group G] [MulAction G Γ]

/-- The subgroup of group elements whose action fixes `φ` ([Proposition 2.1][FriedlEtAl2014]). -/
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

/-- Membership in the stabilizer is equivalent to fixing `φ` under the group action. -/
@[simp]
theorem mem_stabilizer {φ : Γ} {x : G} : x ∈ stabilizer φ ↔ x • φ = φ := Iff.rfl

/-- If `x` fixes `φ`, its conjugate by `u` fixes `u • φ`. -/
theorem conj_mem_stabilizer {u x : G} {φ : Γ} (hx : x • φ = φ) :
    (u * x * u⁻¹) • (u • φ) = u • φ := by
  rw [mul_smul, mul_smul, inv_smul_smul, hx]

/-- An element `x` fixes `u • φ` exactly when its conjugate `u⁻¹ * x * u` fixes `φ`
([Proposition 2.1][FriedlEtAl2014]). -/
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

/-- The set of group elements sending `φ₁` to `φ₀` under the action. -/
def translatingCoset (φ₀ φ₁ : Γ) : Set G := {u | u • φ₁ = φ₀}

/-- The left coset of `H` represented by `u`, described by the condition `u⁻¹ * g ∈ H`. -/
def leftCoset (u : G) (H : Subgroup G) : Set G := {g | u⁻¹ * g ∈ H}

/-- If `u` sends `φ₁` to `φ₀`, the translating set equals the left coset of the stabilizer of
`φ₁` represented by `u` ([Corollary 3.8][FriedlEtAl2014]). -/
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

/-- Every nonempty translating set possesses a representative making it a left coset of the
source stabilizer. -/
theorem translatingCoset_empty_or_coset {φ₀ φ₁ : Γ}
    (h : (translatingCoset (G := G) φ₀ φ₁).Nonempty) :
    ∃ u : G, translatingCoset (G := G) φ₀ φ₁ = leftCoset u (stabilizer (G := G) φ₁) := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u, translatingCoset_eq_leftCoset hu⟩

section Functions

variable {S : Type*}

/-- Right translation of a function argument by `x`, sending `g` to `f (g * x)` ([Proposition
2.2][FriedlEtAl2014]). -/
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

/-- For the translation action on functions, the stabilizer consists exactly of elements whose
right translations preserve all function values ([Proposition 2.1][FriedlEtAl2014]). -/
theorem stabilizer_translate_eq (f : G → S) :
    stabilizer (G := G) (Γ := G → S) f = {x : G | ∀ g, f (g * x) = f g} := by
  ext x
  constructor
  · intro h g
    exact congrFun h g
  · intro h
    exact funext h

/-- If the injective function `f₁` gives `f₀` by right translation by `u`, their translating set
is the singleton containing `u` ([Proposition 2.2][FriedlEtAl2014]). -/
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

/-- For the function translation action, injectivity of `f₁` and the specified translation
identity imply that the translating set is exactly `{u}`. -/
theorem translatingCoset_singleton' {f₀ f₁ : G → S} {u : G}
    (htrans : ∀ g, f₀ g = f₁ (g * u)) (hinj : Function.Injective f₁) :
    translatingCoset (Γ := G → S) f₀ f₁ = {u} :=
  translatingCoset_singleton htrans hinj

end Functions

end Qatlib.Papers.HiddenTransl02.MainResults.Section2
