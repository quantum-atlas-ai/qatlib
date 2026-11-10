/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemidirectHSP07.MainResults.FactorReduction
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Qatlib.Papers.SemidirectHSP07.MainResults

def HiddenFor {G X : Type*} [Group G] (f : G → X) (H : Subgroup G) : Prop :=
  ∀ x y : G, f x = f y ↔ x⁻¹ * y ∈ H

theorem subgroup_eq_of_map_eq
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (hcop : Nat.Coprime (Nat.card A) (Nat.card B))
    {H₁ H₂ : Subgroup (A × B)}
    (h1 : H₁.map (MonoidHom.fst A B) = H₂.map (MonoidHom.fst A B))
    (h2 : H₁.map (MonoidHom.snd A B) = H₂.map (MonoidHom.snd A B)) :
    H₁ = H₂ := by
  rw [subgroup_eq_prod_of_coprime_card hcop H₁,
    subgroup_eq_prod_of_coprime_card hcop H₂, h1, h2]

theorem hides_fst
    {A B X : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (hcop : Nat.Coprime (Nat.card A) (Nat.card B))
    {H : Subgroup (A × B)} {f : A × B → X} (hf : HiddenFor f H) :
    HiddenFor (fun a : A => f (a, 1)) (H.map (MonoidHom.fst A B)) := by
  intro a a'
  rw [hf]
  have hz : ((a, 1) : A × B)⁻¹ * (a', 1) = (a⁻¹ * a', 1) := by simp
  rw [hz]
  constructor
  · intro h
    exact Subgroup.mem_map.mpr ⟨(a⁻¹ * a', 1), h, rfl⟩
  · intro h
    rw [Subgroup.mem_map] at h
    obtain ⟨⟨x1, x2⟩, hxH, hxeq⟩ := h
    have hx1 : x1 = a⁻¹ * a' := hxeq
    have hfst : (x1, 1) ∈ H := fst_mem_of_coprime hcop H hxH
    rw [← hx1]
    exact hfst

theorem hides_snd
    {A B X : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (hcop : Nat.Coprime (Nat.card A) (Nat.card B))
    {H : Subgroup (A × B)} {f : A × B → X} (hf : HiddenFor f H) :
    HiddenFor (fun b : B => f (1, b)) (H.map (MonoidHom.snd A B)) := by
  intro b b'
  rw [hf]
  have hz : ((1, b) : A × B)⁻¹ * (1, b') = (1, b⁻¹ * b') := by simp
  rw [hz]
  constructor
  · intro h
    exact Subgroup.mem_map.mpr ⟨(1, b⁻¹ * b'), h, rfl⟩
  · intro h
    rw [Subgroup.mem_map] at h
    obtain ⟨⟨x1, x2⟩, hxH, hxeq⟩ := h
    have hx2 : x2 = b⁻¹ * b' := hxeq
    have hsnd : (1, x2) ∈ H := snd_mem_of_coprime hcop H hxH
    rw [← hx2]
    exact hsnd

theorem source_hsp_reduction (p q r s : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hs : 0 < s) (hne : p ≠ q)
    (ψ : Cyc (p ^ 2) →* MulAut (Cyc (p ^ r))) {X : Type*}
    (H : Subgroup (Cyc (q ^ s) × SDG p r ψ)) (f : Cyc (q ^ s) × SDG p r ψ → X)
    (hf : HiddenFor f H) :
    HiddenFor (fun a : Cyc (q ^ s) => f (a, 1))
        (H.map (MonoidHom.fst _ _)) ∧
      HiddenFor (fun b : SDG p r ψ => f (1, b))
        (H.map (MonoidHom.snd _ _)) ∧
      (∀ H' : Subgroup (Cyc (q ^ s) × SDG p r ψ),
        H'.map (MonoidHom.fst _ _) = H.map (MonoidHom.fst _ _) →
        H'.map (MonoidHom.snd _ _) = H.map (MonoidHom.snd _ _) → H' = H) := by
  haveI : NeZero (q ^ s) := ⟨pow_ne_zero s hq.ne_zero⟩
  haveI : Finite (Cyc (q ^ s)) := Finite.of_fintype _
  haveI : Finite (SDG p r ψ) :=
    Nat.finite_of_card_ne_zero (by
      rw [card_SDG_prime_pow p r hp ψ]
      exact pow_ne_zero _ hp.ne_zero)
  have hcop := coprime_card_cyc_sdg p q r s hp hq hs hne ψ
  exact ⟨hides_fst hcop hf, hides_snd hcop hf,
    fun H' h1 h2 => subgroup_eq_of_map_eq hcop h1 h2⟩

end Qatlib.Papers.SemidirectHSP07.MainResults
