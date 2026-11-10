/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NilpotentHSP07.MainResults

open scoped BigOperators

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

def inner (ψ φ : G → ℂ) : ℂ := ∑ x, ψ x * star (φ x)

def rightAct (g : G) (ψ : G → ℂ) : G → ℂ := fun x => ψ (x * g⁻¹)

theorem inner_rightAct (g : G) (ψ φ : G → ℂ) :
    inner (rightAct g ψ) (rightAct g φ) = inner ψ φ := by
  unfold inner rightAct
  exact Equiv.sum_comp (Equiv.mulRight g⁻¹) (fun y => ψ y * star (φ y))

theorem rightAct_mul (g h : G) (ψ : G → ℂ) :
    rightAct (g * h) ψ = rightAct h (rightAct g ψ) := by
  funext x
  simp [rightAct, mul_inv_rev, mul_assoc]

def cosetState (K : Subgroup G) (a : G) (c : ℂ) : G → ℂ := by
  classical
  exact fun x => if ∃ k ∈ K, x = a * k then c else 0

def inCoset (K : Subgroup G) (a : G) (x : G) : Prop := ∃ k ∈ K, x = a * k

theorem inCoset_congr (K : Subgroup G) {a b : G} (h : a⁻¹ * b ∈ K) :
    ∀ x, inCoset K a x ↔ inCoset K b x := by
  intro x
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨(a⁻¹ * b)⁻¹ * k, K.mul_mem (K.inv_mem h) hk, ?_⟩
    group
  · rintro ⟨k, hk, rfl⟩
    refine ⟨(a⁻¹ * b) * k, K.mul_mem h hk, ?_⟩
    group

theorem cosetState_congr (K : Subgroup G) {a b : G} (h : a⁻¹ * b ∈ K) (c : ℂ) :
    cosetState K a c = cosetState K b c := by
  funext x
  by_cases hxa : ∃ k ∈ K, x = a * k
  · have hxb : ∃ k ∈ K, x = b * k := (inCoset_congr K h x).mp hxa
    simp only [cosetState]
    rw [if_pos hxa, if_pos hxb]
  · have hxb : ¬ ∃ k ∈ K, x = b * k := fun h' => hxa ((inCoset_congr K h x).mpr h')
    simp only [cosetState]
    rw [if_neg hxa, if_neg hxb]

theorem rightAct_cosetState (K : Subgroup G) [K.Normal] (a g : G) (c : ℂ) :
    rightAct g (cosetState K a c) = cosetState K (a * g) c := by
  funext x
  simp only [rightAct, cosetState]
  by_cases hx : ∃ k ∈ K, x * g⁻¹ = a * k
  · have hx' : ∃ k ∈ K, x = a * g * k := by
      obtain ⟨k, hk, hk_eq⟩ := hx
      refine ⟨g⁻¹ * k * g, ?_, ?_⟩
      · exact Subgroup.Normal.conj_mem' (inferInstance : K.Normal) k hk g
      · have hx_eq : x = a * k * g := by
          calc x = (x * g⁻¹) * g := by group
            _ = a * k * g := by rw [hk_eq]
        rw [hx_eq]; group
    rw [if_pos hx, if_pos hx']
  · have hx' : ¬ ∃ k ∈ K, x = a * g * k := by
      rintro ⟨k, hk, hk_eq⟩
      apply hx
      refine ⟨g * k * g⁻¹, ?_, ?_⟩
      · exact Subgroup.Normal.conj_mem (inferInstance : K.Normal) k hk g
      · rw [hk_eq]; group
    rw [if_neg hx, if_neg hx']

def IsHidingSet (K : Subgroup G) (Ψ : G → G → ℂ) : Prop :=
  (∀ g, inner (Ψ g) (Ψ g) = 1) ∧
  (∀ g₁ g₂, g₁⁻¹ * g₂ ∈ K → Ψ g₁ = Ψ g₂) ∧
  (∀ g₁ g₂, g₁⁻¹ * g₂ ∉ K → inner (Ψ g₁) (Ψ g₂) = 0)

theorem inner_eq_zero_of_disjoint {ψ φ : G → ℂ}
    (h : ∀ x, ψ x = 0 ∨ φ x = 0) : inner ψ φ = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  rcases h x with hx | hx <;> simp [hx]

theorem cosetState_inner_eq_zero (K : Subgroup G) {a b : G} (h : a⁻¹ * b ∉ K) (c : ℂ) :
    inner (cosetState K a c) (cosetState K b c) = 0 := by
  apply inner_eq_zero_of_disjoint
  intro x
  by_cases hxa : ∃ k ∈ K, x = a * k
  · right
    have hxb : ¬ ∃ k ∈ K, x = b * k := by
      rintro ⟨l, hl, hl_eq⟩
      apply h
      obtain ⟨k, hk, hk_eq⟩ := hxa
      have h1 : a * k = b * l := by rw [← hk_eq, ← hl_eq]
      have h2 : k = a⁻¹ * b * l := by
        calc k = a⁻¹ * (a * k) := by group
          _ = a⁻¹ * (b * l) := by rw [h1]
          _ = a⁻¹ * b * l := by group
      have h3 : a⁻¹ * b = k * l⁻¹ := by rw [h2]; group
      rw [h3]
      exact K.mul_mem hk (K.inv_mem hl)
    simp only [cosetState]
    rw [if_neg hxb]
  · left
    simp only [cosetState]
    rw [if_neg hxa]

theorem hidingSet_of_cosetState (K : Subgroup G) [K.Normal] (φ : G ≃* G)
    (hφ : ∀ x, x ∈ K ↔ φ x ∈ K) (a : G) (c : ℂ)
    (hunit : inner (cosetState K a c) (cosetState K a c) = 1) :
    IsHidingSet K (fun g => rightAct (φ g) (cosetState K a c)) := by
  refine ⟨fun g => ?_, ?_, ?_⟩
  · rw [inner_rightAct, hunit]
  · intro g₁ g₂ h
    change rightAct (φ g₁) (cosetState K a c) = rightAct (φ g₂) (cosetState K a c)
    rw [rightAct_cosetState, rightAct_cosetState]
    apply cosetState_congr
    have heq : (a * φ g₁)⁻¹ * (a * φ g₂) = φ (g₁⁻¹ * g₂) := by
      rw [map_mul, map_inv]; group
    rw [heq]
    exact (hφ _).mp h
  · intro g₁ g₂ h
    change inner (rightAct (φ g₁) (cosetState K a c)) (rightAct (φ g₂) (cosetState K a c)) = 0
    rw [rightAct_cosetState, rightAct_cosetState]
    apply cosetState_inner_eq_zero
    intro hconj
    apply h
    have heq : (a * φ g₁)⁻¹ * (a * φ g₂) = φ (g₁⁻¹ * g₂) := by
      rw [map_mul, map_inv]; group
    have hmem : φ (g₁⁻¹ * g₂) ∈ K := by rw [← heq]; exact hconj
    exact (hφ _).mpr hmem

noncomputable def cosetEquiv (K : Subgroup G) (a : G) :
    K ≃ {x : G // ∃ k ∈ K, x = a * k} := by
  classical
  refine
    { toFun := fun k => ⟨a * k.1, k.1, k.2, rfl⟩
      invFun := fun x => ⟨a⁻¹ * x.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · obtain ⟨k, hk, hk_eq⟩ := x.2
    rw [hk_eq]
    simpa using hk
  · intro k
    apply Subtype.ext
    show a⁻¹ * (a * k.1) = k.1
    group
  · intro x
    apply Subtype.ext
    change a * (a⁻¹ * x.1) = x.1
    obtain ⟨k, hk, hk_eq⟩ := x.2
    rw [hk_eq]
    show a * (a⁻¹ * (a * k)) = a * k
    group

theorem card_coset (K : Subgroup G) (a : G) :
    Nat.card {x : G // ∃ k ∈ K, x = a * k} = Nat.card K :=
  (Nat.card_congr (cosetEquiv K a)).symm

theorem inner_cosetState_self (K : Subgroup G) (a : G) (c : ℂ) :
    inner (cosetState K a c) (cosetState K a c) = (Nat.card K : ℂ) * (c * star c) := by
  classical
  simp only [inner, cosetState]
  have hcongr : ∀ x : G,
      (if ∃ k ∈ K, x = a * k then c else 0) * star (if ∃ k ∈ K, x = a * k then c else 0)
        = if ∃ k ∈ K, x = a * k then c * star c else 0 := by
    intro x
    by_cases hx : ∃ k ∈ K, x = a * k <;> simp [hx]
  rw [Finset.sum_congr rfl (fun x _ => hcongr x)]
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.univ.filter (fun x : G => ∃ k ∈ K, x = a * k)).card = Nat.card K := by
    rw [← Fintype.card_subtype (fun x : G => ∃ k ∈ K, x = a * k)]
    rw [← Nat.card_eq_fintype_card]
    exact card_coset K a
  rw [hcard]

theorem inner_cosetState_self_sqrt (K : Subgroup G) (a : G) :
    inner (cosetState K a (((Real.sqrt (Nat.card K) : ℂ))⁻¹))
      (cosetState K a (((Real.sqrt (Nat.card K) : ℂ))⁻¹)) = 1 := by
  classical
  have hne : Nat.card K ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hcard : (Nat.card K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hne
  rw [inner_cosetState_self]
  have hsq : ((Real.sqrt (Nat.card K) : ℂ)) * ((Real.sqrt (Nat.card K) : ℂ))
      = (Nat.card K : ℂ) := by
    have h := congrArg (fun r : ℝ => (r : ℂ))
      (Real.sq_sqrt (Nat.cast_nonneg (Nat.card K)))
    push_cast at h
    rwa [pow_two] at h
  have hc : star (((Real.sqrt (Nat.card K) : ℂ))⁻¹)
      = ((Real.sqrt (Nat.card K) : ℂ))⁻¹ := by simp
  have hcc : ((Real.sqrt (Nat.card K) : ℂ))⁻¹ * ((Real.sqrt (Nat.card K) : ℂ))⁻¹
      = (Nat.card K : ℂ)⁻¹ := by
    rw [← mul_inv, hsq]
  rw [hc, hcc, mul_inv_cancel₀ hcard]

theorem hidingSet_uniform (K : Subgroup G) [K.Normal] (φ : G ≃* G)
    (hφ : ∀ x, x ∈ K ↔ φ x ∈ K) (a : G) :
    IsHidingSet K
      (fun g => rightAct (φ g) (cosetState K a (((Real.sqrt (Nat.card K) : ℂ))⁻¹))) :=
  hidingSet_of_cosetState K φ hφ a _ (inner_cosetState_self_sqrt K a)

theorem rightAct_cosetState_of_mem (K : Subgroup G) [K.Normal] {g : G} (hg : g ∈ K)
    (a : G) (c : ℂ) : rightAct g (cosetState K a c) = cosetState K a c := by
  rw [rightAct_cosetState]
  apply cosetState_congr
  have h : (a * g)⁻¹ * a = g⁻¹ := by group
  rw [h]
  exact K.inv_mem hg

end Qatlib.Papers.NilpotentHSP07.MainResults
