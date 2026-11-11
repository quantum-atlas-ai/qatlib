/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Shared Phases

The four actual local phases, sampled once per input and shared by both copies.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk

/-- The four actual local phases, sampled once per input and shared by both copies. -/
def fourthPhase (k : Fin 4) : ℂ := Complex.I ^ k.val

/-- The uniform finite average over every complete fourth-root phase assignment. -/
def phaseMean {A : Type*} [Fintype A] (f : (A → Fin 4) → ℂ) : ℂ :=
  ∑ ω : A → Fin 4, (∏ _ : A, (1 / 4 : ℂ)) * f ω

/-- Independence factors the actual complete phase average; it does not resample phases between copies. -/
theorem phaseMean_prod {A : Type*} [Fintype A] (f : A → Fin 4 → ℂ) :
    phaseMean (fun ω => ∏ x, f x (ω x)) =
      ∏ x, (∑ k : Fin 4, (1 / 4 : ℂ) * f x k) := by
  unfold phaseMean
  simp_rw [← Finset.prod_mul_distrib]
  exact (Finset.prod_univ_sum (t := fun _ : A => (Finset.univ : Finset (Fin 4)))
    (f := fun x k => (1 / 4 : ℂ) * f x k)).symm

/-- The exact local degree-two character orthogonality distinguishes fourth roots from signs. -/
theorem fourthPhase_local_moment (a b c d : Bool) :
    (∑ k : Fin 4, (1 / 4 : ℂ) *
      ((if a then fourthPhase k else 1) * (if b then fourthPhase k else 1) *
        (if c then star (fourthPhase k) else 1) *
          (if d then star (fourthPhase k) else 1))) =
      if a.toNat + b.toNat = c.toNat + d.toNat then 1 else 0 := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [fourthPhase, Fin.sum_univ_succ, pow_succ, Complex.I_mul_I]

/-- Equality of the two address multisets is exactly equality of every local multiplicity. -/
theorem paired_addresses_iff {A : Type*} [DecidableEq A] (x y u v : A) :
    (∀ i, (if i = x then 1 else 0 : ℕ) + (if i = y then 1 else 0) =
      (if i = u then 1 else 0) + (if i = v then 1 else 0)) ↔
      (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  constructor
  · intro h
    by_cases hx : x = u
    · subst u
      have hy : y = v := by
        by_contra hn
        have hh := h y
        by_cases he : y = x <;> simp_all
      exact Or.inl ⟨rfl, hy⟩
    · have hv : x = v := by
        by_contra hn
        have hh := h x
        by_cases he : x = y <;> simp_all
      subst v
      have hy : y = u := by
        by_contra hn
        have hh := h y
        by_cases he : y = x <;> simp_all
      exact Or.inr ⟨rfl, hy⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) i
    · rfl
    · omega

/-- The actual shared-phase fourth moment is one precisely for paired addresses and zero otherwise. -/
theorem fourthPhase_shared_moment {A : Type*} [Fintype A] [DecidableEq A]
    (x y u v : A) :
    phaseMean (fun ω => fourthPhase (ω x) * fourthPhase (ω y) *
      star (fourthPhase (ω u)) * star (fourthPhase (ω v))) =
      if (x = u ∧ y = v) ∨ (x = v ∧ y = u) then 1 else 0 := by
  let f : A → Fin 4 → ℂ := fun i k =>
    (if i = x then fourthPhase k else 1) *
      (if i = y then fourthPhase k else 1) *
        (if i = u then star (fourthPhase k) else 1) *
          (if i = v then star (fourthPhase k) else 1)
  have hf (ω : A → Fin 4) : (∏ i, f i (ω i)) =
      fourthPhase (ω x) * fourthPhase (ω y) *
        star (fourthPhase (ω u)) * star (fourthPhase (ω v)) := by
    simp only [f, Finset.prod_mul_distrib]
    simp only [Fintype.prod_ite_eq']
  have hm : phaseMean (fun (ω : A → Fin 4) => fourthPhase (ω x) * fourthPhase (ω y) *
      star (fourthPhase (ω u)) * star (fourthPhase (ω v))) =
        phaseMean (fun (ω : A → Fin 4) => ∏ i, f i (ω i)) := by
    apply congrArg (@phaseMean A _)
    funext ω
    exact (hf ω).symm
  rw [hm, phaseMean_prod f]
  have localFactor (i : A) : (∑ k : Fin 4, (1 / 4 : ℂ) * f i k) =
      if (if i = x then 1 else 0 : ℕ) + (if i = y then 1 else 0) =
        (if i = u then 1 else 0) + (if i = v then 1 else 0) then 1 else 0 := by
    have hnat (p : Prop) [Decidable p] : (decide p).toNat = (if p then 1 else 0 : ℕ) := by
      by_cases hp : p <;> simp [hp]
    simpa [f, hnat] using fourthPhase_local_moment (decide (i = x))
      (decide (i = y)) (decide (i = u)) (decide (i = v))
  simp_rw [localFactor]
  by_cases h : ∀ i, (if i = x then 1 else 0 : ℕ) + (if i = y then 1 else 0) =
    (if i = u then 1 else 0) + (if i = v then 1 else 0)
  · have hp := (paired_addresses_iff x y u v).mp h
    simp [h, hp]
  · have hp : ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u)) := by
      exact fun hp => h ((paired_addresses_iff x y u v).mpr hp)
    rw [ite_eq_right hp]
    push Not at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
