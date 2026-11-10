/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Order.PiLex
import Mathlib.Tactic

import Qatlib.Concepts.QcaDynamics.ScalarNoGo.LocalKernel

set_option autoImplicit false

namespace Qatlib.Concepts.QcaDynamics.ScalarNoGo

open Finset
open scoped BigOperators
open Qatlib.Concepts.QcaDynamics.ScalarNoGo

variable {V : Type*}

theorem noGo_weights [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]
    (A : Weights V) (hunit : Unitary A) :
    ∃ e₀ : V, A.weight e₀ ≠ 0 ∧ (∀ e, A.weight e ≠ 0 → e = e₀) ∧
      ‖A.weight e₀‖ = 1 := by
  obtain ⟨hdiag, hoff⟩ := hunit

  have hex : ∃ e, A.weight e ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : (∑ e ∈ A.neighborhood, A.weight e * star (A.weight e)) = 0 := by
      apply Finset.sum_eq_zero
      intro e _
      simp [h e]
    rw [h0] at hdiag
    exact zero_ne_one hdiag
  obtain ⟨e0, he0w⟩ := hex

  let E' := A.neighborhood.filter fun e => A.weight e ≠ 0
  have hE'ne : E'.Nonempty := ⟨e0, Finset.mem_filter.mpr ⟨A.support e0 he0w, he0w⟩⟩

  let k := E'.min' hE'ne
  let j := E'.max' hE'ne
  have hk' : k ∈ E' := Finset.min'_mem E' hE'ne
  have hj' : j ∈ E' := Finset.max'_mem E' hE'ne
  have hkE : k ∈ A.neighborhood := (Finset.mem_filter.mp hk').1
  have hjE : j ∈ A.neighborhood := (Finset.mem_filter.mp hj').1
  have hwk : A.weight k ≠ 0 := (Finset.mem_filter.mp hk').2
  have hwj : A.weight j ≠ 0 := (Finset.mem_filter.mp hj').2
  have hmin : ∀ x ∈ E', k ≤ x := fun x hx => Finset.min'_le E' x hx
  have hmax : ∀ x ∈ E', x ≤ j := fun x hx => Finset.le_max' E' x hx

  have hjk : j = k := by
    by_contra hne
    have hd : j - k ≠ 0 := sub_ne_zero.mpr hne
    have hoffd := hoff (j - k) hd
    have hsum : (∑ e ∈ A.neighborhood,
        A.weight e * star (A.weight (e - (j - k)))) = A.weight j * star (A.weight k) := by
      have hkey : j - (j - k) = k := by abel
      calc (∑ e ∈ A.neighborhood, A.weight e * star (A.weight (e - (j - k))))
          = A.weight j * star (A.weight (j - (j - k))) := by
            apply Finset.sum_eq_single j
            · intro x hxE hxj
              by_cases hxw : A.weight x = 0
              · simp [hxw]
              · have hx' : x ∈ E' := Finset.mem_filter.mpr ⟨hxE, hxw⟩
                have hxle : x ≤ j := hmax x hx'
                have hxlt : x < j := lt_of_le_of_ne hxle hxj

                have hlt1 : x - j < 0 := by
                  have h := add_lt_add_right hxlt (-j)
                  simpa [sub_eq_add_neg] using h
                have hlt2 : x - (j - k) < k := by
                  have h := add_lt_add_right hlt1 k
                  have heq : x - (j - k) = (x - j) + k := by abel
                  rw [heq]
                  simpa using h
                have hzero : A.weight (x - (j - k)) = 0 := by
                  by_contra hc
                  have hx'' : x - (j - k) ∈ E' :=
                    Finset.mem_filter.mpr ⟨A.support (x - (j - k)) hc, hc⟩
                  exact absurd (hmin _ hx'') (not_le.mpr hlt2)
                simp [hzero]
            · intro hjE'
              exact absurd hjE hjE'
        _ = A.weight j * star (A.weight k) := by rw [hkey]
    rw [hsum] at hoffd
    have hstar : star (A.weight k) ≠ 0 := star_ne_zero.mpr hwk
    have hwj0 : A.weight j = 0 := by
      rcases mul_eq_zero.mp hoffd with h | h
      · exact h
      · exact absurd h hstar
    exact hwj hwj0

  refine ⟨k, hwk, ?_, ?_⟩
  · intro e he
    have he' : e ∈ E' := Finset.mem_filter.mpr ⟨A.support e he, he⟩
    have h1 : e ≤ j := hmax e he'
    rw [hjk] at h1
    exact le_antisymm h1 (hmin e he')
  · have hdiag' : (∑ e ∈ A.neighborhood,
        A.weight e * star (A.weight e)) = A.weight k * star (A.weight k) := by
      apply Finset.sum_eq_single k
      · intro x hxE hxk
        by_cases hxw : A.weight x = 0
        · simp [hxw]
        · have hx' : x ∈ E' := Finset.mem_filter.mpr ⟨hxE, hxw⟩
          have h1 : x ≤ j := hmax x hx'
          rw [hjk] at h1
          have hxk' : x = k := le_antisymm h1 (hmin x hx')
          exact absurd hxk' hxk
      · intro hkE'
        exact absurd hkE hkE'
    rw [hdiag'] at hdiag
    have hmul : A.weight k * star (A.weight k) = 1 := hdiag
    have hmul2 : A.weight k * star (A.weight k) = ((‖A.weight k‖ ^ 2 : ℝ) : ℂ) := by
      show A.weight k * (starRingEnd ℂ) (A.weight k) = ((‖A.weight k‖ ^ 2 : ℝ) : ℂ)
      rw [Complex.ofReal_pow]
      exact Complex.mul_conj' (A.weight k)
    have hc : ((‖A.weight k‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← hmul2]
      exact hmul
    have hsq : ‖A.weight k‖ ^ 2 = 1 := by
      exact_mod_cast hc
    rcases sq_eq_one_iff.mp hsq with h | h
    · exact h
    · have := norm_nonneg (A.weight k)
      linarith

theorem noGo_theorem [AddCommGroup V] [LinearOrder V] [IsOrderedAddMonoid V]
    (A : Weights V) (hunit : Unitary A) :
    ∃ (e₀ : V) (c : ℂ), A.weight e₀ = c ∧ ‖c‖ = 1 ∧
      (∀ e, A.weight e ≠ 0 → e = e₀) ∧ evolveByTranslation A e₀ c := by
  obtain ⟨e₀, hne, honly, hnorm⟩ := noGo_weights A hunit
  refine ⟨e₀, A.weight e₀, rfl, hnorm, honly, ?_⟩
  intro φ x
  show (∑ e ∈ A.neighborhood, A.weight e * φ (x + e)) = A.weight e₀ * φ (x + e₀)
  rw [Finset.sum_eq_single e₀]
  · intro b _ hbne
    have hbw : A.weight b = 0 := by
      by_contra h
      exact hbne (honly b h)
    simp [hbw]
  · intro hmem
    exact absurd (A.support e₀ hne) hmem

theorem noGo_oneDimension (A : Weights ℤ) (hunit : Unitary A) :
    ∃ (e₀ : ℤ) (c : ℂ), A.weight e₀ = c ∧ ‖c‖ = 1 ∧
      (∀ e, A.weight e ≠ 0 → e = e₀) ∧ evolveByTranslation A e₀ c :=
  noGo_theorem A hunit

noncomputable instance instIsOrderedAddMonoidLexPi (d : ℕ) :
    IsOrderedAddMonoid (Lex (Fin d → ℤ)) where
  add_le_add_left a b h c := by
    rw [le_iff_lt_or_eq] at h ⊢
    rcases h with h | h
    · left
      obtain ⟨i, hi, hlt⟩ := h
      refine ⟨i, ?_, ?_⟩
      · intro j hj
        have hji : a j = b j := hi j hj
        show a j + c j = b j + c j
        rw [hji]
      · show a i + c i < b i + c i
        linarith [hlt]
    · right
      rw [h]

theorem noGo_finDimension (d : ℕ) (A : Weights (Lex (Fin d → ℤ))) (hunit : Unitary A) :
    ∃ (e₀ : Lex (Fin d → ℤ)) (c : ℂ), A.weight e₀ = c ∧ ‖c‖ = 1 ∧
      (∀ e, A.weight e ≠ 0 → e = e₀) ∧ evolveByTranslation A e₀ c :=
  @noGo_theorem (Lex (Fin d → ℤ)) _ _ (instIsOrderedAddMonoidLexPi d) A hunit

noncomputable def weightedTranslation [DecidableEq V] (e₀ : V) (c : ℂ) : Weights V where
  neighborhood := {e₀}
  weight := fun e => if e = e₀ then c else 0
  support := by
    intro v hv
    by_contra h
    rw [Finset.mem_singleton] at h
    exact hv (if_neg h)

theorem weightedTranslation_isUnitary [AddCommGroup V] [DecidableEq V] (e₀ : V) {c : ℂ}
    (hc : ‖c‖ = 1) :
    Unitary (weightedTranslation e₀ c) := by
  constructor
  · show (∑ e ∈ ({e₀} : Finset V),
        (if e = e₀ then c else 0) * star (if e = e₀ then c else 0)) = 1
    rw [Finset.sum_singleton]
    simp only [if_true]
    have hmul : c * star c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
      show c * (starRingEnd ℂ) c = ((‖c‖ ^ 2 : ℝ) : ℂ)
      rw [Complex.ofReal_pow]
      exact Complex.mul_conj' c
    rw [hmul, hc]
    norm_num
  · intro d hd
    show (∑ e ∈ ({e₀} : Finset V),
        (if e = e₀ then c else 0) * star (if e - d = e₀ then c else 0)) = 0
    rw [Finset.sum_singleton]
    have hsub : e₀ - d ≠ e₀ := by
      intro h
      apply hd
      have := congrArg (· + d) h
      simpa [add_comm, add_left_comm, add_assoc] using this
    simp [hsub]

theorem weightedTranslation_evolution [AddCommGroup V] [DecidableEq V] (e₀ : V) (c : ℂ) :
    evolveByTranslation (weightedTranslation e₀ c) e₀ c := by
  intro φ x
  show (∑ e ∈ ({e₀} : Finset V), (if e = e₀ then c else 0) * φ (x + e))
      = c * φ (x + e₀)
  rw [Finset.sum_singleton]
  simp

end Qatlib.Concepts.QcaDynamics.ScalarNoGo
