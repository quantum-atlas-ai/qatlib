/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JonesPoly06.MainResults.AmplitudeApprox
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped ComplexInnerProductSpace

namespace Qatlib.Papers.JonesPoly06.MainResults

def wordEval {α M : Type*} [Monoid M] (g : α → M) : List α → M
  | [] => 1
  | a :: l => g a * wordEval g l

theorem wordEval_append {α M : Type*} [Monoid M] (g : α → M) :
    ∀ l₁ l₂ : List α, wordEval g (l₁ ++ l₂) = wordEval g l₁ * wordEval g l₂
  | [], l₂ => by simp [wordEval]
  | a :: l₁, l₂ => by
      simp only [List.cons_append, wordEval]
      rw [wordEval_append g l₁ l₂, mul_assoc]

theorem wordEval_singleton {α M : Type*} [Monoid M] (g : α → M) (a : α) :
    wordEval g [a] = g a := by simp [wordEval]

theorem list_sum_le_length_mul {l : List ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x ∈ l, x ≤ c) : l.sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.sum_cons, List.length_cons]
      have ha : a ≤ c := h a (by simp)
      have htail : ∀ x ∈ l, x ≤ c := fun x hx => h x (by simp [hx])
      have hih := ih htail
      have hlen : (0 : ℝ) ≤ (l.length : ℝ) := by positivity
      push_cast
      nlinarith

theorem compile_total_error {A : Type*} [SeminormedRing A] [NormOneClass A]
    (L L' : List A) (hlen : L.length = L'.length) (m : ℕ)
    (hm : L.length = m) (ε' : ℝ) (hε' : 0 ≤ ε')
    (hU : ∀ a ∈ L, ‖a‖ ≤ 1) (hU' : ∀ a ∈ L', ‖a‖ ≤ 1)
    (hgate : ∀ x ∈ L.zipWith (fun a b => ‖a - b‖) L', x ≤ ε') :
    ‖L.prod - L'.prod‖ ≤ (m : ℝ) * ε' := by
  have htel := list_prod_sub_prod_le L L' hlen hU hU'
  have hsum := list_sum_le_length_mul hε' hgate
  have hlen' : (L.zipWith (fun a b => ‖a - b‖) L').length = m := by
    rw [List.length_zipWith, hlen, min_self, ← hlen, hm]
  calc ‖L.prod - L'.prod‖
      ≤ (L.zipWith (fun a b => ‖a - b‖) L').sum := htel
    _ ≤ ((L.zipWith (fun a b => ‖a - b‖) L').length : ℝ) * ε' := hsum
    _ = (m : ℝ) * ε' := by rw [hlen']

theorem plat_amplitude_le_one {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (U : E →L[ℂ] E) (hU : ∀ x, ‖U x‖ = ‖x‖)
    (t : E) (ht : ‖t‖ = 1) :
    ‖inner ℂ t (U t)‖ ^ 2 ≤ 1 := by
  have h1 : ‖inner ℂ t (U t)‖ ≤ ‖t‖ * ‖U t‖ := norm_inner_le_norm t (U t)
  rw [hU t, ht, one_mul] at h1
  nlinarith [norm_nonneg (inner ℂ t (U t))]

theorem normalized_jones_mem {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (U : E →L[ℂ] E) (hU : ∀ x, ‖U x‖ = ‖x‖)
    (t : E) (ht : ‖t‖ = 1) :
    ‖inner ℂ t (U t)‖ ^ 2 ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨sq_nonneg _, plat_amplitude_le_one U hU t ht⟩

theorem theorem71_reduction {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [Nontrivial E] (L L' : List (E →L[ℂ] E))
    (hlen : L.length = L'.length)
    (hU : ∀ W ∈ L, ∀ x, ‖W x‖ = ‖x‖)
    (hU' : ∀ W ∈ L', ∀ x, ‖W x‖ = ‖x‖)
    (φ ψ : E) (hφ : ‖φ‖ = 1) (hψ : ‖ψ‖ = 1)
    (ε : ℝ) (hsum : (L.zipWith (fun a b => ‖a - b‖) L').sum ≤ ε) (hε : ε ≤ 1) :
    |‖inner ℂ φ (L.prod ψ)‖ ^ 2 - ‖inner ℂ φ (L'.prod ψ)‖ ^ 2| ≤ ε :=
  compiled_amplitude_bound L L' hlen hU hU' φ ψ hφ hψ ε hsum hε

end Qatlib.Papers.JonesPoly06.MainResults
