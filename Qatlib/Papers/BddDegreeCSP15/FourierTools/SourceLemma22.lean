/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BddDegreeCSP15.FourierTools.SourceModel

@[expose] public section


/-!
# BddDegreeCSP15 — source Lemma 2.2 (Block `FourierTools`)

Fixed source: arXiv:1505.03424v2, Lemma 2.2 (p. 5): for a predicate
`P : {±1}^r → {0,1}`, `r ≥ 2`, depending on every coordinate,
`Var[(∂ᵢP)(x)] ≥ 2^{−r}/16 = Ω(2^{−r})` for every `i`.


-/

set_option autoImplicit false

namespace Qatlib.Papers.BddDegreeCSP15.FourierTools

open scoped BigOperators
open Finset

/-! ## §A. Auxiliary analysis -/

/-- A pointwise upper bound bounds the uniform average. -/
theorem avg_le_const {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (M : ℝ) (h : ∀ x, f x ≤ M) : avg f ≤ M := by
  have hN : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [avg_def, div_le_iff₀ hN]
  calc ∑ x, f x ≤ ∑ _x : α, M := Finset.sum_le_sum (fun x _ => h x)
    _ = M * (Fintype.card α : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- A pointwise lower bound bounds the uniform average from below. -/
theorem const_le_avg {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (m : ℝ) (h : ∀ x, m ≤ f x) : m ≤ avg f := by
  have hN : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rw [avg_def, le_div_iff₀ hN]
  calc m * (Fintype.card α : ℝ) = ∑ _x : α, m := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ ∑ x, f x := Finset.sum_le_sum (fun x _ => h x)

/-- The variance is the average squared deviation written as a quotient. -/
theorem variance_eq_sum {α : Type*} [Fintype α] (f : α → ℝ) :
    variance f = (∑ x, (f x - avg f) ^ 2) / (Fintype.card α : ℝ) := by
  rw [variance_def, avg_def]

/-- If `a,b ∈ {−½,0,½}`, `b ≤ a` and `a ≠ b`, then `a − b ≥ ½`. -/
theorem half_le_sub_of_three_values {a b : ℝ}
    (ha : a = -(1/2) ∨ a = 0 ∨ a = 1/2)
    (hb : b = -(1/2) ∨ b = 0 ∨ b = 1/2)
    (hba : b ≤ a) (hne : a ≠ b) : (1/2 : ℝ) ≤ a - b := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first
      | linarith
      | (exfalso; exact hne rfl)

/-- On a finite nonempty uniform domain, a nonconstant function taking values in `{−½,0,½}` has
variance at least `(1/16)/N`. -/
theorem variance_lower_three_values {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (hvals : ∀ x, f x = -(1/2) ∨ f x = 0 ∨ f x = 1/2)
    (hne : ∃ x y, f x ≠ f y) :
    (1/16) / (Fintype.card α : ℝ) ≤ variance f := by
  have hcard_pos : (0 : ℝ) < (Fintype.card α : ℝ) := by
    exact_mod_cast Fintype.card_pos
  obtain ⟨xM, -, hxM⟩ :=
    Finset.exists_max_image (Finset.univ : Finset α) f Finset.univ_nonempty
  obtain ⟨xm, -, hxm⟩ :=
    Finset.exists_min_image (Finset.univ : Finset α) f Finset.univ_nonempty
  have hmM : f xm ≤ f xM := hxM xm (Finset.mem_univ xm)
  have hmμ : f xm ≤ avg f := const_le_avg f (f xm) (fun x => hxm x (Finset.mem_univ x))
  have hμM : avg f ≤ f xM := avg_le_const f (f xM) (fun x => hxM x (Finset.mem_univ x))
  have hne_maxmin : f xM ≠ f xm := by
    intro hEq
    obtain ⟨x, y, hxy⟩ := hne
    have hx : f x = f xm :=
      le_antisymm (hEq ▸ hxM x (Finset.mem_univ x)) (hxm x (Finset.mem_univ x))
    have hy : f y = f xm :=
      le_antisymm (hEq ▸ hxM y (Finset.mem_univ y)) (hxm y (Finset.mem_univ y))
    exact hxy (hx.trans hy.symm)
  have hrange : (1/2 : ℝ) ≤ f xM - f xm :=
    half_le_sub_of_three_values (hvals xM) (hvals xm) hmM hne_maxmin
  have hes : (1/4 : ℝ) ≤ f xM - avg f ∨ (1/4 : ℝ) ≤ avg f - f xm := by
    by_cases h : (1/4 : ℝ) ≤ f xM - avg f
    · exact Or.inl h
    · right
      push Not at h
      linarith
  have hS : (1/16 : ℝ) ≤ ∑ x, (f x - avg f) ^ 2 := by
    rcases hes with hdev | hdev
    · have hterm : (f xM - avg f) ^ 2 ≤ ∑ x, (f x - avg f) ^ 2 := by
        apply Finset.single_le_sum (s := Finset.univ) (a := xM)
        · intro x _; positivity
        · exact Finset.mem_univ xM
      have hdev2 : (1/4 : ℝ) ^ 2 ≤ (f xM - avg f) ^ 2 := by nlinarith [hdev]
      nlinarith [hterm, hdev2]
    · have hterm : (f xm - avg f) ^ 2 ≤ ∑ x, (f x - avg f) ^ 2 := by
        apply Finset.single_le_sum (s := Finset.univ) (a := xm)
        · intro x _; positivity
        · exact Finset.mem_univ xm
      have hdev2 : (1/4 : ℝ) ^ 2 ≤ (f xm - avg f) ^ 2 := by nlinarith [hdev]
      nlinarith [hterm, hdev2]
  have hinv : (0 : ℝ) ≤ (Fintype.card α : ℝ)⁻¹ := by positivity
  rw [variance_eq_sum]
  calc (1/16) / (Fintype.card α : ℝ) = (1/16) * (Fintype.card α : ℝ)⁻¹ := by ring
    _ ≤ (∑ x, (f x - avg f) ^ 2) * (Fintype.card α : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right hS hinv
    _ = (∑ x, (f x - avg f) ^ 2) / (Fintype.card α : ℝ) := by ring

/-- `∂ᵢP` of a `{0,1}`-valued predicate takes values in `{−½,0,½}`. -/
theorem deriv_val_cases {r : ℕ} (P : SignCube r → ℝ)
    (hP : ∀ x, P x = 0 ∨ P x = 1) (i : Fin r) (x : SignCube r) :
    deriv P i x = -(1/2) ∨ deriv P i x = 0 ∨ deriv P i x = 1/2 := by
  unfold deriv
  rcases hP (setCoord x i true) with h1 | h1 <;>
    rcases hP (setCoord x i false) with h0 | h0 <;>
    rw [h1, h0] <;> norm_num

/-- At a point where `P` genuinely depends on coordinate `i`, the derivative is nonzero. -/
theorem deriv_ne_zero_of_dep {r : ℕ} (P : SignCube r → ℝ) (i : Fin r) {x : SignCube r}
    (h : P (setCoord x i true) ≠ P (setCoord x i false)) : deriv P i x ≠ 0 := by
  unfold deriv
  intro hc
  apply h
  have h2 : P (setCoord x i true) - P (setCoord x i false) = 0 := by linarith
  exact sub_eq_zero.mp h2

/-- If the derivative `∂ᵢP` is a nonzero constant, then `P` depends only on coordinate `i`. -/
theorem deriv_const_depends_only_on {r : ℕ} (P : SignCube r → ℝ)
    (hP : ∀ x, P x = 0 ∨ P x = 1) (i : Fin r) {c : ℝ}
    (hconst : ∀ x, deriv P i x = c) (hc : c ≠ 0) :
    ∀ a b : SignCube r, a i = b i → P a = P b := by
  have hdiff : ∀ x, P (setCoord x i true) - P (setCoord x i false) = 2 * c := by
    intro x
    have := hconst x
    unfold deriv at this
    linarith
  have h2c : 2 * c = 1 ∨ 2 * c = -(1 : ℝ) := by
    have hval := hdiff (fun _ => false)
    have h1 := hP (setCoord (fun _ => false) i true)
    have h0 := hP (setCoord (fun _ => false) i false)
    rcases h1 with h1 | h1 <;> rcases h0 with h0 | h0
    · exfalso; apply hc; rw [h1, h0] at hval; linarith
    · right; rw [h1, h0] at hval; linarith
    · left; rw [h1, h0] at hval; linarith
    · exfalso; apply hc; rw [h1, h0] at hval; linarith
  have htrue : ∀ y, P (setCoord y i true) = (if 2 * c = 1 then (1 : ℝ) else 0) := by
    intro y
    have hy := hdiff y
    rcases h2c with h2 | h2
    · rw [ite_eq_left h2]
      rcases hP (setCoord y i true) with h | h <;>
        rcases hP (setCoord y i false) with h' | h' <;> linarith
    · rw [ite_eq_right (by linarith)]
      rcases hP (setCoord y i true) with h | h <;>
        rcases hP (setCoord y i false) with h' | h' <;> linarith
  have hfalse : ∀ y, P (setCoord y i false) = (if 2 * c = 1 then (0 : ℝ) else 1) := by
    intro y
    have hy := hdiff y
    rcases h2c with h2 | h2
    · rw [ite_eq_left h2]
      rcases hP (setCoord y i true) with h | h <;>
        rcases hP (setCoord y i false) with h' | h' <;> linarith
    · rw [ite_eq_right (by linarith)]
      rcases hP (setCoord y i true) with h | h <;>
        rcases hP (setCoord y i false) with h' | h' <;> linarith
  intro a b hab
  have hbeq : b i = a i := by rw [hab]
  cases hbit : a i with
  | true =>
      have ha : a = setCoord a i true := by
        funext j
        by_cases hji : j = i
        · rw [hji, setCoord_self]; exact hbit
        · rw [setCoord_ne a i j true hji]
      have hbb : b = setCoord b i true := by
        funext j
        by_cases hji : j = i
        · rw [hji, setCoord_self]; exact hbeq.trans hbit
        · rw [setCoord_ne b i j true hji]
      rw [ha, hbb, htrue a, htrue b]
  | false =>
      have ha : a = setCoord a i false := by
        funext j
        by_cases hji : j = i
        · rw [hji, setCoord_self]; exact hbit
        · rw [setCoord_ne a i j false hji]
      have hbb : b = setCoord b i false := by
        funext j
        by_cases hji : j = i
        · rw [hji, setCoord_self]; exact hbeq.trans hbit
        · rw [setCoord_ne b i j false hji]
      rw [ha, hbb, hfalse a, hfalse b]

/-- Under dependence on every coordinate and `r ≥ 2`, `∂ᵢP` is nonconstant. -/
theorem deriv_nonconstant {r : ℕ} (hr : 2 ≤ r) (P : SignCube r → ℝ)
    (hP : ∀ x, P x = 0 ∨ P x = 1)
    (hdep : ∀ j : Fin r, ∃ x, P (setCoord x j true) ≠ P (setCoord x j false))
    (i : Fin r) : ∃ x y, deriv P i x ≠ deriv P i y := by
  by_contra hcon
  push Not at hcon
  obtain ⟨w, hw⟩ := hdep i
  have hw0 : deriv P i w ≠ 0 := deriv_ne_zero_of_dep P i hw
  have hcard : 1 < Fintype.card (Fin r) := by
    rw [Fintype.card_fin]; omega
  obtain ⟨j, hj⟩ := Fintype.exists_ne_of_one_lt_card hcard i
  have hdeponly : ∀ a b : SignCube r, a i = b i → P a = P b :=
    deriv_const_depends_only_on P hP i (fun x => hcon x w) hw0
  obtain ⟨w2, hw2⟩ := hdep j
  apply hw2
  apply hdeponly
  rw [setCoord_ne w2 j i true (Ne.symm hj), setCoord_ne w2 j i false (Ne.symm hj)]

/-! ## §B. Source Lemma 2.2 -/

/-- **Fixed arXiv:1505.03424v2, Lemma 2.2 (p. 5).**  For a predicate
`P : {±1}^r → {0,1}`, `r ≥ 2`, depending on every coordinate,
`Var[(∂ᵢP)(x)] ≥ 2^{−r}/16 = Ω(2^{−r})` for every `i`. -/
theorem lemma_2_2_variance_deriv (r : ℕ) (hr : 2 ≤ r)
    (P : SignCube r → ℝ) (hP : ∀ x, P x = 0 ∨ P x = 1)
    (hdep : ∀ j : Fin r, ∃ x, P (setCoord x j true) ≠ P (setCoord x j false))
    (i : Fin r) :
    (1/16) / (2 : ℝ) ^ r ≤ variance (deriv P i) := by
  have hvals : ∀ x, deriv P i x = -(1/2) ∨ deriv P i x = 0 ∨ deriv P i x = 1/2 :=
    fun x => deriv_val_cases P hP i x
  have hne : ∃ x y, deriv P i x ≠ deriv P i y := deriv_nonconstant hr P hP hdep i
  have hmain := variance_lower_three_values (deriv P i) hvals hne
  have hcard : (Fintype.card (SignCube r) : ℝ) = (2 : ℝ) ^ r := by
    have h : Fintype.card (SignCube r) = 2 ^ r := by simp [SignCube]
    rw [h]; push_cast; ring
  rwa [hcard] at hmain

end Qatlib.Papers.BddDegreeCSP15.FourierTools
