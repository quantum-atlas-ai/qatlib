/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GameTree09.MainResults.Composition

/-!
# Operator norm bound for OR composition

This module proves the OR-composition norm estimate in the span-program development of
[Reichardt2009]. The rectangular matrix `orScale` duplicates and rescales the second column
block; its product with its conjugate transpose is diagonal.

Factoring `orComposedBlock` through this scaling matrix gives the squared operator-norm bound,
which specializes to the gate coefficients in `lemma_3_4_or`.

## Main statements

* `orComposedBlock_eq_mul`: Factorization of the composed OR block.
* `orScale_mul_conjTranspose`: The diagonal scaling Gram matrix.
* `orComposedBlock_norm_sq_le`: The general squared-norm inequality.
* `lemma_3_4_or`: The OR part of the source composition bound.

## References

* [Reichardt, 2009][Reichardt2009]
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Classical
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.GameTree09.MainResults

/-- The rectangular scaling matrix that preserves the first block and sends two copies of the
second block to weights `ε₁` and `ε₂`. -/
def orScale {α β : Type*} [DecidableEq α] [DecidableEq β] (ε₁ ε₂ : ℝ) :
    Matrix (α ⊕ β) (α ⊕ (β ⊕ β)) ℝ :=
  fun i j =>
    Sum.elim
      (fun a => Sum.elim (fun a' => if a = a' then 1 else 0) (fun _ => 0) j)
      (fun b => Sum.elim (fun _ => 0)
        (Sum.elim (fun b' => if b = b' then ε₁ else 0)
          (fun b' => if b = b' then ε₂ else 0)) j)
      i

/-- The diagonal function equal to one on the first summand and `ε₁² + ε₂²` on the second. -/
def orScaleDiag {α β : Type*} (ε₁ ε₂ : ℝ) : α ⊕ β → ℝ :=
  Sum.elim (fun _ => 1) (fun _ => ε₁ ^ 2 + ε₂ ^ 2)

/-- The first-to-first block of `orScale` is the identity matrix. -/
theorem orScale_apply_inl_inl {α β : Type*} [DecidableEq α] [DecidableEq β]
    (ε₁ ε₂ : ℝ) (a a' : α) :
    orScale (α := α) (β := β) ε₁ ε₂ (Sum.inl a) (Sum.inl a') =
      (if a = a' then 1 else 0) := rfl

/-- Entries from a first-summand row to either duplicated second-summand column are zero. -/
theorem orScale_apply_inl_inr {α β : Type*} [DecidableEq α] [DecidableEq β]
    (ε₁ ε₂ : ℝ) (a : α) (j : β ⊕ β) :
    orScale (α := α) (β := β) ε₁ ε₂ (Sum.inl a) (Sum.inr j) = 0 := rfl

/-- Entries from a second-summand row to a first-summand column are zero. -/
theorem orScale_apply_inr_inl {α β : Type*} [DecidableEq α] [DecidableEq β]
    (ε₁ ε₂ : ℝ) (b : β) (a : α) :
    orScale (α := α) (β := β) ε₁ ε₂ (Sum.inr b) (Sum.inl a) = 0 := rfl

/-- The block from the first copy of the second column summand to the second row summand is `ε₁`
times the identity. -/
theorem orScale_apply_inr_inr_inl {α β : Type*} [DecidableEq α] [DecidableEq β]
    (ε₁ ε₂ : ℝ) (b b' : β) :
    orScale (α := α) (β := β) ε₁ ε₂ (Sum.inr b) (Sum.inr (Sum.inl b')) =
      (if b = b' then ε₁ else 0) := rfl

/-- The block from the second copy of the second column summand to the second row summand is
`ε₂` times the identity. -/
theorem orScale_apply_inr_inr_inr {α β : Type*} [DecidableEq α] [DecidableEq β]
    (ε₁ ε₂ : ℝ) (b b' : β) :
    orScale (α := α) (β := β) ε₁ ε₂ (Sum.inr b) (Sum.inr (Sum.inr b')) =
      (if b = b' then ε₂ else 0) := rfl

/-- The scaling Gram diagonal is one on the first summand. -/
theorem orScaleDiag_apply_inl {α β : Type*} (ε₁ ε₂ : ℝ) (a : α) :
    orScaleDiag (α := α) (β := β) ε₁ ε₂ (Sum.inl a) = 1 := rfl

/-- The scaling Gram diagonal is `ε₁² + ε₂²` on the second summand. -/
theorem orScaleDiag_apply_inr {α β : Type*} (ε₁ ε₂ : ℝ) (b : β) :
    orScaleDiag (α := α) (β := β) ε₁ ε₂ (Sum.inr b) = ε₁ ^ 2 + ε₂ ^ 2 := rfl

/-- The composed OR block with first weight one factors as the source OR block multiplied by
`orScale`. See [Reichardt2009]. -/
theorem orComposedBlock_eq_mul {m α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (A : Matrix m α ℝ) (B : Matrix m β ℝ)
    (ε₁ ε₂ : ℝ) :
    orComposedBlock 1 ε₁ ε₂ A B = orSourceBlock A B * orScale ε₁ ε₂ := by
  ext i j
  rcases j with a | b | b
  · simp only [orComposedBlock, Matrix.mul_apply, Fintype.sum_sum_type, orSourceBlock,
      orScale, Sum.elim_inl, Sum.elim_inr]
    have hβ : (∑ b' : β, B i b' * (0 : ℝ)) = 0 :=
      Finset.sum_eq_zero (fun b' _ => mul_zero _)
    rw [hβ, add_zero]
    have hfun : ∀ a' : α, A i a' * (if a' = a then 1 else 0) =
        if a' = a then A i a' else 0 := by
      intro a'
      by_cases h : a' = a <;> simp [h]
    rw [Finset.sum_congr rfl (fun a' _ => hfun a'), Finset.sum_eq_single a]
    · simp
    · intro a' _ ha'
      rw [ite_eq_right ha']
    · intro hmem
      exact absurd (Finset.mem_univ a) hmem
  · simp only [orComposedBlock, Matrix.mul_apply, Fintype.sum_sum_type, orSourceBlock,
      orScale, Sum.elim_inl, Sum.elim_inr]
    rw [Finset.sum_eq_zero (fun a' _ => by simp), zero_add]
    have hfun : ∀ b' : β, B i b' * (if b' = b then ε₁ else 0) =
        if b' = b then B i b' * ε₁ else 0 := by
      intro b'
      by_cases h : b' = b <;> simp [h]
    rw [Finset.sum_congr rfl (fun b' _ => hfun b'), Finset.sum_eq_single b]
    · rw [ite_eq_left rfl, mul_comm]
    · intro b' _ hb'
      rw [ite_eq_right hb']
    · intro hmem
      exact absurd (Finset.mem_univ b) hmem
  · simp only [orComposedBlock, Matrix.mul_apply, Fintype.sum_sum_type, orSourceBlock,
      orScale, Sum.elim_inl, Sum.elim_inr]
    rw [Finset.sum_eq_zero (fun a' _ => by simp), zero_add]
    have hfun : ∀ b' : β, B i b' * (if b' = b then ε₂ else 0) =
        if b' = b then B i b' * ε₂ else 0 := by
      intro b'
      by_cases h : b' = b <;> simp [h]
    rw [Finset.sum_congr rfl (fun b' _ => hfun b'), Finset.sum_eq_single b]
    · rw [ite_eq_left rfl, mul_comm]
    · intro b' _ hb'
      rw [ite_eq_right hb']
    · intro hmem
      exact absurd (Finset.mem_univ b) hmem

/-- The scaling matrix multiplied by its conjugate transpose is the diagonal matrix defined by
`orScaleDiag`. See [Reichardt2009]. -/
theorem orScale_mul_conjTranspose {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (ε₁ ε₂ : ℝ) :
    orScale (α := α) (β := β) ε₁ ε₂ * (orScale (α := α) (β := β) ε₁ ε₂)ᴴ =
      Matrix.diagonal (orScaleDiag (α := α) (β := β) ε₁ ε₂) := by
  ext r r'
  rcases r with a | b <;> rcases r' with a' | b'
  all_goals
    simp only [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.conjTranspose_apply,
      star_trivial, orScale_apply_inl_inl, orScale_apply_inl_inr, orScale_apply_inr_inl,
      orScale_apply_inr_inr_inl, orScale_apply_inr_inr_inr, orScaleDiag_apply_inl,
      orScaleDiag_apply_inr, Matrix.diagonal_apply]
  · by_cases h : a = a'
    · subst h
      have hfun : ∀ c : α,
          (if a = c then (1 : ℝ) else 0) * (if a = c then 1 else 0) =
            if a = c then 1 else 0 := by
        intro c
        by_cases h2 : a = c <;> simp [h2]
      rw [Finset.sum_congr rfl (fun c _ => hfun c)]
      simp
    · have hfun : ∀ c : α,
          (if a = c then (1 : ℝ) else 0) * (if a' = c then 1 else 0) = 0 := by
        intro c
        by_cases h2 : a = c
        · have h3 : ¬ (a' = c) := fun h3 => h (h2.trans h3.symm)
          simp [h2, h3]
        · simp [h2]
      rw [Finset.sum_congr rfl (fun c _ => hfun c)]
      have hne : ¬ ((Sum.inl a : α ⊕ β) = Sum.inl a') := fun hh => h (Sum.inl.inj hh)
      simp [hne]
  · have hne : ¬ (Sum.inl a = Sum.inr b') := fun hh => by cases hh
    simp [hne]
  · have hne : ¬ (Sum.inr b = Sum.inl a') := fun hh => by cases hh
    simp [hne]
  · by_cases h : b = b'
    · subst h
      have h1 : ∀ c : β,
          (if b = c then (ε₁ : ℝ) else 0) * (if b = c then ε₁ else 0) =
            if b = c then ε₁ ^ 2 else 0 := by
        intro c
        by_cases h2 : b = c <;> simp [h2, sq]
      have h2 : ∀ c : β,
          (if b = c then (ε₂ : ℝ) else 0) * (if b = c then ε₂ else 0) =
            if b = c then ε₂ ^ 2 else 0 := by
        intro c
        by_cases h3 : b = c <;> simp [h3, sq]
      rw [Finset.sum_congr rfl (fun c _ => h1 c),
        Finset.sum_congr rfl (fun c _ => h2 c)]
      simp
    · have h1 : ∀ c : β,
          (if b = c then (ε₁ : ℝ) else 0) * (if b' = c then ε₁ else 0) = 0 := by
        intro c
        by_cases h2 : b = c
        · have h3 : ¬ (b' = c) := fun h3 => h (h2.trans h3.symm)
          simp [h2, h3]
        · simp [h2]
      have h2 : ∀ c : β,
          (if b = c then (ε₂ : ℝ) else 0) * (if b' = c then ε₂ else 0) = 0 := by
        intro c
        by_cases h3 : b = c
        · have h4 : ¬ (b' = c) := fun h4 => h (h3.trans h4.symm)
          simp [h3, h4]
        · simp [h3]
      rw [Finset.sum_congr rfl (fun c _ => h1 c),
        Finset.sum_congr rfl (fun c _ => h2 c)]
      have hne : ¬ ((Sum.inr b : α ⊕ β) = Sum.inr b') := fun hh => h (Sum.inr.inj hh)
      simp [hne]

/-- For nonnegative weights with squared sum at least one, the squared operator norm of
`orScale` is at most `ε₁² + ε₂²`. -/
theorem orScale_norm_sq_le {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] {ε₁ ε₂ : ℝ} (_hε₁ : 0 ≤ ε₁) (_hε₂ : 0 ≤ ε₂)
    (h : 1 ≤ ε₁ ^ 2 + ε₂ ^ 2) :
    ‖orScale (α := α) (β := β) ε₁ ε₂‖ ^ 2 ≤ ε₁ ^ 2 + ε₂ ^ 2 := by
  have hc0 : (0 : ℝ) ≤ ε₁ ^ 2 + ε₂ ^ 2 := le_trans zero_le_one h
  have hdiag : ‖orScale (α := α) (β := β) ε₁ ε₂ *
      (orScale (α := α) (β := β) ε₁ ε₂)ᴴ‖ ≤ ε₁ ^ 2 + ε₂ ^ 2 := by
    rw [orScale_mul_conjTranspose, Matrix.l2_opNorm_diagonal]
    rw [pi_norm_le_iff_of_nonneg hc0]
    intro i
    rcases i with a | b
    · simpa [orScaleDiag] using h
    · simp [orScaleDiag, Real.norm_eq_abs, abs_of_nonneg hc0]
  have hsq : ‖orScale (α := α) (β := β) ε₁ ε₂‖ *
      ‖orScale (α := α) (β := β) ε₁ ε₂‖ =
      ‖orScale (α := α) (β := β) ε₁ ε₂ *
        (orScale (α := α) (β := β) ε₁ ε₂)ᴴ‖ := by
    have h1 : ‖(orScale (α := α) (β := β) ε₁ ε₂)ᴴ‖ =
        ‖orScale (α := α) (β := β) ε₁ ε₂‖ :=
      Matrix.l2_opNorm_conjTranspose _
    have h2 : ‖((orScale (α := α) (β := β) ε₁ ε₂)ᴴ)ᴴ *
        (orScale (α := α) (β := β) ε₁ ε₂)ᴴ‖ =
        ‖(orScale (α := α) (β := β) ε₁ ε₂)ᴴ‖ *
          ‖(orScale (α := α) (β := β) ε₁ ε₂)ᴴ‖ :=
      Matrix.l2_opNorm_conjTranspose_mul_self _
    rw [Matrix.conjTranspose_conjTranspose] at h2
    rw [h2, h1]
  rw [pow_two, hsq]
  exact hdiag

/-- For nonnegative weights with squared sum at least one, the squared norm of the composed OR
block is at most their squared sum times the squared norm of the source block. -/
theorem orComposedBlock_norm_sq_le {m α β : Type*} [Fintype m]
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (A : Matrix m α ℝ) (B : Matrix m β ℝ) {ε₁ ε₂ : ℝ}
    (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) (h : 1 ≤ ε₁ ^ 2 + ε₂ ^ 2) :
    ‖orComposedBlock 1 ε₁ ε₂ A B‖ ^ 2 ≤
      (ε₁ ^ 2 + ε₂ ^ 2) * ‖orSourceBlock A B‖ ^ 2 := by
  have hR2 : ‖orScale (α := α) (β := β) ε₁ ε₂‖ ^ 2 ≤ ε₁ ^ 2 + ε₂ ^ 2 :=
    orScale_norm_sq_le (α := α) (β := β) hε₁ hε₂ h
  have hMN : ‖orComposedBlock 1 ε₁ ε₂ A B‖ ≤
      ‖orSourceBlock A B‖ * ‖orScale (α := α) (β := β) ε₁ ε₂‖ := by
    rw [orComposedBlock_eq_mul A B ε₁ ε₂]
    exact Matrix.l2_opNorm_mul (orSourceBlock A B) (orScale (α := α) (β := β) ε₁ ε₂)
  have hK : (0 : ℝ) ≤ ‖orSourceBlock A B‖ * ‖orScale (α := α) (β := β) ε₁ ε₂‖ := by
    positivity
  have hMK : ‖orComposedBlock 1 ε₁ ε₂ A B‖ ^ 2 ≤
      (‖orSourceBlock A B‖ * ‖orScale (α := α) (β := β) ε₁ ε₂‖) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_le_mul hMN hMN (norm_nonneg _) hK
  calc ‖orComposedBlock 1 ε₁ ε₂ A B‖ ^ 2
      ≤ (‖orSourceBlock A B‖ * ‖orScale (α := α) (β := β) ε₁ ε₂‖) ^ 2 := hMK
    _ = ‖orSourceBlock A B‖ ^ 2 * ‖orScale (α := α) (β := β) ε₁ ε₂‖ ^ 2 := by
        ring
    _ ≤ ‖orSourceBlock A B‖ ^ 2 * (ε₁ ^ 2 + ε₂ ^ 2) :=
        mul_le_mul_of_nonneg_left hR2 (by positivity)
    _ = (ε₁ ^ 2 + ε₂ ^ 2) * ‖orSourceBlock A B‖ ^ 2 := by ring

/-- For nonnegative source matrices and positive child weights, the squared norm of the
OR-composed block is bounded by `(√(s 0) + √(s 1)) / √(s 0 + s 1)` times the squared
source-block norm. See [Reichardt2009]. -/
theorem lemma_3_4_or {m α β : Type*} [Fintype m] [DecidableEq m]
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (A : Matrix m α ℝ) (B : Matrix m β ℝ) (s : Fin 2 → ℝ)
    (_hA : ∀ i j, 0 ≤ A i j) (_hB : ∀ i j, 0 ≤ B i j)
    (h0 : 0 < s 0) (h1 : 0 < s 1) :
    ‖orComposedBlock 1 (alpha s 0) (alpha s 1) A B‖ ^ 2 ≤
      (Real.sqrt (s 0) + Real.sqrt (s 1)) / Real.sqrt (s 0 + s 1) *
        ‖orSourceBlock A B‖ ^ 2 := by
  have hlt := orComposedBlock_norm_sq_le A B (alpha_nonneg s 0) (alpha_nonneg s 1)
    (le_of_lt (alpha_sum_sq_gt_one h0 h1))
  rwa [alpha_sum_sq h0 h1] at hlt

/-- The OR norm bound satisfies `source_lemma_3_4_or_statement` for nonnegative source matrices
and positive weights. -/
theorem source_lemma_3_4_or_proved {m α β : Type*} [Fintype m] [DecidableEq m]
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (A : Matrix m α ℝ) (B : Matrix m β ℝ) (s : Fin 2 → ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j)
    (h0 : 0 < s 0) (h1 : 0 < s 1) :
    source_lemma_3_4_or_statement A B s hA hB h0 h1 :=
  lemma_3_4_or A B s hA hB h0 h1

end Qatlib.Papers.GameTree09.MainResults
