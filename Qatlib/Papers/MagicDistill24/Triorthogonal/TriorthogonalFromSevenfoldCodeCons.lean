/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.Triorthogonal.TriorthogonalCss
public import Qatlib.Papers.MagicDistill24.Triorthogonal.TriorthogonalFromSevenfoldCodeStat

@[expose] public section

namespace Qatlib.Papers.MagicDistill24.Triorthogonal

open Matrix

/-- Shows that each row of the standard generator belongs to its row space. -/
private theorem stdGen_row_mem {k m' n : ℕ} (G₁ : Matrix (Fin k) (Fin n) F1024)
    (G₀ : Matrix (Fin m') (Fin n) F1024) (r : Fin k ⊕ Fin m') :
    triStdGen G₁ G₀ r ∈ triRowSpace (triStdGen G₁ G₀) :=
  Submodule.subset_span ⟨r, rfl⟩

/-- Computes the identity-block entries of a distinguished standard generator row. -/
private theorem stdGen_inl_left {k m' n : ℕ} (G₁ : Matrix (Fin k) (Fin n) F1024)
    (G₀ : Matrix (Fin m') (Fin n) F1024) (a j : Fin k) :
    triStdGen G₁ G₀ (Sum.inl a) (Sum.inl j) = if a = j then 1 else 0 := by
  simp [triStdGen, Matrix.fromBlocks_apply₁₁, Matrix.one_apply]

/-- Computes the right-block entries of a distinguished standard generator row as entries of
`G₁`. -/
private theorem stdGen_inl_right {k m' n : ℕ} (G₁ : Matrix (Fin k) (Fin n) F1024)
    (G₀ : Matrix (Fin m') (Fin n) F1024) (a : Fin k) (i : Fin n) :
    triStdGen G₁ G₀ (Sum.inl a) (Sum.inr i) = G₁ a i := by
  simp [triStdGen, Matrix.fromBlocks_apply₁₂]

/-- Shows that the left-block entries of a clause-zero standard generator row vanish. -/
private theorem stdGen_inr_left {k m' n : ℕ} (G₁ : Matrix (Fin k) (Fin n) F1024)
    (G₀ : Matrix (Fin m') (Fin n) F1024) (a' : Fin m') (j : Fin k) :
    triStdGen G₁ G₀ (Sum.inr a') (Sum.inl j) = 0 := by
  simp [triStdGen, Matrix.fromBlocks_apply₂₁]

/-- Computes the right-block entries of a clause-zero standard generator row as entries of `G₀`. -/
private theorem stdGen_inr_right {k m' n : ℕ} (G₁ : Matrix (Fin k) (Fin n) F1024)
    (G₀ : Matrix (Fin m') (Fin n) F1024) (a' : Fin m') (i : Fin n) :
    triStdGen G₁ G₀ (Sum.inr a') (Sum.inr i) = G₀ a' i := by
  simp [triStdGen, Matrix.fromBlocks_apply₂₂]

/-- Shows that two elements of `F1024` summing to zero are equal. -/
private theorem char2_eq_of_add_eq_zero {X Y : F1024} (h : X + Y = 0) : Y = X := by
  have h2 : (2 : F1024) = 0 := CharTwo.two_eq_zero
  have hYY : Y + Y = 0 := by
    calc Y + Y = (2 : F1024) * Y := by ring
      _ = 0 * Y := by rw [h2]
      _ = 0 := by ring
  calc Y = 0 + Y := (zero_add Y).symm
    _ = (X + Y) + Y := by rw [h]
    _ = X + (Y + Y) := by rw [add_assoc]
    _ = X + 0 := by rw [hYY]
    _ = X := add_zero X

/-- Equates the left and right block triple sums with exponents four, two, and one under
sevenfold orthogonality. -/
private theorem sevenfold_split {k m' n : ℕ} (G₁ : Matrix (Fin k) (Fin n) F1024)
    (G₀ : Matrix (Fin m') (Fin n) F1024)
    (h7 : ∀ y₁ y₂ y₃ y₄ y₅ y₆ y₇ : Fin k ⊕ Fin n → F1024,
      y₁ ∈ triRowSpace (triStdGen G₁ G₀) → y₂ ∈ triRowSpace (triStdGen G₁ G₀) →
      y₃ ∈ triRowSpace (triStdGen G₁ G₀) → y₄ ∈ triRowSpace (triStdGen G₁ G₀) →
      y₅ ∈ triRowSpace (triStdGen G₁ G₀) → y₆ ∈ triRowSpace (triStdGen G₁ G₀) →
      y₇ ∈ triRowSpace (triStdGen G₁ G₀) →
        ∑ i, y₁ i * y₂ i * y₃ i * y₄ i * y₅ i * y₆ i * y₇ i = 0)
    (t₁ t₂ t₃ : Fin k ⊕ Fin m') :
    (∑ i : Fin n, triStdGen G₁ G₀ t₁ (Sum.inr i) ^ 4
          * triStdGen G₁ G₀ t₂ (Sum.inr i) ^ 2 * triStdGen G₁ G₀ t₃ (Sum.inr i))
      = ∑ j : Fin k, triStdGen G₁ G₀ t₁ (Sum.inl j) ^ 4
          * triStdGen G₁ G₀ t₂ (Sum.inl j) ^ 2 * triStdGen G₁ G₀ t₃ (Sum.inl j) := by
  have hfull := h7 (triStdGen G₁ G₀ t₁) (triStdGen G₁ G₀ t₁)
    (triStdGen G₁ G₀ t₁) (triStdGen G₁ G₀ t₁) (triStdGen G₁ G₀ t₂)
    (triStdGen G₁ G₀ t₂) (triStdGen G₁ G₀ t₃)
    (stdGen_row_mem G₁ G₀ t₁) (stdGen_row_mem G₁ G₀ t₁)
    (stdGen_row_mem G₁ G₀ t₁) (stdGen_row_mem G₁ G₀ t₁)
    (stdGen_row_mem G₁ G₀ t₂) (stdGen_row_mem G₁ G₀ t₂)
    (stdGen_row_mem G₁ G₀ t₃)
  rw [Fintype.sum_sum_type] at hfull
  have hentry : ∀ x : Fin k ⊕ Fin n,
      triStdGen G₁ G₀ t₁ x * triStdGen G₁ G₀ t₁ x * triStdGen G₁ G₀ t₁ x
          * triStdGen G₁ G₀ t₁ x * triStdGen G₁ G₀ t₂ x * triStdGen G₁ G₀ t₂ x
          * triStdGen G₁ G₀ t₃ x
        = triStdGen G₁ G₀ t₁ x ^ 4 * triStdGen G₁ G₀ t₂ x ^ 2
            * triStdGen G₁ G₀ t₃ x := by
    intro x
    ring
  rw [Finset.sum_congr rfl fun j _ => hentry (Sum.inl j),
    Finset.sum_congr rfl fun i _ => hentry (Sum.inr i)] at hfull
  exact char2_eq_of_add_eq_zero hfull

/-- Equates the left and right weighted pair sums under the stated weighted orthogonality
assumption. -/
private theorem weighted_split {k m' n : ℕ} (G₁ : Matrix (Fin k) (Fin n) F1024)
    (G₀ : Matrix (Fin m') (Fin n) F1024) (w : Fin k ⊕ Fin n → F1024)
    (h5 : ∀ y₁ y₂ : Fin k ⊕ Fin n → F1024,
      y₁ ∈ triRowSpace (triStdGen G₁ G₀) → y₂ ∈ triRowSpace (triStdGen G₁ G₀) →
        ∑ i, (w i) ^ 5 * y₁ i * y₂ i = 0)
    (t₁ t₂ : Fin k ⊕ Fin m') :
    (∑ i : Fin n, (w (Sum.inr i)) ^ 5 * triStdGen G₁ G₀ t₁ (Sum.inr i)
          * triStdGen G₁ G₀ t₂ (Sum.inr i))
      = ∑ j : Fin k, (w (Sum.inl j)) ^ 5 * triStdGen G₁ G₀ t₁ (Sum.inl j)
          * triStdGen G₁ G₀ t₂ (Sum.inl j) := by
  have hfull := h5 (triStdGen G₁ G₀ t₁) (triStdGen G₁ G₀ t₂)
    (stdGen_row_mem G₁ G₀ t₁) (stdGen_row_mem G₁ G₀ t₂)
  rw [Fintype.sum_sum_type] at hfull
  exact char2_eq_of_add_eq_zero hfull

/-- Evaluates a product of three coordinate indicators as the indicator that all three indices
agree. -/
private theorem diag3_sum {k : ℕ} (α β γ : Fin k) :
    (∑ j : Fin k, (if α = j then (1 : F1024) else 0) * (if β = j then 1 else 0)
          * (if γ = j then 1 else 0))
      = if α = β ∧ β = γ then 1 else 0 := by
  by_cases h1 : α = β
  · by_cases h2 : β = γ
    · rw [ite_eq_left ⟨h1, h2⟩]
      rw [Finset.sum_eq_single α]
      · rw [← h2, ← h1]
        simp
      · intro j _ hj
        simp [Ne.symm hj]
      · intro hcon
        exact absurd (Finset.mem_univ α) hcon
    · rw [ite_eq_right (fun hc => h2 hc.2)]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj1 : α = j
      · by_cases hj2 : β = j
        · by_cases hj3 : γ = j
          · exact absurd (hj2.trans hj3.symm) h2
          · simp [hj3]
        · simp [hj2]
      · simp [hj1]
  · rw [ite_eq_right (fun hc => h1 hc.1)]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj1 : α = j
    · by_cases hj2 : β = j
      · exact absurd (hj1.trans hj2.symm) h1
      · simp [hj2]
    · simp [hj1]

/-- Evaluates a weighted product of two coordinate indicators at their common index, or zero if
they differ. -/
private theorem diag2_sum {k : ℕ} (W : Fin k → F1024) (α β : Fin k) :
    (∑ j : Fin k, W j * (if α = j then (1 : F1024) else 0)
          * (if β = j then 1 else 0))
      = if α = β then W α else 0 := by
  by_cases h : α = β
  · subst h
    simp
  · rw [ite_eq_right h]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj1 : α = j
    · by_cases hj2 : β = j
      · exact absurd (hj1.trans hj2.symm) h
      · simp [hj2]
    · simp [hj1]

/-- Shows that a positive power leaves a zero-one indicator unchanged. -/
private theorem ite_pow (b : Prop) [Decidable b] {r : ℕ} (hr : 0 < r) :
    (if b then (1 : F1024) else 0) ^ r = if b then 1 else 0 := by
  by_cases hb : b
  · rw [ite_eq_left hb, one_pow]
  · rw [ite_eq_right hb, zero_pow (by omega)]

/-- Identifies the natural value of an index whose inverse sum encoding lies in the left
summand. -/
private theorem val_lt_of_symm_inl {k m' : ℕ} {a : Fin (k + m')} {α : Fin k}
    (h : finSumFinEquiv.symm a = Sum.inl α) : (a : ℕ) = (α : ℕ) := by
  have ha : a = finSumFinEquiv (Sum.inl α) := by
    rw [← h, finSumFinEquiv.apply_symm_apply]
  rw [ha, finSumFinEquiv_apply_left, Fin.val_castAdd]

/-- Bounds an index below by the left summand size when its inverse sum encoding lies in the
right summand. -/
private theorem val_ge_of_symm_inr {k m' : ℕ} (a : Fin (k + m')) {α' : Fin m'}
    (h : finSumFinEquiv.symm a = Sum.inr α') : k ≤ (a : ℕ) := by
  have ha : a = finSumFinEquiv (Sum.inr α') := by
    rw [← h, finSumFinEquiv.apply_symm_apply]
  rw [ha, finSumFinEquiv_apply_right, Fin.val_natAdd]
  omega

/-- Establishes the triorthogonal construction from a sevenfold orthogonal code. -/
theorem triorthogonalFromSevenfoldCode : TriorthogonalFromSevenfoldCode := by
  intro k m' n G₁ G₀ w hw h7 h5
  refine ⟨?_, ?_⟩
  · intro a b c
    have hsplit := sevenfold_split G₁ G₀ h7 (finSumFinEquiv.symm a)
      (finSumFinEquiv.symm b) (finSumFinEquiv.symm c)
    have hlhs : (∑ i : Fin n, triPuncture G₁ G₀ a i ^ 4 * triPuncture G₁ G₀ b i ^ 2
          * triPuncture G₁ G₀ c i)
        = ∑ i : Fin n, triStdGen G₁ G₀ (finSumFinEquiv.symm a) (Sum.inr i) ^ 4
            * triStdGen G₁ G₀ (finSumFinEquiv.symm b) (Sum.inr i) ^ 2
            * triStdGen G₁ G₀ (finSumFinEquiv.symm c) (Sum.inr i) := rfl
    rw [hlhs, hsplit]
    rcases hsa : finSumFinEquiv.symm a with α | α'
    · rcases hsb : finSumFinEquiv.symm b with β | β'
      · rcases hsc : finSumFinEquiv.symm c with γ | γ'
        · have hva : (a : ℕ) = (α : ℕ) := val_lt_of_symm_inl hsa
          have hvb : (b : ℕ) = (β : ℕ) := val_lt_of_symm_inl hsb
          have hvc : (c : ℕ) = (γ : ℕ) := val_lt_of_symm_inl hsc
          rw [hva, hvb, hvc]
          simp only [Fin.val_inj]
          simp only [stdGen_inl_left, ite_pow _ (show 0 < 4 by norm_num),
            ite_pow _ (show 0 < 2 by norm_num), diag3_sum]
          by_cases h1 : α = β
          · by_cases h2 : β = γ
            · rw [ite_eq_left ⟨h1, h2⟩, ite_eq_left ⟨h1, h2, α.isLt⟩]
            · rw [ite_eq_right (fun hc => h2 hc.2), ite_eq_right (fun hc => h2 hc.2.1)]
          · rw [ite_eq_right (fun hc => h1 hc.1), ite_eq_right (fun hc => h1 hc.1)]
        · simp only [stdGen_inr_left, mul_zero, Finset.sum_const_zero]
          rw [ite_eq_right (fun hc => by
            have hva : (a : ℕ) = (α : ℕ) := val_lt_of_symm_inl hsa
            have hvb : (b : ℕ) = (β : ℕ) := val_lt_of_symm_inl hsb
            have hge : k ≤ (c : ℕ) := val_ge_of_symm_inr c hsc
            have hbc := hc.2.1
            omega)]
      · simp only [stdGen_inr_left, zero_pow (show (2 : ℕ) ≠ 0 by norm_num),
          mul_zero, zero_mul, Finset.sum_const_zero]
        rw [ite_eq_right (fun hc => by
          have hva : (a : ℕ) = (α : ℕ) := val_lt_of_symm_inl hsa
          have hge : k ≤ (b : ℕ) := val_ge_of_symm_inr b hsb
          have hab := hc.1
          omega)]
    · simp only [stdGen_inr_left, zero_pow (show (4 : ℕ) ≠ 0 by norm_num),
        zero_mul, Finset.sum_const_zero]
      rw [ite_eq_right (fun hc => by
        have hge : k ≤ (a : ℕ) := val_ge_of_symm_inr a hsa
        have hlt := hc.2.2
        omega)]
  · intro a b
    have hsplit := weighted_split G₁ G₀ w h5 (finSumFinEquiv.symm a)
      (finSumFinEquiv.symm b)
    have hlhs : (∑ i : Fin n, (w (Sum.inr i)) ^ 5 * triPuncture G₁ G₀ a i
          * triPuncture G₁ G₀ b i)
        = ∑ i : Fin n, (w (Sum.inr i)) ^ 5 * triStdGen G₁ G₀ (finSumFinEquiv.symm a)
            (Sum.inr i) * triStdGen G₁ G₀ (finSumFinEquiv.symm b) (Sum.inr i) := rfl
    rw [hlhs, hsplit]
    rcases hsa : finSumFinEquiv.symm a with α | α'
    · rcases hsb : finSumFinEquiv.symm b with β | β'
      · have hva : (a : ℕ) = (α : ℕ) := val_lt_of_symm_inl hsa
        have hvb : (b : ℕ) = (β : ℕ) := val_lt_of_symm_inl hsb
        simp only [stdGen_inl_left, diag2_sum]
        by_cases h : α = β
        · rw [ite_eq_left h]
          have hab : (a : ℕ) = (b : ℕ) := by rw [hva, hvb, h]
          have hlt : (a : ℕ) < k := by rw [hva]; exact α.isLt
          rw [dite_eq_left ⟨hab, hlt⟩]
          have hfin : (⟨(a : ℕ), hlt⟩ : Fin k) = α := Fin.ext hva
          rw [hfin]
        · rw [ite_eq_right h]
          rw [dite_eq_right (fun hc => by
            have hab := hc.1
            have hva' : (a : ℕ) = (α : ℕ) := val_lt_of_symm_inl hsa
            have hvb' : (b : ℕ) = (β : ℕ) := val_lt_of_symm_inl hsb
            omega)]
      · simp only [stdGen_inr_left, mul_zero, Finset.sum_const_zero]
        rw [dite_eq_right (fun hc => by
          have hva : (a : ℕ) = (α : ℕ) := val_lt_of_symm_inl hsa
          have hge : k ≤ (b : ℕ) := val_ge_of_symm_inr b hsb
          have hab := hc.1
          omega)]
    · simp only [stdGen_inr_left, mul_zero, zero_mul, Finset.sum_const_zero]
      rw [dite_eq_right (fun hc => by
        have hge : k ≤ (a : ℕ) := val_ge_of_symm_inr a hsa
        have hlt := hc.2
        omega)]

end Qatlib.Papers.MagicDistill24.Triorthogonal
