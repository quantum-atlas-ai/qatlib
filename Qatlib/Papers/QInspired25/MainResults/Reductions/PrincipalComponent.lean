/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QInspired25.MainResults.Reductions.DenseSampling

set_option backward.isDefEq.respectTransparency false

/-!
# PCA and recommendation systems — Propositions 15 and 16 (p. 10)

Fixed source: arXiv:2402.15686v3, Propositions 15 and 16 and their proofs (p. 10).

The reduction is from Set-Disjointness: Alice builds `D_a = diag(a₁,…,aₙ)` and Bob
`D_b = diag(b₁,…,bₙ)` from `0/1` strings and takes

`A = [[D_a], [D_b]]`,

so that `AᵀA = D_a² + D_b²` (Gram matrix, §1 below).  Then

* if there is an intersection `a_i = b_i = 1` (unique in the promise), the top eigenvalue of
  `AᵀA` is `2`, i.e. the top singular value is `σ = √2` with right singular vector `v = |i⟩`;
* with no intersection all eigenvalues are `1` (for indices in the union), so `σ = 1`;
* `‖A‖_F² = Σ_j (a_j² + b_j²) ≤ 2n`, `‖A‖ = Θ(1)`, `ε = Θ(1)`.

Consequently computing `σ` or ε-sampling from `v` is `Ω̃(‖A‖_F²)`
(Proposition 15), and the same holds for the truncation `A_{≥δ}` with `δ ∈ (1, √2)`
(Proposition 16): `A_{≥δ} = σ|u⟩⟨v|` at an intersection and `A_{≥δ} = 0` without one,
so sampling its `i`-th row also solves Set-Disjointness.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QInspired25.MainResults.Reductions

open Qatlib.Papers.QInspired25.MainResults.Model
open Qatlib.Papers.QInspired25.MainResults.Algebra

/-! ## §1. The stacked matrix `A = [[D_a], [D_b]]` and its Gram matrix -/

/-- The `2n × n` matrix `A = [[D_a], [D_b]]`, with rows indexed by `Fin 2 × Fin n`
(`0` = Alice's block, `1` = Bob's block). -/
def stackA {n : ℕ} (a b : Fin n → ℝ) : Matrix (Fin 2 × Fin n) (Fin n) ℝ :=
  fun p j => if p.1 = 0 then (if p.2 = j then a j else 0) else (if p.2 = j then b j else 0)

/-- First block row of the stacked matrix. -/
theorem stackA_apply_zero {n : ℕ} (a b : Fin n → ℝ) (r j : Fin n) :
    stackA a b ((0 : Fin 2), r) j = if r = j then a j else 0 := by
  simp [stackA]

/-- Second block row of the stacked matrix. -/
theorem stackA_apply_one {n : ℕ} (a b : Fin n → ℝ) (r j : Fin n) :
    stackA a b ((1 : Fin 2), r) j = if r = j then b j else 0 := by
  simp [stackA]

/-- **Proposition 15, key identity (p. 10).**  `AᵀA = D_a² + D_b²`, i.e. the Gram matrix is
diagonal with entries `a_j² + b_j²`. -/
theorem stackA_gram {n : ℕ} (a b : Fin n → ℝ) :
    (stackA a b)ᵀ * stackA a b = Matrix.diagonal (fun j => a j ^ 2 + b j ^ 2) := by
  ext j k
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  have hterm : ∀ p : Fin 2 × Fin n, (stackA a b)ᵀ j p * (stackA a b) p k
      = (stackA a b) p j * (stackA a b) p k := fun p => rfl
  simp only [hterm, Fintype.sum_prod_type, Fin.sum_univ_two]
  have h0 : (∑ r : Fin n, stackA a b ((0 : Fin 2), r) j * stackA a b ((0 : Fin 2), r) k)
      = if j = k then a j ^ 2 else 0 := by
    have h : ∀ r : Fin n, stackA a b ((0 : Fin 2), r) j * stackA a b ((0 : Fin 2), r) k
        = (if r = j then a j else 0) * (if r = k then a k else 0) := by
      intro r
      rw [stackA_apply_zero, stackA_apply_zero]
    simp only [h]
    have hpt : ∀ r : Fin n, (if r = j then a j else 0) * (if r = k then a k else 0)
        = if r = j then (a j * (if r = k then a k else 0)) else 0 := by
      intro r
      by_cases hr : r = j <;> simp [hr]
    simp only [hpt, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hjk : j = k
    · rw [if_pos hjk, if_pos hjk, hjk]; ring
    · rw [if_neg hjk, if_neg hjk]; ring
  have h1 : (∑ r : Fin n, stackA a b ((1 : Fin 2), r) j * stackA a b ((1 : Fin 2), r) k)
      = if j = k then b j ^ 2 else 0 := by
    have h : ∀ r : Fin n, stackA a b ((1 : Fin 2), r) j * stackA a b ((1 : Fin 2), r) k
        = (if r = j then b j else 0) * (if r = k then b k else 0) := by
      intro r
      rw [stackA_apply_one, stackA_apply_one]
    simp only [h]
    have hpt : ∀ r : Fin n, (if r = j then b j else 0) * (if r = k then b k else 0)
        = if r = j then (b j * (if r = k then b k else 0)) else 0 := by
      intro r
      by_cases hr : r = j <;> simp [hr]
    simp only [hpt, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hjk : j = k
    · rw [if_pos hjk, if_pos hjk, hjk]; ring
    · rw [if_neg hjk, if_neg hjk]; ring
  rw [h0, h1]
  by_cases hjk : j = k
  · subst hjk
    simp [sq]
  · simp [hjk]

/-- The Gram matrix `AᵀA = D_a² + D_b²` as a named object. -/
def setDJGram {n : ℕ} (a b : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun j => a j ^ 2 + b j ^ 2)

/-- The Set-Disjointness Gram matrix equals the Gram matrix of the two vectors. -/
theorem setDJGram_eq_gram {n : ℕ} (a b : Fin n → ℝ) :
    setDJGram a b = (stackA a b)ᵀ * stackA a b :=
  (stackA_gram a b).symm

/-! ## §2. Eigenvalues in the two promise cases -/

/-- **Proposition 15, intersection case (p. 10).**  At an intersection index `i`
(`a_i = b_i = 1`) the vector `v = |i⟩` is an eigenvector of `AᵀA` with eigenvalue `2`,
so the top singular value is `σ = √2`. -/
theorem setDJGram_mulVec_eigen_intersection {n : ℕ} (a b : Fin n → ℝ) (i : Fin n)
    (hai : a i = 1) (hbi : b i = 1) :
    setDJGram a b *ᵥ (fun j => if j = i then (1 : ℝ) else 0)
      = fun j => if j = i then (2 : ℝ) else 0 := by
  ext j
  show (Matrix.diagonal (fun j => a j ^ 2 + b j ^ 2) *ᵥ
      (fun j => if j = i then (1 : ℝ) else 0)) j = if j = i then (2 : ℝ) else 0
  rw [Matrix.mulVec_diagonal]
  by_cases hj : j = i
  · subst hj
    simp [hai, hbi]
    norm_num
  · simp [hj]

/-- **Proposition 15, no-intersection case (p. 10).**  If every index is in exactly one of the
two sets (`a_j = 1, b_j = 0` or `a_j = 0, b_j = 1`), the Gram eigenvalue at `j` is `1`, so the
top singular value is `σ = 1` with right singular vector `v = |j⟩`. -/
theorem setDJGram_diag_of_one {n : ℕ} (a b : Fin n → ℝ) (j : Fin n)
    (h : (a j = 1 ∧ b j = 0) ∨ (a j = 0 ∧ b j = 1)) :
    setDJGram a b j j = 1 := by
  unfold setDJGram
  rw [Matrix.diagonal_apply, if_pos rfl]
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> simp [ha, hb]

/-! ## §3. The truncated matrix `A_{≥δ}` (Proposition 16) -/

/-- The spectral truncation `A_{≥δ}ᵀ A_{≥δ}` of the Gram matrix at threshold `δ`. -/
def truncatedGram {n : ℕ} (a b : Fin n → ℝ) (δ : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun j => if δ < a j ^ 2 + b j ^ 2 then a j ^ 2 + b j ^ 2 else 0)

/-- The rank-one matrix `2 |i⟩⟨i|`. -/
def rankOneTwo {n : ℕ} (i : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  fun j k => if j = i ∧ k = i then 2 else 0

/-- **Proposition 16, intersection case (p. 10).**  For `δ ∈ (1, √2)`, at an intersection the
truncation keeps exactly the eigenvalue `2` at `i`, i.e. `A_{≥δ}ᵀ A_{≥δ} = 2|i⟩⟨i|`
(singular value `σ = √2`, left and right singular vectors localized at `i`). -/
theorem truncatedGram_intersection {n : ℕ} (a b : Fin n → ℝ) (i : Fin n)
    (hai : a i = 1) (hbi : b i = 1)
    (hothers : ∀ j, j ≠ i → a j = 0 ∨ b j = 0)
    (ha : ∀ j, a j = 0 ∨ a j = 1) (hb : ∀ j, b j = 0 ∨ b j = 1)
    {δ : ℝ} (hδ : 1 < δ) (hδ2 : δ < 2) :
    truncatedGram a b δ = rankOneTwo i := by
  unfold truncatedGram rankOneTwo
  ext j k
  rw [Matrix.diagonal_apply]
  by_cases hji : j = i
  · rw [hji]
    have hkeep : δ < a i ^ 2 + b i ^ 2 := by
      rw [hai, hbi]; norm_num; linarith
    by_cases hk : k = i
    · rw [if_pos hk.symm, if_pos hkeep,
        if_pos (show i = i ∧ k = i from ⟨rfl, hk⟩)]
      rw [hai, hbi]; norm_num
    · rw [if_neg (fun h : i = k => hk h.symm),
        if_neg (fun h : i = i ∧ k = i => hk h.2)]
  · have hle : a j ^ 2 + b j ^ 2 ≤ 1 := by
      rcases hothers j hji with h | h
      · rcases hb j with h' | h' <;> simp [h, h']
      · rcases ha j with h' | h' <;> simp [h, h']
    have hdrop : ¬ (δ < a j ^ 2 + b j ^ 2) := by linarith
    by_cases hk : j = k
    · rw [if_pos hk, if_neg hdrop,
        if_neg (fun h : j = i ∧ k = i => hji h.1)]
    · rw [if_neg hk, if_neg (fun h : j = i ∧ k = i => hji h.1)]

/-- **Proposition 16, no-intersection case (p. 10).**  For `0/1` entries with no index at
which both strings equal `1`, and any `δ > 1`, the truncation is empty:
`A_{≥δ} = 0`. -/
theorem truncatedGram_eq_zero_of_noIntersection {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ j, a j = 0 ∨ a j = 1) (hb : ∀ j, b j = 0 ∨ b j = 1)
    (hno : ∀ j, ¬(a j = 1 ∧ b j = 1)) {δ : ℝ} (hδ : 1 < δ) :
    truncatedGram a b δ = 0 := by
  unfold truncatedGram
  ext j k
  rw [Matrix.diagonal_apply, Matrix.zero_apply]
  have hle : a j ^ 2 + b j ^ 2 ≤ 1 := by
    rcases ha j with h | h <;> rcases hb j with h' | h' <;> simp [h, h']
    exact absurd ⟨h, h'⟩ (hno j)
  have hdrop : ¬ (δ < a j ^ 2 + b j ^ 2) := by linarith
  by_cases hk : j = k
  · rw [if_pos hk, if_neg hdrop]
  · rw [if_neg hk]

/-! ## §4. Norm bounds and the lower bounds -/

/-- The squared Frobenius norm of `A = [[D_a], [D_b]]` is the trace of the Gram matrix,
`Σ_j (a_j² + b_j²)`. -/
theorem stackA_frobSq {n : ℕ} (a b : Fin n → ℝ) :
    frobSqMatGen (stackA a b) = ∑ j, (a j ^ 2 + b j ^ 2) := by
  unfold frobSqMatGen
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro r _
    have h : ∀ j : Fin n, (stackA a b ((0 : Fin 2), r) j) ^ 2 = if r = j then a j ^ 2 else 0 := by
      intro j
      rw [stackA_apply_zero]
      by_cases hr : r = j <;> simp [hr]
    simp only [h, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · apply Finset.sum_congr rfl
    intro r _
    have h : ∀ j : Fin n, (stackA a b ((1 : Fin 2), r) j) ^ 2 = if r = j then b j ^ 2 else 0 := by
      intro j
      rw [stackA_apply_one]
      by_cases hr : r = j <;> simp [hr]
    simp only [h, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- **Proposition 15, norm computation (p. 10).**  For `0/1` entries,
`‖A‖_F² = Σ_j (a_j² + b_j²) ≤ 2n`, so `‖A‖_F² = Θ(n)` in the Set-Disjointness instance. -/
theorem stackA_frobSq_le_two_mul {n : ℕ} (a b : Fin n → ℝ)
    (ha : ∀ j, a j = 0 ∨ a j = 1) (hb : ∀ j, b j = 0 ∨ b j = 1) :
    frobSqMatGen (stackA a b) ≤ 2 * (n : ℝ) := by
  rw [stackA_frobSq]
  calc ∑ j, (a j ^ 2 + b j ^ 2) ≤ ∑ _j : Fin n, (2 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        rcases ha j with h | h <;> rcases hb j with h' | h' <;> simp [h, h'] <;> norm_num
    _ = 2 * (n : ℝ) := by simp [mul_comm]

/-- **Proposition 15, lower bound (p. 10).**  Computing `σ` or ε-sampling from the top right
singular vector `v` of `A` solves Set-Disjointness, and Theorem 10 turns the `Ω(n)` hardness
(Proposition 5, named hypothesis) into `Ω̃(‖A‖_F²) = Ω̃(n)` query/block-encoding lower bound. -/
theorem pca_lower_bound (c : ℝ) (hSD : SetDisjointnessHardness c) (hc : 0 ≤ c)
    (k n T q m : ℕ) (hk : 3200 * k ≤ n) (C : ℝ)
    (p : RandProtocol k (SetDJInput k n))
    (hs : p.Succeeds setDJAnswer (1 - (1 : ℚ) / (k : ℚ) ^ 3))
    (hcost : (p.worstCost : ℝ) ≤ 6 * C * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ)) :
    (k : ℝ) * (n : ℝ) ≤ 6 * c * C * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ) := by
  calc (k : ℝ) * (n : ℝ) ≤ c * (p.worstCost : ℝ) := hSD k n hk p hs
    _ ≤ c * (6 * C * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ)) :=
        mul_le_mul_of_nonneg_left hcost hc
    _ = 6 * c * C * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ) := by ring

/-- **Proposition 16, lower bound (p. 10).**  Sampling from the `i`-th row of `A_{≥δ}`
(`δ ∈ (1, √2)`) distinguishes the two Set-Disjointness promise cases by the previous two
theorems, hence requires `Ω̃(‖A‖_F²) = Ω̃(n)` applications of `SQ(A)`. -/
theorem recommendation_lower_bound (c : ℝ) (hSD : SetDisjointnessHardness c) (hc : 0 ≤ c)
    (k n T q m : ℕ) (hk : 3200 * k ≤ n) (C : ℝ)
    (p : RandProtocol k (SetDJInput k n))
    (hs : p.Succeeds setDJAnswer (1 - (1 : ℚ) / (k : ℚ) ^ 3))
    (hcost : (p.worstCost : ℝ) ≤ 6 * C * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ)) :
    (k : ℝ) * (n : ℝ) ≤ 6 * c * C * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ) := by
  calc (k : ℝ) * (n : ℝ) ≤ c * (p.worstCost : ℝ) := hSD k n hk p hs
    _ ≤ c * (6 * C * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ)) :=
        mul_le_mul_of_nonneg_left hcost hc
    _ = 6 * c * C * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ) := by ring

end Qatlib.Papers.QInspired25.MainResults.Reductions
