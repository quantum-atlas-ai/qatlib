/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PottsTutte07.MainResults.ComplexityDefs
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.PottsTutte07.MainResults

open scoped BigOperators
open Finset

theorem entryDist_nonneg {n : Type*} [Fintype n] (A B : Matrix n n ℂ) : 0 ≤ entryDist A B :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem entryDist_self {n : Type*} [Fintype n] (A : Matrix n n ℂ) : entryDist A A = 0 := by
  unfold entryDist
  simp

theorem entryDist_comm {n : Type*} [Fintype n] (A B : Matrix n n ℂ) :
    entryDist A B = entryDist B A := by
  unfold entryDist
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [norm_sub_rev]

theorem entryDist_eq_sub {n : Type*} [Fintype n] (A B : Matrix n n ℂ) :
    entryDist A B = entryDist (A - B) 0 := by
  unfold entryDist
  simp [Matrix.sub_apply]

theorem double_sum_entry_le {ι : Type*} [Fintype ι] (f : ι → ι → ℝ)
    (hf : ∀ a b, 0 ≤ f a b) (i j : ι) : f i j ≤ ∑ a, ∑ b, f a b := by
  have h1 : f i j ≤ ∑ b, f i b :=
    Finset.single_le_sum (f := fun b => f i b) (fun b _ => hf i b) (Finset.mem_univ j)
  have h2 : (∑ b, f i b) ≤ ∑ a, ∑ b, f a b :=
    Finset.single_le_sum (f := fun a => ∑ b, f a b)
      (fun a _ => Finset.sum_nonneg fun b _ => hf a b) (Finset.mem_univ i)
  exact h1.trans h2

theorem entryDist_entry_le {n : Type*} [Fintype n] (A B : Matrix n n ℂ) (i j : n) :
    ‖A i j - B i j‖ ≤ entryDist A B :=
  double_sum_entry_le (fun a b => ‖A a b - B a b‖) (fun _ _ => norm_nonneg _) i j

theorem eq_of_entryDist_eq_zero {n : Type*} [Fintype n] (A B : Matrix n n ℂ)
    (h : entryDist A B = 0) : A = B := by
  funext i j
  have h1 : ‖A i j - B i j‖ = 0 := by
    refine le_antisymm ?_ (norm_nonneg _)
    rw [← h]
    exact entryDist_entry_le A B i j
  exact sub_eq_zero.mp (norm_eq_zero.mp h1)

theorem entryDist_triangle {n : Type*} [Fintype n] (A B C : Matrix n n ℂ) :
    entryDist A C ≤ entryDist A B + entryDist B C := by
  unfold entryDist
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  calc ‖A i j - C i j‖ = ‖(A i j - B i j) + (B i j - C i j)‖ := by ring_nf
    _ ≤ ‖A i j - B i j‖ + ‖B i j - C i j‖ := norm_add_le _ _

theorem entryDist_sub_zero_le {n : Type*} [Fintype n] (X Y : Matrix n n ℂ) :
    entryDist (X - Y) 0 ≤ entryDist X 0 + entryDist Y 0 := by
  unfold entryDist
  simp only [Matrix.sub_apply, Matrix.zero_apply, sub_zero]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  exact norm_sub_le _ _

theorem entryDist_sub_sub_le {n : Type*} [Fintype n] (A B C D : Matrix n n ℂ) :
    entryDist (A - B) (C - D) ≤ entryDist A C + entryDist B D := by
  unfold entryDist
  simp only [Matrix.sub_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have h : (A i j - B i j) - (C i j - D i j) = (A i j - C i j) - (B i j - D i j) := by ring
  rw [h]
  exact norm_sub_le _ _

theorem entryDist_add_le {n : Type*} [Fintype n] (A B C D : Matrix n n ℂ) :
    entryDist (A + B) (C + D) ≤ entryDist A C + entryDist B D := by
  unfold entryDist
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have h : (A + B) i j - (C + D) i j = (A i j - C i j) + (B i j - D i j) := by
    simp only [Matrix.add_apply]; ring
  rw [h]
  exact norm_add_le _ _

theorem entryDist_smul {n : Type*} [Fintype n] (c : ℂ) (A B : Matrix n n ℂ) :
    entryDist (c • A) (c • B) = ‖c‖ * entryDist A B := by
  unfold entryDist
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_sub, norm_mul]

theorem entryDist_smul_zero {n : Type*} [Fintype n] (c : ℂ) (A : Matrix n n ℂ) :
    entryDist (c • A) 0 = ‖c‖ * entryDist A 0 := by
  simpa using entryDist_smul (n := n) c A 0

theorem entryDist_mul_zero_le {n : Type*} [Fintype n] (A B : Matrix n n ℂ) :
    entryDist (A * B) 0 ≤ (Fintype.card n : ℝ) ^ 3 * entryDist A 0 * entryDist B 0 := by
  have hA0 : 0 ≤ entryDist A 0 := entryDist_nonneg _ _
  have hB0 : 0 ≤ entryDist B 0 := entryDist_nonneg _ _
  have hN0 : 0 ≤ (Fintype.card n : ℝ) := by positivity
  have hentry : ∀ i j : n,
      ‖(A * B) i j‖ ≤ (Fintype.card n : ℝ) * (entryDist A 0 * entryDist B 0) := by
    intro i j
    have h1 : ‖(A * B) i j‖ ≤ ∑ k : n, ‖A i k‖ * ‖B k j‖ := by
      rw [Matrix.mul_apply]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => by rw [norm_mul])
    have h2 : ∀ k : n, ‖A i k‖ * ‖B k j‖ ≤ entryDist A 0 * entryDist B 0 := by
      intro k
      exact mul_le_mul (by simpa using entryDist_entry_le A 0 i k)
        (by simpa using entryDist_entry_le B 0 k j) (norm_nonneg _) hA0
    calc ‖(A * B) i j‖ ≤ ∑ k : n, ‖A i k‖ * ‖B k j‖ := h1
      _ ≤ ∑ _k : n, entryDist A 0 * entryDist B 0 := Finset.sum_le_sum fun k _ => h2 k
      _ = (Fintype.card n : ℝ) * (entryDist A 0 * entryDist B 0) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsum : entryDist (A * B) 0
      ≤ ∑ _i : n, ∑ _j : n, (Fintype.card n : ℝ) * (entryDist A 0 * entryDist B 0) := by
    unfold entryDist
    exact Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ => by simpa [entryDist, Matrix.zero_apply] using hentry i j
  refine hsum.trans (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

theorem entryDist_mul_pair_le {n : Type*} [Fintype n] (A B C D : Matrix n n ℂ) :
    entryDist (A * B) (C * D) ≤ (Fintype.card n : ℝ) ^ 3 *
      (entryDist A 0 * entryDist B D + entryDist A C * entryDist D 0) := by
  have hdecomp : A * B - C * D = A * (B - D) + (A - C) * D := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    exact (sub_add_sub_cancel (A * B) (A * D) (C * D)).symm
  rw [entryDist_eq_sub, hdecomp]
  have hadd := entryDist_add_le (A * (B - D)) ((A - C) * D) 0 0
  rw [add_zero] at hadd
  refine le_trans hadd ?_
  have h1 := entryDist_mul_zero_le A (B - D)
  have h2 := entryDist_mul_zero_le (A - C) D
  have e1 : entryDist (A * (B - D)) 0
      ≤ (Fintype.card n : ℝ) ^ 3 * entryDist A 0 * entryDist B D := by
    refine h1.trans (le_of_eq ?_)
    rw [entryDist_eq_sub B D]
  have e2 : entryDist ((A - C) * D) 0
      ≤ (Fintype.card n : ℝ) ^ 3 * entryDist A C * entryDist D 0 := by
    refine h2.trans (le_of_eq ?_)
    rw [entryDist_eq_sub A C]
  have hN0 : 0 ≤ (Fintype.card n : ℝ) := by positivity
  have e10 : 0 ≤ entryDist A 0 := entryDist_nonneg _ _
  have e20 : 0 ≤ entryDist D 0 := entryDist_nonneg _ _
  have e12 : 0 ≤ entryDist B D := entryDist_nonneg _ _
  have e21 : 0 ≤ entryDist A C := entryDist_nonneg _ _
  have := add_le_add e1 e2
  calc entryDist (A * (B - D)) 0 + entryDist ((A - C) * D) 0
      ≤ ((Fintype.card n : ℝ) ^ 3 * entryDist A 0 * entryDist B D)
          + ((Fintype.card n : ℝ) ^ 3 * entryDist A C * entryDist D 0) := this
    _ = (Fintype.card n : ℝ) ^ 3 *
          (entryDist A 0 * entryDist B D + entryDist A C * entryDist D 0) := by ring

theorem entryDist_commutator_le {n : Type*} [Fintype n]
    (V W Vt Wt : Matrix n n ℂ) (ε b b' : ℝ)
    (hε : 0 ≤ ε)
    (hV : entryDist V 0 ≤ b) (hW : entryDist W 0 ≤ b)
    (hVt : entryDist Vt 0 ≤ b') (hWt0 : entryDist Wt 0 ≤ b')
    (hVVt : entryDist V Vt ≤ ε) (hWWt : entryDist W Wt ≤ ε) :
    entryDist (V * W - W * V) (Vt * Wt - Wt * Vt)
      ≤ 2 * (Fintype.card n : ℝ) ^ 3 * ε * (b + b') := by
  have hN0 : 0 ≤ (Fintype.card n : ℝ) := by positivity
  have hb0 : 0 ≤ b := le_trans (entryDist_nonneg _ _) hV
  have hb'0 : 0 ≤ b' := le_trans (entryDist_nonneg _ _) hVt
  have hsplit : entryDist (V * W - W * V) (Vt * Wt - Wt * Vt)
      ≤ entryDist (V * W) (Vt * Wt) + entryDist (W * V) (Wt * Vt) :=
    entryDist_sub_sub_le (V * W) (W * V) (Vt * Wt) (Wt * Vt)
  have h1 := entryDist_mul_pair_le V W Vt Wt
  have h2 := entryDist_mul_pair_le W V Wt Vt
  have hWWtR : entryDist W Wt ≤ ε := hWWt
  have e1 : entryDist (V * W) (Vt * Wt)
      ≤ (Fintype.card n : ℝ) ^ 3 * (b * ε + ε * b') := by
    refine h1.trans ?_
    have p1 : entryDist V 0 * entryDist W Wt ≤ b * ε :=
      mul_le_mul hV hWWtR (entryDist_nonneg _ _) hb0
    have p2 : entryDist V Vt * entryDist Wt 0 ≤ ε * b' :=
      mul_le_mul hVVt hWt0 (entryDist_nonneg _ _) hε
    have s := add_le_add p1 p2
    have hpow : 0 ≤ (Fintype.card n : ℝ) ^ 3 := by positivity
    have := mul_le_mul_of_nonneg_left s hpow
    nlinarith [this]
  have e2 : entryDist (W * V) (Wt * Vt)
      ≤ (Fintype.card n : ℝ) ^ 3 * (b * ε + ε * b') := by
    refine h2.trans ?_
    have p1 : entryDist W 0 * entryDist V Vt ≤ b * ε :=
      mul_le_mul hW hVVt (entryDist_nonneg _ _) hb0
    have p2 : entryDist W Wt * entryDist Vt 0 ≤ ε * b' :=
      mul_le_mul hWWtR hVt (entryDist_nonneg _ _) hε
    have s := add_le_add p1 p2
    have hpow : 0 ≤ (Fintype.card n : ℝ) ^ 3 := by positivity
    have := mul_le_mul_of_nonneg_left s hpow
    nlinarith [this]
  nlinarith [hsplit, e1, e2, hN0, hε, hb0, hb'0]

theorem isUnitary_one {n : Type*} [Fintype n] [DecidableEq n] :
    IsUnitary (1 : Matrix n n ℂ) := by
  unfold IsUnitary
  simp

theorem isUnitary_mul {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : IsUnitary A) (hB : IsUnitary B) : IsUnitary (A * B) := by
  unfold IsUnitary at *
  constructor
  · have h1 : (A * B) * (A * B).conjTranspose
        = A * (B * B.conjTranspose) * A.conjTranspose := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [h1, hB.1, Matrix.mul_one, hA.1]
  · have h2 : (A * B).conjTranspose * (A * B)
        = B.conjTranspose * (A.conjTranspose * A) * B := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [h2, hA.2, Matrix.mul_one, hB.2]

theorem isUnitary_conjTranspose {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : IsUnitary A) : IsUnitary (Matrix.conjTranspose A) := by
  unfold IsUnitary at *
  constructor
  · rw [Matrix.conjTranspose_conjTranspose]; exact hA.2
  · rw [Matrix.conjTranspose_conjTranspose]; exact hA.1

theorem isUnitary_det_ne_zero {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : IsUnitary A) : Matrix.det A ≠ 0 := by
  intro h
  have h1 : Matrix.det (A * Matrix.conjTranspose A) = Matrix.det (1 : Matrix n n ℂ) := by
    rw [hA.1]
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at h1
  exact zero_ne_one h1

theorem isUnitary_diagonal_iff {n : Type*} [Fintype n] [DecidableEq n] (z : n → ℂ) :
    IsUnitary (Matrix.diagonal z) ↔ ∀ i, ‖z i‖ = 1 := by
  have hdiag : Matrix.diagonal z * Matrix.conjTranspose (Matrix.diagonal z)
      = Matrix.diagonal (fun i => (Complex.normSq (z i) : ℂ)) := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simpa using Complex.mul_conj (z i)
  have hdiag' : Matrix.conjTranspose (Matrix.diagonal z) * Matrix.diagonal z
      = Matrix.diagonal (fun i => (Complex.normSq (z i) : ℂ)) := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    show star (z i) * z i = (Complex.normSq (z i) : ℂ)
    rw [mul_comm]
    simpa using Complex.mul_conj (z i)
  have unit_of_normSq : ∀ i, Complex.normSq (z i) = 1 ↔ ‖z i‖ = 1 := by
    intro i
    constructor
    · intro h
      have h2 : ‖z i‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq]; exact h
      nlinarith [norm_nonneg (z i)]
    · intro h
      rw [Complex.normSq_eq_norm_sq, h]; norm_num
  constructor
  · intro h i
    have h1 : Matrix.diagonal (fun i => (Complex.normSq (z i) : ℂ)) = 1 := by
      rw [← hdiag]; exact h.1
    have h2 := congrFun (Matrix.diagonal_eq_one.mp h1) i
    have h2' : (Complex.normSq (z i) : ℂ) = 1 := by simpa using h2
    exact (unit_of_normSq i).1 (by exact_mod_cast h2')
  · intro h
    unfold IsUnitary
    constructor
    · rw [hdiag, Matrix.diagonal_eq_one]
      funext i
      have hi := (unit_of_normSq i).2 (h i)
      show (Complex.normSq (z i) : ℂ) = 1
      rw [hi]; norm_num
    · rw [hdiag', Matrix.diagonal_eq_one]
      funext i
      have hi := (unit_of_normSq i).2 (h i)
      show (Complex.normSq (z i) : ℂ) = 1
      rw [hi]; norm_num

theorem isUnitary_diagonal {n : Type*} [Fintype n] [DecidableEq n] (z : n → ℂ)
    (h : ∀ i, ‖z i‖ = 1) : IsUnitary (Matrix.diagonal z) :=
  (isUnitary_diagonal_iff z).2 h

theorem wordEval_nil {K : ℕ} : wordEval ([] : List (Matrix (Fin K) (Fin K) ℂ)) = 1 := by
  simp [wordEval]

theorem wordEval_cons {K : ℕ} (g : Matrix (Fin K) (Fin K) ℂ)
    (l : List (Matrix (Fin K) (Fin K) ℂ)) : wordEval (g :: l) = g * wordEval l := by
  simp [wordEval, List.prod_cons]

theorem wordEval_append {K : ℕ} (l₁ l₂ : List (Matrix (Fin K) (Fin K) ℂ)) :
    wordEval (l₁ ++ l₂) = wordEval l₁ * wordEval l₂ := by
  simp [wordEval, List.prod_append]

theorem exists_word_of_mem_generatedBy {K : ℕ}
    (gens : Set (Matrix (Fin K) (Fin K) ℂ)) (g : Matrix (Fin K) (Fin K) ℂ)
    (hg : g ∈ generatedBy gens) :
    ∃ word : List (Matrix (Fin K) (Fin K) ℂ),
      (∀ x ∈ word, x ∈ gens) ∧ wordEval word = g := by
  classical
  unfold generatedBy at hg
  refine Submonoid.closure_induction
    (motive := fun x _ => ∃ word : List (Matrix (Fin K) (Fin K) ℂ),
      (∀ y ∈ word, y ∈ gens) ∧ wordEval word = x) ?_ ?_ ?_ hg
  · intro x hx
    exact ⟨[x], by simp [hx, wordEval]⟩
  · exact ⟨[], by simp [wordEval]⟩
  · intro x y _ _ ihx ihy
    obtain ⟨l₁, h₁, e₁⟩ := ihx
    obtain ⟨l₂, h₂, e₂⟩ := ihy
    refine ⟨l₁ ++ l₂, ?_, ?_⟩
    · intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact h₁ z hz
      · exact h₂ z hz
    · rw [wordEval_append, e₁, e₂]

theorem dense_word_approx {n : Type*} [Fintype n] {K : ℕ}
    (gens : Set (Matrix (Fin K) (Fin K) ℂ)) (target : Set (Matrix (Fin K) (Fin K) ℂ))
    (h : DenseIn target (generatedBy gens)) :
    ∀ U ∈ target, ∀ ε : ℝ, 0 < ε →
      ∃ word : List (Matrix (Fin K) (Fin K) ℂ),
        (∀ g ∈ word, g ∈ gens) ∧ entryDist (wordEval word) U < ε := by
  intro U hU ε hε
  obtain ⟨g, hg, hd⟩ := h U hU ε hε
  obtain ⟨word, hword, hval⟩ := exists_word_of_mem_generatedBy gens g hg
  exact ⟨word, hword, by rw [hval]; exact hd⟩

theorem one_le_polyLogBound (δ : ℝ) : 1 ≤ polyLogBound δ := by
  unfold polyLogBound
  exact Nat.le_add_left 1 _

theorem polyLogBound_pos (δ : ℝ) : 0 < polyLogBound δ :=
  lt_of_lt_of_le Nat.zero_lt_one (one_le_polyLogBound δ)

theorem promise_decide_yes {a r : ℂ} (ha : ‖a‖ ≤ 1) (hp : 2 / 3 ≤ ‖a‖ ^ 2)
    (h : ‖r - a‖ ≤ 1 / 100) : 1 / 2 ≤ ‖r‖ ^ 2 := by
  have hkey : ‖a‖ - ‖r‖ ≤ ‖r - a‖ := by
    simpa [norm_sub_rev] using norm_sub_norm_le a r
  have ha0 : 0 ≤ ‖a‖ := norm_nonneg _
  have hr0 : 0 ≤ ‖r‖ := norm_nonneg _
  have h0 : 0 ≤ ‖a‖ - 1 / 100 := by nlinarith
  have hge : ‖a‖ - 1 / 100 ≤ ‖r‖ := by linarith
  have hpow : (‖a‖ - 1 / 100) ^ 2 ≤ ‖r‖ ^ 2 := by
    nlinarith [sq_nonneg ((‖a‖ - 1 / 100) - ‖r‖), sq_nonneg (‖r‖ - (‖a‖ - 1 / 100))]
  nlinarith [hpow, hp, ha]

theorem promise_decide_no {a r : ℂ} (hp : ‖a‖ ^ 2 ≤ 1 / 3)
    (h : ‖r - a‖ ≤ 1 / 100) : ‖r‖ ^ 2 ≤ 1 / 2 := by
  have hkey : ‖r‖ - ‖a‖ ≤ ‖r - a‖ := by
    simpa [norm_sub_rev] using norm_sub_norm_le r a
  have ha0 : 0 ≤ ‖a‖ := norm_nonneg _
  have hr0 : 0 ≤ ‖r‖ := norm_nonneg _
  have hle : ‖r‖ ≤ ‖a‖ + 1 / 100 := by linarith
  have ha1 : ‖a‖ ≤ 1 := by nlinarith [sq_nonneg (‖a‖ - 1), sq_nonneg (‖a‖ + 1)]
  nlinarith [sq_nonneg (‖r‖ - ‖a‖), sq_nonneg (‖a‖ + 1 / 100)]

theorem dotProduct_smul_right {ι : Type*} [Fintype ι] (v w : ι → ℂ) (d : ℂ) :
    v ⬝ᵥ (d • w) = d * (v ⬝ᵥ w) := by
  rw [dotProduct, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem mulVec_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ℂ) (ψ : ι → ℂ) :
    (d • (1 : Matrix ι ι ℂ)).mulVec ψ = d • ψ := by
  funext i
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · simp [Pi.smul_apply]
  · intro j _ hji
    have hij : i ≠ j := fun h => hji h.symm
    simp [Matrix.smul_apply, hij]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem dotProduct_star_eq_ofReal {ι : Type*} [Fintype ι] (u : ι → ℂ) :
    (star u) ⬝ᵥ u = ((∑ i, Complex.normSq (u i) : ℝ) : ℂ) := by
  rw [dotProduct]
  rw [show (∑ i, star u i * u i) = ∑ i, (Complex.normSq (u i) : ℂ) from
    Finset.sum_congr rfl fun i _ => by
      rw [Pi.star_apply, mul_comm]
      exact Complex.mul_conj (u i)]
  rw [Complex.ofReal_sum]

theorem sum_normSq_eq_re_dotProduct {ι : Type*} [Fintype ι] (u : ι → ℂ) :
    ∑ i, Complex.normSq (u i) = Complex.re ((star u) ⬝ᵥ u) := by
  rw [dotProduct_star_eq_ofReal, Complex.ofReal_re]

theorem re_dotProduct_mulVec {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) (ψ : ι → ℂ) :
    Complex.re ((star (A.mulVec ψ)) ⬝ᵥ (A.mulVec ψ))
      = Complex.re ((star ψ) ⬝ᵥ ((Matrix.conjTranspose A * A).mulVec ψ)) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

theorem conjTranspose_smul_mul_self {n : Type*} [Fintype n] [DecidableEq n]
    (c : ℂ) (U : Matrix n n ℂ) (hU : IsUnitary U) :
    (c • U).conjTranspose * (c • U) = (Complex.normSq c : ℂ) • (1 : Matrix n n ℂ) ∧
    (c • U) * (c • U).conjTranspose = (Complex.normSq c : ℂ) • (1 : Matrix n n ℂ) := by
  have hc : star c * c = (Complex.normSq c : ℂ) := by
    rw [mul_comm]
    simpa using Complex.mul_conj c
  constructor
  · rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hU.2, hc]
  · rw [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hU.1, hc]

end Qatlib.Papers.PottsTutte07.MainResults
