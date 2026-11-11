/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Data.Matrix.Mul

set_option backward.isDefEq.respectTransparency false

/-! Expectation framework over finite product sample spaces for
"A simple analysis of a quantum-inspired algorithm for solving
low-rank linear systems" (arXiv:2508.13108, 2025).

The paper's randomness is a fixed number of independent categorical
draws (rows sampled with replacement, each equal to `r` with
probability `p r`). We model the sample space directly as the function
space `Fin R → n` with product weights `∏ j, p (ρ j)`, so expectations
are finite sums and independence is structural:

- `expProd p g = ∑ ρ, (∏ j, p (ρ j)) * g ρ` is the expectation of `g`
  under `R` independent draws.
- `expProd_one`: the product distribution is normalised.
- `expProd_const`: expectations of constants.
- `expProd_coord`: the single-draw marginal
  `E[f (ρ j)] = ∑ r, p r * f r`.
- `expProd_pair`: distinct draws are independent,
  `E[f (ρ j) * g (ρ l)] = E[f] * E[g]` for `j ≠ l`.
- `expProd_sum`: expectation commutes with finite sums.

On this framework we prove the paper's **Lemma A.1**
(`thm:expected_norm_sum`), the iid second-moment identity behind every
deferred proof: for `R` independent copies `Z (ρ j)` of a
matrix-valued statistic `Z` of a single draw,

`E‖(1/R) Σ_j Z_j‖_F² = (1/R) E‖Z‖_F² + (1 − 1/R) ‖E Z‖_F²`,

restricted to single-draw statistics, with the Frobenius square `frob2`
as a finite entry sum over the index product.

No axiom beyond the three standard ones, no `sorry`. -/
set_option autoImplicit false

namespace Qatlib.Papers.LowRankSolve25.MainResults.RowSampling

open Finset

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Splitting off the first draw: `(Fin (R+1) → n) ≃ (n × (Fin R → n))`
via `Fin.cons`. -/
def consEquiv (n : Type) [Fintype n] [DecidableEq n] (R : ℕ) :
    (Fin (R + 1) → n) ≃ (n × (Fin R → n)) where
  toFun ρ := (ρ 0, fun j => ρ j.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv ρ := by
    funext j
    match j with
    | 0 => rfl
    | ⟨j + 1, _⟩ => rfl
  right_inv x := by rw [Prod.ext_iff]; exact ⟨rfl, rfl⟩

/-- Expectation under `R` independent categorical draws with weights
`p`: the finite sum over the sample space `Fin R → n` against the
product weights. -/
def expProd (p : n → ℝ) {R : ℕ} (g : (Fin R → n) → ℝ) : ℝ :=
  ∑ ρ : Fin R → n, (∏ j, p (ρ j)) * g ρ

omit [DecidableEq n] in
/-- The expectation of a constant. -/
lemma expProd_const (p : n → ℝ) {R : ℕ} (c : ℝ) :
    expProd p (fun _ : Fin R → n => c) = c * expProd p (fun _ : Fin R → n => 1) := by
  show ∑ ρ : Fin R → n, (∏ j, p (ρ j)) * c
      = c * ∑ ρ : Fin R → n, (∏ j, p (ρ j)) * 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ρ _ => by ring

omit [DecidableEq n] in
/-- A constant factor leaves the expectation. -/
lemma expProd_const_mul (p : n → ℝ) {R : ℕ} (c : ℝ) (F : (Fin R → n) → ℝ) :
    expProd p (fun ρ => c * F ρ) = c * expProd p F := by
  show ∑ ρ : Fin R → n, (∏ j, p (ρ j)) * (c * F ρ)
      = c * ∑ ρ : Fin R → n, (∏ j, p (ρ j)) * F ρ
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun ρ _ => by ring

omit [DecidableEq n] in
/-- A constant right-factor leaves the expectation. -/
lemma expProd_mul_const (p : n → ℝ) {R : ℕ} (c : ℝ) (F : (Fin R → n) → ℝ) :
    expProd p (fun ρ => F ρ * c) = expProd p F * c := by
  show ∑ ρ : Fin R → n, (∏ j, p (ρ j)) * (F ρ * c)
      = (∑ ρ : Fin R → n, (∏ j, p (ρ j)) * F ρ) * c
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun ρ _ => by ring

omit [DecidableEq n] in
/-- Expectation is additive. -/
lemma expProd_add (p : n → ℝ) {R : ℕ} (F G : (Fin R → n) → ℝ) :
    expProd p (fun ρ => F ρ + G ρ) = expProd p F + expProd p G := by
  show ∑ ρ : Fin R → n, (∏ j, p (ρ j)) * (F ρ + G ρ)
      = (∑ ρ : Fin R → n, (∏ j, p (ρ j)) * F ρ)
          + ∑ ρ : Fin R → n, (∏ j, p (ρ j)) * G ρ
  simp only [mul_add, Finset.sum_add_distrib]

/-- Peeling one draw off: the `R+1`-draw expectation is the weighted
sum of the `R`-draw expectations with the first draw fixed. -/
lemma expProd_succ (p : n → ℝ) {R : ℕ} (h : (Fin (R + 1) → n) → ℝ) :
    expProd p h = ∑ r, p r * expProd p (fun ρ' => h (Fin.cons r ρ')) := by
  have key : ∀ ρ : Fin (R + 1) → n,
      (∏ j, p (ρ j)) * h ρ
        = (p (ρ 0) * ∏ j : Fin R, p (ρ j.succ))
            * h (Fin.cons (ρ 0) (fun k : Fin R => ρ k.succ)) := by
    intro ρ
    have hcons : Fin.cons (ρ 0) (fun k : Fin R => ρ k.succ) = ρ := by
      funext j
      match j with
      | 0 => rfl
      | ⟨j + 1, _⟩ => rfl
    simp only [hcons, Fin.prod_univ_succ, mul_assoc]
  unfold expProd
  rw [Fintype.sum_equiv (consEquiv n R) (fun ρ => (∏ j, p (ρ j)) * h ρ)
    (fun x => (p x.1 * ∏ j, p (x.2 j)) * h (Fin.cons x.1 x.2)) key,
    Fintype.sum_prod_type]
  simp only [Finset.mul_sum, mul_assoc]

/-- The product distribution of the weights `p` is normalised. -/
lemma expProd_one (p : n → ℝ) (hp : ∑ r, p r = 1) {R : ℕ} :
    expProd p (fun _ : Fin R → n => 1) = 1 := by
  induction R with
  | zero =>
      unfold expProd
      rw [Finset.univ_unique]
      simp
  | succ R ih =>
      rw [expProd_succ]
      simp only [ih, mul_one, hp]

/-- **Single-draw marginal**: a statistic of one draw has the weighted
average as its expectation. -/
lemma expProd_coord (p : n → ℝ) (hp : ∑ r, p r = 1) {R : ℕ}
    (j : Fin R) (f : n → ℝ) :
    expProd p (fun ρ => f (ρ j)) = ∑ r, p r * f r := by
  induction R with
  | zero => exact j.elim0
  | succ R ih =>
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', hj⟩
      · rw [expProd_succ]
        simp only [Fin.cons_zero, expProd_const, expProd_one p hp, mul_one]
      · rw [hj, expProd_succ]
        simp only [Fin.cons_succ, ih j']
        rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) =>
          mul_comm (p x) (∑ r, p r * f r)), ← Finset.mul_sum, hp, mul_one]

/-- **Independence of distinct draws**: the expectation of a product of
statistics of two distinct draws factorises into the marginals. -/
lemma expProd_pair (p : n → ℝ) (hp : ∑ r, p r = 1) {R : ℕ}
    {j l : Fin R} (hjl : j ≠ l) (f g : n → ℝ) :
    expProd p (fun ρ => f (ρ j) * g (ρ l))
      = (∑ r, p r * f r) * (∑ r, p r * g r) := by
  induction R with
  | zero => exact j.elim0
  | succ R ih =>
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', hj⟩
      · rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l', hl⟩
        · exact absurd rfl hjl
        · rw [hl, expProd_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, expProd_const_mul,
            expProd_coord p hp l' g, ← mul_assoc]
          rw [Finset.sum_mul]
      · rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l', hl⟩
        · rw [hj, expProd_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, expProd_mul_const,
            expProd_coord p hp j' f]
          rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) =>
            mul_left_comm (p x) (∑ r, p r * f r) (g x)), ← Finset.mul_sum]
        · have hjl' : j' ≠ l' := by
            intro h
            apply hjl
            rw [hj, hl, h]
          rw [hj, hl, expProd_succ]
          simp only [Fin.cons_succ, ih hjl']
          rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) =>
            mul_comm (p x) ((∑ r, p r * f r) * ∑ r, p r * g r)),
            ← Finset.mul_sum, hp, mul_one]

omit [DecidableEq n] in
/-- Expectation commutes with finite sums. -/
lemma expProd_sum (p : n → ℝ) {R : ℕ} {ι : Type} [Fintype ι]
    (s : Finset ι) (F : ι → (Fin R → n) → ℝ) :
    expProd p (fun ρ => ∑ i ∈ s, F i ρ) = ∑ i ∈ s, expProd p (F i) := by
  show ∑ ρ : Fin R → n, (∏ j, p (ρ j)) * (∑ i ∈ s, F i ρ)
      = ∑ i ∈ s, ∑ ρ : Fin R → n, (∏ j, p (ρ j)) * F i ρ
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

/-! ## Quadratic expansion of entry sums -/

/-- Expanding a squared finite sum into diagonal and off-diagonal
parts. -/
lemma sq_sum_expand {ι : Type} [Fintype ι] [DecidableEq ι] (x : ι → ℝ) :
    (∑ j, x j) ^ 2 = ∑ j, x j ^ 2 + ∑ j, ∑ l ∈ Finset.univ.erase j, x j * x l := by
  rw [sq, Finset.sum_mul_sum, Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) =>
    (Finset.add_sum_erase Finset.univ (fun l => x j * x l) (Finset.mem_univ j)).symm)]
  rw [Finset.sum_add_distrib]
  simp only [sq]

/-- The entrywise quadratic identity behind Lemma A.1: the squared sum
over entries splits into diagonal and off-diagonal contributions. -/
lemma entry_sq_quad {κ ι : Type} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (h : ι → κ → ℝ) :
    (∑ k, (∑ j, h j k) ^ 2)
      = ∑ j, ∑ k, (h j k) ^ 2
          + ∑ j, ∑ l ∈ Finset.univ.erase j, ∑ k, h j k * h l k := by
  rw [Finset.sum_congr rfl (fun k _ => sq_sum_expand (fun j => h j k)),
    Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_comm
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => Finset.sum_comm)

/-! ## Frobenius square and the iid second-moment identity -/

variable {a b : Type} [Fintype a] [Fintype b]

/-- The squared Frobenius norm as a finite sum over the index product. -/
def frob2 (M : Matrix a b ℝ) : ℝ := ∑ k : a × b, (M k.1 k.2) ^ 2

/-- The entrywise Frobenius inner product. -/
def innerF (X Y : Matrix a b ℝ) : ℝ := ∑ k : a × b, X k.1 k.2 * Y k.1 k.2

/-- Scaling a matrix scales its squared Frobenius norm by the square. -/
lemma frob2_smul (c : ℝ) (M : Matrix a b ℝ) :
    frob2 (c • M) = c ^ 2 * frob2 M := by
  unfold frob2
  have h : ∀ k ∈ (Finset.univ : Finset (a × b)),
      ((c • M) k.1 k.2) ^ 2 = (M k.1 k.2) ^ 2 * c ^ 2 := by
    intro k _
    rw [Matrix.smul_apply]
    ring
  rw [Finset.sum_congr rfl (fun k hk => h k hk), ← Finset.sum_mul]
  exact mul_comm _ _

/-- The Frobenius square of a finite matrix sum, expanded. -/
lemma frob2_sum {R : ℕ} (Z : Fin R → Matrix a b ℝ) :
    frob2 (∑ j, Z j)
      = ∑ j, frob2 (Z j) + ∑ j, ∑ l ∈ Finset.univ.erase j, innerF (Z j) (Z l) := by
  have hsum : ∀ k : a × b, (∑ j, Z j) k.1 k.2 = ∑ j, Z j k.1 k.2 :=
    fun (k : a × b) => Matrix.sum_apply k.1 k.2 Finset.univ Z
  unfold frob2 innerF
  simp only [hsum]
  exact entry_sq_quad (fun (j : Fin R) (k : a × b) => Z j k.1 k.2)

/-- The expectation of a matrix-valued statistic, entrywise. -/
def emat (p : n → ℝ) (Z : n → Matrix a b ℝ) : Matrix a b ℝ :=
  Matrix.of fun c d => ∑ r, p r * Z r c d

/-- The Frobenius square is the inner product with itself. -/
lemma frob2_eq_innerF (M : Matrix a b ℝ) : frob2 M = innerF M M := by
  unfold frob2 innerF
  exact Finset.sum_congr rfl (fun k _ => sq (M k.1 k.2))

/-- **Lemma A.1 (thm:expected_norm_sum), concluding display**: for `R`
independent copies of a matrix-valued statistic `Z` of one draw, the
squared Frobenius norm of the sample mean satisfies the exact
second-moment identity

`E‖(1/R) Σ_j Z_j‖_F² = (1/R) E‖Z‖_F² + (1 − 1/R) ‖E Z‖_F²`. -/
theorem exp_frob2_mean (p : n → ℝ) (hp : ∑ r, p r = 1) {R : ℕ} [NeZero R]
    (Z : n → Matrix a b ℝ) :
    expProd p (fun ρ : Fin R → n => frob2 ((R : ℝ)⁻¹ • ∑ j, Z (ρ j)))
      = (R : ℝ)⁻¹ * (∑ r, p r * frob2 (Z r))
        + (1 - (R : ℝ)⁻¹) * frob2 (emat p Z) := by
  have hcard : ∀ j : Fin R, (∑ l ∈ Finset.univ.erase j, frob2 (emat p Z))
      = ((R : ℝ) - 1) * frob2 (emat p Z) := by
    intro j
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul (R := ℝ), smul_eq_mul,
      Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (Nat.pos_of_ne_zero (NeZero.ne R))]
    norm_num
  have hEcoord : ∀ j : Fin R, expProd p (fun ρ : Fin R → n => frob2 (Z (ρ j)))
      = ∑ r, p r * frob2 (Z r) := fun j => expProd_coord p hp j (fun r => frob2 (Z r))
  have hEpairsq : ∀ (j l : Fin R), j ≠ l →
      expProd p (fun ρ : Fin R → n => innerF (Z (ρ j)) (Z (ρ l)))
        = frob2 (emat p Z) := by
    intro j l hjl
    have hpair : ∀ k : a × b,
        expProd p (fun ρ : Fin R → n => Z (ρ j) k.1 k.2 * Z (ρ l) k.1 k.2)
          = (∑ r, p r * Z r k.1 k.2) * (∑ r, p r * Z r k.1 k.2) :=
      fun k => expProd_pair p hp hjl (fun r => Z r k.1 k.2) (fun r => Z r k.1 k.2)
    unfold innerF emat frob2
    rw [expProd_sum, Finset.sum_congr rfl (fun k _ => hpair k)]
    exact Finset.sum_congr rfl fun k _ => (sq (∑ r, p r * Z r k.1 k.2)).symm
  have hcardj : (∑ j : Fin R, frob2 (emat p Z)) = ((R : ℝ)) * frob2 (emat p Z) := by
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul (R := ℝ), smul_eq_mul,
      Finset.card_univ, Fintype.card_fin]
  have hS : (∑ j : Fin R, ∑ r, p r * frob2 (Z r)) = ((R : ℝ)) * (∑ r, p r * frob2 (Z r)) := by
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul (R := ℝ), smul_eq_mul,
      Finset.card_univ, Fintype.card_fin]
  simp only [frob2_smul, frob2_sum, expProd_const_mul, expProd_add,
    expProd_sum, hEcoord]
  rw [hS, Finset.sum_congr rfl (fun j _ =>
    Finset.sum_congr rfl (fun l hl =>
      hEpairsq j l (Ne.symm (Finset.ne_of_mem_erase hl)))),
    Finset.sum_congr rfl (fun j _ => hcard j), ← Finset.mul_sum, hcardj]
  have hR : ((R : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne R)
  field_simp

end Qatlib.Papers.LowRankSolve25.MainResults.RowSampling
