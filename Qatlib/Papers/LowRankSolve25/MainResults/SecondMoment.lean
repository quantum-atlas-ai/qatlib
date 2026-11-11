/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowRankSolve25.MainResults.RowSampling

set_option backward.isDefEq.respectTransparency false

/-! Second moments of the row-sampled estimator for
"A simple analysis of a quantum-inspired algorithm for solving
low-rank linear systems" (arXiv:2508.13108, 2025).

**Lemma 2.1 (`thm:Mk_bd`)**: for the row-sampled estimator

`M_k = (1/R) Σ_j p(ρ_j)⁻¹ a_{ρ_j} a_{ρ_j}ᵀ`,

with `R` draws sampled i.i.d. from the row-norm-squared distribution
`p r = ‖a_r‖² / ‖A‖_F²`, we have `E[M_k] = AᵀA` (for any non-vanishing
sampling distribution) and

`E[M_k²] = (1/R) ‖A‖_F² AᵀA + (1 − 1/R) (AᵀA)²`,

the exact second-moment identity driving the paper's convergence
analysis. Proofs are entrywise computations on the `RowSampling`
finite product-space expectation: diagonal terms collapse through
`p r = ‖a_r‖²/‖A‖_F²`, off-diagonal terms factorise through the
independence of distinct draws (`expProd_pair`).

No axiom beyond the three standard ones, no `sorry`. -/
set_option autoImplicit false

namespace Qatlib.Papers.LowRankSolve25.MainResults.SecondMoment

open Finset
open scoped Matrix
open Qatlib.Papers.LowRankSolve25.MainResults.RowSampling

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The squared norm of one row. -/
def rowN2 (A : Matrix n m ℝ) (r : n) : ℝ := ∑ c, (A r c) ^ 2

/-- The row-sampled estimator `M_k`, entrywise. -/
noncomputable def Mk (p : n → ℝ) (A : Matrix n m ℝ) {R : ℕ} (ρ : Fin R → n) : Matrix m m ℝ :=
  Matrix.of fun c d => (R : ℝ)⁻¹ * ∑ j, (p (ρ j))⁻¹ * A (ρ j) c * A (ρ j) d

/-- Entrywise expectation of a matrix-valued statistic. -/
def ematM (p : n → ℝ) {R : ℕ} (X : (Fin R → n) → Matrix m m ℝ) : Matrix m m ℝ :=
  Matrix.of fun c d => expProd p (fun ρ : Fin R → n => X ρ c d)

omit [Fintype m] [DecidableEq m] in
/-- **Lemma 2.1, first part**: the row-sampled estimator is unbiased,
`E[M_k] = AᵀA`, for any sampling weights with `p r ≠ 0` and `Σp = 1`. -/
theorem exp_Mk (p : n → ℝ) (hp1 : ∑ r, p r = 1) (hp0 : ∀ r, p r ≠ 0)
    (A : Matrix n m ℝ) {R : ℕ} [NeZero R] :
    ematM p (R := R) (Mk p A) = Aᵀ * A := by
  have hR : ((R : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne R)
  apply Matrix.ext
  intro c d
  have inner : ∀ j : Fin R,
      expProd p (fun ρ : Fin R → n => (p (ρ j))⁻¹ * A (ρ j) c * A (ρ j) d)
        = ∑ r, A r c * A r d := by
    intro j
    rw [expProd_coord p hp1 j (fun r => (p r)⁻¹ * A r c * A r d)]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    field_simp [hp0 r]
  unfold ematM Mk
  simp only [Matrix.of_apply, expProd_const_mul, expProd_sum, inner,
    Finset.sum_const, ← Nat.cast_smul_eq_nsmul (R := ℝ), smul_eq_mul,
    Finset.card_univ, Fintype.card_fin, Matrix.mul_apply, Matrix.transpose_apply]
  rw [← mul_assoc, inv_mul_cancel₀ hR, one_mul]

/-- Splitting a double sum into diagonal and off-diagonal parts. -/
lemma pair_split {ι : Type} [Fintype ι] [DecidableEq ι] (F : ι → ι → ℝ) :
    (∑ j, ∑ l, F j l) = (∑ j, F j j) + (∑ j, ∑ l ∈ Finset.univ.erase j, F j l) := by
  rw [Finset.sum_congr rfl (fun j _ =>
    (Finset.add_sum_erase Finset.univ (F j) (Finset.mem_univ j)).symm),
    Finset.sum_add_distrib]

omit [DecidableEq n] [DecidableEq m] in
/-- The Frobenius square is the sum of squared row norms. -/
lemma frob2_eq_sum_rowN2 (A : Matrix n m ℝ) :
    frob2 A = ∑ r, rowN2 A r := by
  unfold frob2 rowN2
  rw [Fintype.sum_prod_type]

omit [DecidableEq n] [DecidableEq m] in
/-- The row-norm-squared weights are normalised. -/
lemma sum_p_eq_one (A : Matrix n m ℝ) (p : n → ℝ)
    (hp : ∀ r, p r = rowN2 A r / frob2 A) (hf : frob2 A ≠ 0) :
    ∑ r, p r = 1 := by
  rw [Finset.sum_congr rfl (fun r _ => hp r), ← Finset.sum_div, ← frob2_eq_sum_rowN2,
    div_self hf]

omit [DecidableEq m] in
/-- **Lemma 2.1, second part**: for row-norm-squared sampling
`p r = ‖a_r‖²/‖A‖_F²` with non-vanishing rows, the second moment of the
row-sampled estimator is exactly

`E[M_k²] = (1/R) ‖A‖_F² AᵀA + (1 − 1/R) (AᵀA)²`. -/
theorem exp_Mk_sq (p : n → ℝ) (A : Matrix n m ℝ) {R : ℕ} [NeZero R]
    (hp : ∀ r, p r = rowN2 A r / frob2 A) (hf : frob2 A ≠ 0)
    (hr : ∀ r, rowN2 A r ≠ 0) :
    ematM p (R := R) (fun ρ => Mk p A ρ * Mk p A ρ)
      = (frob2 A / (R : ℝ)) • (Aᵀ * A) + (1 - (R : ℝ)⁻¹) • (Aᵀ * A * Aᵀ * A) := by
  have hp1 : ∑ r, p r = 1 := sum_p_eq_one A p hp hf
  have hR : ((R : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne R)
  have hfnn : 0 ≤ frob2 A := by
    unfold frob2
    exact Finset.sum_nonneg (fun k _ => sq_nonneg _)
  have hfpos : 0 < frob2 A := lt_of_le_of_ne hfnn (fun h => hf h.symm)
  have hp0 : ∀ r, p r ≠ 0 := by
    intro r h0
    apply hr r
    have h1 : rowN2 A r / frob2 A = 0 := by rw [← hp r, h0]
    rw [div_eq_zero_iff] at h1
    rcases h1 with h | h
    · exact h
    · exact absurd h hf
  have hpinv : ∀ r, (p r)⁻¹ * rowN2 A r = frob2 A := by
    intro r
    rw [hp r, inv_div, div_mul_cancel₀ (frob2 A) (hr r)]
  apply Matrix.ext
  intro c d
  rw [Matrix.mul_assoc]
  have hcancel : ∀ (r : n) (x y : m),
      p r * ((p r)⁻¹ * A r x * A r y) = A r x * A r y := by
    intro r x y
    rw [← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (hp0 r), one_mul]
  have hpinvsum : ∀ r : n,
      p r * ((p r)⁻¹ * A r c * (p r)⁻¹ * A r d * rowN2 A r)
        = frob2 A * (A r c * A r d) := by
    intro r
    have hrw : p r * ((p r)⁻¹ * A r c * (p r)⁻¹ * A r d * rowN2 A r)
        = (p r * (p r)⁻¹) * ((p r)⁻¹ * rowN2 A r) * (A r c * A r d) := by ring
    rw [hrw, mul_inv_cancel₀ (hp0 r), hpinv r, one_mul]
  have hdiag : ∀ j : Fin R, expProd p (fun ρ : Fin R → n =>
      (p (ρ j))⁻¹ * A (ρ j) c * (p (ρ j))⁻¹ * A (ρ j) d * rowN2 A (ρ j))
      = frob2 A * (∑ r, A r c * A r d) := by
    intro j
    rw [expProd_coord p hp1 j (fun r => (p r)⁻¹ * A r c * (p r)⁻¹ * A r d * rowN2 A r),
      Finset.sum_congr rfl (fun r _ => hpinvsum r), ← Finset.mul_sum]
  have hsumrow : ∀ r : n,
      ∑ e : m, (p r)⁻¹ * A r c * A r e * ((p r)⁻¹ * A r e * A r d)
        = (p r)⁻¹ * A r c * (p r)⁻¹ * A r d * rowN2 A r := by
    intro r
    have h : ∀ e ∈ (Finset.univ : Finset m),
        (p r)⁻¹ * A r c * A r e * ((p r)⁻¹ * A r e * A r d)
          = ((p r)⁻¹ * A r c * (p r)⁻¹ * A r d) * (A r e * A r e) :=
      fun e _ => by ring
    rw [Finset.sum_congr rfl h, ← Finset.mul_sum]
    congr 1
    unfold rowN2
    exact Finset.sum_congr rfl (fun e _ => (pow_two (A r e)).symm)
  have hdiagsum : ∀ j : Fin R, ∑ e : m, expProd p (fun ρ : Fin R → n =>
      (p (ρ j))⁻¹ * A (ρ j) c * A (ρ j) e * ((p (ρ j))⁻¹ * A (ρ j) e * A (ρ j) d))
      = frob2 A * (∑ r, A r c * A r d) := by
    intro j
    rw [← expProd_sum]
    simp only [hsumrow]
    exact hdiag j
  have hoffE : ∀ (e : m) (j l : Fin R), j ≠ l →
      expProd p (fun ρ : Fin R → n =>
        (p (ρ j))⁻¹ * A (ρ j) c * A (ρ j) e * ((p (ρ l))⁻¹ * A (ρ l) e * A (ρ l) d))
      = (∑ r, A r c * A r e) * (∑ r, A r e * A r d) := by
    intro e j l hjl
    rw [expProd_pair p hp1 hjl (fun r => (p r)⁻¹ * A r c * A r e)
      (fun r => (p r)⁻¹ * A r e * A r d),
      Finset.sum_congr rfl (fun r _ => hcancel r c e),
      Finset.sum_congr rfl (fun r _ => hcancel r e d)]
  have hoffsum : ∀ (l j : Fin R), j ∈ Finset.univ.erase l →
      ∑ e : m, expProd p (fun ρ : Fin R → n =>
        (p (ρ j))⁻¹ * A (ρ j) c * A (ρ j) e * ((p (ρ l))⁻¹ * A (ρ l) e * A (ρ l) d))
      = ∑ e : m, (∑ r, A r c * A r e) * (∑ r, A r e * A r d) := by
    intro l j hj
    rw [Finset.sum_congr rfl (fun e _ => hoffE e j l (Finset.ne_of_mem_erase hj))]
  have hsplit : ∀ e : m,
      expProd p (fun ρ : Fin R → n =>
        (∑ j : Fin R, (p (ρ j))⁻¹ * A (ρ j) c * A (ρ j) e)
          * (∑ l : Fin R, (p (ρ l))⁻¹ * A (ρ l) e * A (ρ l) d))
      = ∑ l : Fin R, ∑ j : Fin R, expProd p (fun ρ : Fin R → n =>
          (p (ρ j))⁻¹ * A (ρ j) c * A (ρ j) e * ((p (ρ l))⁻¹ * A (ρ l) e * A (ρ l) d)) := by
    intro e
    unfold expProd
    beta_reduce
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun l _ => Finset.sum_comm)]
  have hsplitE : ∀ e : m,
      expProd p (fun ρ : Fin R → n =>
        ((R : ℝ)⁻¹ * ∑ j : Fin R, (p (ρ j))⁻¹ * A (ρ j) c * A (ρ j) e)
          * ((R : ℝ)⁻¹ * ∑ l : Fin R, (p (ρ l))⁻¹ * A (ρ l) e * A (ρ l) d))
      = ((R : ℝ)⁻¹ * (R : ℝ)⁻¹) * ∑ l : Fin R, ∑ j : Fin R,
          expProd p (fun ρ : Fin R → n =>
            (p (ρ j))⁻¹ * A (ρ j) c * A (ρ j) e * ((p (ρ l))⁻¹ * A (ρ l) e * A (ρ l) d)) := by
    intro e
    have hfn : (fun ρ : Fin R → n =>
        ((R : ℝ)⁻¹ * ∑ j : Fin R, (p (ρ j))⁻¹ * A (ρ j) c * A (ρ j) e)
          * ((R : ℝ)⁻¹ * ∑ l : Fin R, (p (ρ l))⁻¹ * A (ρ l) e * A (ρ l) d))
      = (fun ρ : Fin R → n =>
        (R : ℝ)⁻¹ * ((R : ℝ)⁻¹ * ((∑ j : Fin R, (p (ρ j))⁻¹ * A (ρ j) c * A (ρ j) e)
          * (∑ l : Fin R, (p (ρ l))⁻¹ * A (ρ l) e * A (ρ l) d)))) :=
      funext fun ρ => by ring
    rw [hfn, expProd_const_mul, expProd_const_mul, hsplit e]
    ring
  have hcarddiag : (∑ j : Fin R, frob2 A * (∑ r, A r c * A r d))
      = ((R : ℝ)) * (frob2 A * (∑ r, A r c * A r d)) := by
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul (R := ℝ), smul_eq_mul,
      Finset.card_univ, Fintype.card_fin]
  have hcardoff : ∀ j : Fin R,
      (∑ l ∈ Finset.univ.erase j, ∑ e : m, (∑ r, A r c * A r e) * (∑ r, A r e * A r d))
      = ((R : ℝ) - 1) * (∑ e : m, (∑ r, A r c * A r e) * (∑ r, A r e * A r d)) := by
    intro j
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul (R := ℝ), smul_eq_mul,
      Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub (Nat.pos_of_ne_zero (NeZero.ne R)), Nat.cast_one]
  have hcardoff2 : (∑ j : Fin R, ((R : ℝ) - 1)
      * (∑ e : m, (∑ r, A r c * A r e) * (∑ r, A r e * A r d)))
      = ((R : ℝ)) * ((R : ℝ) - 1)
          * (∑ e : m, (∑ r, A r c * A r e) * (∑ r, A r e * A r d)) := by
    rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul (R := ℝ), smul_eq_mul,
      Finset.card_univ, Fintype.card_fin]
    ring
  unfold ematM Mk
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [expProd_sum, Finset.sum_congr rfl (fun e _ => hsplitE e), ← Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_congr rfl (fun l _ => Finset.sum_comm)]
  rw [pair_split, Finset.sum_congr rfl (fun l _ => hdiagsum l),
    Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun j hj => hoffsum l j hj))]
  rw [hcarddiag, Finset.sum_congr rfl (fun l _ => hcardoff l), hcardoff2]
  have hfin : ∀ z F S Q : ℝ, z ≠ 0 →
      z⁻¹ * z⁻¹ * (z * (F * S) + z * (z - 1) * Q) = F / z * S + (1 - z⁻¹) * Q := by
    intro z F S Q hz
    field_simp
  rw [hfin ((R : ℝ)) (frob2 A) _ _ hR]

end Qatlib.Papers.LowRankSolve25.MainResults.SecondMoment
