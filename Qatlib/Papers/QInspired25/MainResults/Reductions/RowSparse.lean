/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QInspired25.MainResults.Model.Basic
import Qatlib.Papers.QInspired25.MainResults.Simulation.CoordinatorSimulation

set_option backward.isDefEq.respectTransparency false

/-!
# Row-sparse linear regression — Proposition 12 (pp. 8--9)

Fixed source: arXiv:2402.15686v3, Proposition 12 and its proof (pp. 8--9).

The construction (p. 8) is the following `kn × k` matrix, written in block form with
`k` row blocks of `n` rows each and `k` columns:

* block 1 (our index `0`): `β_A |1⟩_n` in column 1, zero elsewhere;
* block `j ≥ 2` (our index `j`): `|t_j⟩` in column `j`, zero elsewhere;

and the vector `b` with `β_b |1⟩_n` in the first block and `n |t_1⟩` in every other block.

The paper proves by direct computation

* `Aᵀ A = diag(β_A², 1, …, 1)`  (`rowSparseA_gram`),
* `Aᵀ b = β_A β_b |1⟩ + n Σ_{j≥2} ⟨t_1 | t_j⟩ |j⟩`  (`rowSparseA_mulVec_b`),
* `x* = (AᵀA)⁻¹ Aᵀ b` satisfies the normal equations (`rowSparse_normal_eq`) and is
  therefore the minimiser of `‖Ax - b‖` (`rowSparse_leastSquares`),
* `‖A‖_F² = β_A² + k - 1`, `σ_min = min{β_A, 1}` and the parameter formulas
  `κ² = max(β_A²,1)/min(β_A²,1)`, `κ_F² = (β_A² + k - 1)/min(β_A²,1)`, `γ² = ‖Ax*‖²/‖b‖²`,
* with `β_A² = β_b² = 1` one gets `κ² = 1`, `κ_F² = k`, `γ² = Θ(1/(kn²))`.

The final theorem composes the SQ-call lower bound with Theorem 10 and the cited
Set-Disjointness hardness (Proposition 5 of the source, formalised in `Model.Basic` as the
named hypothesis `SetDisjointnessHardness`).

Notation: we index the `k` row blocks by `Fin k` with `0` the public first block, and the
`n` coordinates by `Fin n`.  The vectors `u j` are the unit vectors `|t_j⟩ = t_j/α_j`; the
paper's normalisation constants `α_j` therefore do not appear explicitly, which is exactly
the content of the paper's "`|t_j⟩` is a unit vector" line.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QInspired25.MainResults.Reductions

open Qatlib.Papers.QInspired25.MainResults.Model
open Qatlib.Papers.QInspired25.MainResults.Simulation

/-! ## §1. The construction -/

/-- The row-sparse matrix `A` of Proposition 12 (p. 8): first block `β_A |1⟩⟨1|`, block `j`
contains `u j` in column `j`. -/
def rowSparseA {k n : ℕ} (βA : ℝ) (u : Fin k → Fin n → ℝ) : Matrix (Fin k × Fin n) (Fin k) ℝ :=
  fun r i =>
    if r.1.val = 0 then (if i.val = 0 then (if r.2.val = 0 then βA else 0) else 0)
    else (if i = r.1 then u r.1 r.2 else 0)

/-- The right-hand side `b` of Proposition 12 (p. 8): `β_b |1⟩` in the first block and
`n · w` in every other block, where `w = |t_1⟩` is the first player's unit vector. -/
def rowSparseb {k n : ℕ} (βb : ℝ) (w : Fin n → ℝ) : (Fin k × Fin n) → ℝ :=
  fun r => if r.1.val = 0 then (if r.2.val = 0 then βb else 0) else (n : ℝ) * w r.2

/-- The solution `x* = (AᵀA)⁻¹ Aᵀ b` of Proposition 12 (p. 8). -/
def xStar {k n : ℕ} (βA βb : ℝ) (u : Fin k → Fin n → ℝ) (w : Fin n → ℝ) : Fin k → ℝ :=
  fun i => if i.val = 0 then βb / βA else (n : ℝ) * innerVec (u i) w

/-- Squared Frobenius norm of a `(Fin k × Fin n) × Fin k` matrix. -/
def frobSqPair {k n : ℕ} (A : Matrix (Fin k × Fin n) (Fin k) ℝ) : ℝ :=
  ∑ j, ∑ l, ∑ i, A (j, l) i ^ 2

/-- Squared Euclidean norm of a `Fin k × Fin n`-indexed vector. -/
def frobSqPairVec {k n : ℕ} (v : Fin k × Fin n → ℝ) : ℝ :=
  ∑ j, ∑ l, v (j, l) ^ 2

/-! ## §2. Small summation helpers -/

/-- Squared Euclidean norm is homogeneous of degree two under scalar multiplication. -/
theorem frobSqVec_smul {n : ℕ} (c : ℝ) (v : Fin n → ℝ) :
    frobSqVec (fun i => c * v i) = c ^ 2 * frobSqVec v := by
  unfold frobSqVec
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `∑_{j : Fin k} (if j = 0 then c else d) = c + (k-1)·d` for `k ≥ 1`. -/
theorem sum_fin_ite_zero {k : ℕ} (hk : 0 < k) (c d : ℝ) :
    (∑ j : Fin k, if j.val = 0 then c else d) = c + ((k : ℝ) - 1) * d := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk)
  rw [Fin.sum_univ_succ]
  have hsucc : ∀ j : Fin k', (if (Fin.succ j).val = 0 then c else d) = d := by
    intro j
    have : (Fin.succ j).val ≠ 0 := by
      simp [Fin.val_succ]
    simp [this]
  simp only [Fin.val_zero, if_true, hsucc, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- `∑_{j : Fin k} (if j = 0 then c else 0) = c` for `k ≥ 1`. -/
theorem sum_fin_ite_zero_single {k : ℕ} (hk : 0 < k) (c : ℝ) :
    (∑ j : Fin k, if j.val = 0 then c else 0) = c := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk)
  rw [Fin.sum_univ_succ]
  have hsucc : ∀ j : Fin k', (if (Fin.succ j).val = 0 then c else 0) = 0 := by
    intro j
    have : (Fin.succ j).val ≠ 0 := by simp [Fin.val_succ]
    simp [this]
  simp only [Fin.val_zero, if_true, hsucc, add_zero]
  simp

/-- The `Fin n` sum of a product of two "single-coordinate" functions. -/
theorem sum_firstBlock {n : ℕ} (hn : 0 < n) (βA : ℝ) (P Q : Prop) [Decidable P] [Decidable Q] :
    (∑ l : Fin n, (if P then (if l.val = 0 then βA else 0) else 0) *
      (if Q then (if l.val = 0 then βA else 0) else 0)) =
      if P ∧ Q then βA ^ 2 else 0 := by
  by_cases hP : P <;> by_cases hQ : Q
  · simp only [hP, hQ, if_true, true_and]
    rw [Finset.sum_eq_single (⟨0, hn⟩)]
    · have h0 : ((⟨0, hn⟩ : Fin n)).val = 0 := rfl
      rw [h0]
      simp only [if_true]
      ring
    · intro l _ hl
      have hl0 : l.val ≠ 0 := by
        intro h; exact hl (Fin.ext (by simpa using h))
      simp [hl0]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp [hP, hQ]
  · simp [hP, hQ]
  · simp [hP, hQ]

/-- The `Fin n` sum of a product of `u` restricted by two propositions. -/
theorem sum_secondBlock {n : ℕ} (u : Fin n → ℝ) (P Q : Prop) [Decidable P] [Decidable Q] :
    (∑ l : Fin n, (if P then u l else 0) * (if Q then u l else 0)) =
      if P ∧ Q then frobSqVec u else 0 := by
  by_cases hP : P <;> by_cases hQ : Q
  · simp only [hP, hQ, if_true, true_and]
    unfold frobSqVec
    exact Finset.sum_congr rfl fun l _ => by ring
  · simp [hP, hQ]
  · simp [hP, hQ]
  · simp [hP, hQ]

/-- A block sum of `Aᵀb`. -/
theorem sum_firstB {n : ℕ} (hn : 0 < n) (βA βb : ℝ) (P : Prop) [Decidable P] :
    (∑ l : Fin n, (if P then (if l.val = 0 then βA else 0) else 0) *
      (if l.val = 0 then βb else 0)) = if P then βA * βb else 0 := by
  by_cases hP : P
  · simp only [hP, if_true]
    rw [Finset.sum_eq_single (⟨0, hn⟩)]
    · have h0 : ((⟨0, hn⟩ : Fin n)).val = 0 := rfl
      rw [h0]
      simp
    · intro l _ hl
      have hl0 : l.val ≠ 0 := by
        intro h; exact hl (Fin.ext (by simpa using h))
      simp [hl0]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp [hP]

/-- A block sum of `Aᵀb` for the non-first blocks. -/
theorem sum_secondB {n : ℕ} (u w : Fin n → ℝ) (c : ℝ) (P : Prop) [Decidable P] :
    (∑ l : Fin n, (if P then u l else 0) * (c * w l)) = if P then c * innerVec u w else 0 := by
  by_cases hP : P
  · simp only [hP, if_true]
    have : ∀ l : Fin n, u l * (c * w l) = c * (u l * w l) := fun l => by ring
    simp only [this]
    rw [← Finset.mul_sum]
    rfl
  · simp [hP]

/-! ## §3. `Aᵀ A = diag(β_A², 1, …, 1)` -/

/-- Gram matrix of the row-sparse instance matrix. -/
theorem rowSparseA_gram {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (βA : ℝ)
    (u : Fin k → Fin n → ℝ) (hunit : ∀ j : Fin k, frobSqVec (u j) = 1) :
    (rowSparseA βA u)ᵀ * rowSparseA βA u =
      Matrix.diagonal (fun i : Fin k => if i.val = 0 then βA ^ 2 else 1) := by
  ext i i'
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.diagonal_apply]
  have hT : ∀ p : Fin k × Fin n, (rowSparseA βA u)ᵀ i p = rowSparseA βA u p i := fun p => rfl
  simp only [hT]
  have hblock : ∀ j : Fin k,
      (∑ l : Fin n, rowSparseA βA u (j, l) i * rowSparseA βA u (j, l) i')
        = if j.val = 0 then (if i.val = 0 ∧ i'.val = 0 then βA ^ 2 else 0)
          else (if i = j ∧ i' = j then 1 else 0) := by
    intro j
    by_cases hj : j.val = 0
    · have hb : ∀ l : Fin n, rowSparseA βA u (j, l) i
          = if i.val = 0 then (if l.val = 0 then βA else 0) else 0 := by
        intro l; simp [rowSparseA, hj]
      have hb' : ∀ l : Fin n, rowSparseA βA u (j, l) i'
          = if i'.val = 0 then (if l.val = 0 then βA else 0) else 0 := by
        intro l; simp [rowSparseA, hj]
      simp only [hb, hb', sum_firstBlock hn, hj, if_true]
    · have hb : ∀ l : Fin n, rowSparseA βA u (j, l) i = if i = j then u j l else 0 := by
        intro l; simp [rowSparseA, hj]
      have hb' : ∀ l : Fin n, rowSparseA βA u (j, l) i' = if i' = j then u j l else 0 := by
        intro l; simp [rowSparseA, hj]
      simp only [hb, hb', sum_secondBlock, hj, if_false]
      rw [hunit j]
  simp only [hblock]
  by_cases hi : i.val = 0
  · have hii : i = ⟨0, hk⟩ := Fin.ext (by simpa using hi)
    rw [Finset.sum_eq_single (⟨0, hk⟩)]
    · simp only [hii, hi, Fin.ext_iff, true_and, if_true]
      by_cases h : i'.val = 0
      · simp [h]
      · simp [h]
        intro hh
        exact absurd hh.symm h
    · intro j _ hj
      have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext (by simpa using h))
      rw [if_neg hj0,
        if_neg (show ¬ (i = j ∧ i' = j) from fun h => hj (h.1.symm.trans hii))]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_single i]
    · simp [hi, eq_comm]
    · intro j _ hj
      by_cases hj0 : j.val = 0
      · rw [if_pos hj0,
          if_neg (show ¬ (i.val = 0 ∧ i'.val = 0) from fun h => hi h.1)]
      · rw [if_neg hj0,
          if_neg (show ¬ (i = j ∧ i' = j) from fun h => hj h.1.symm)]
    · intro h; exact absurd (Finset.mem_univ i) h

/-! ## §4. `Aᵀ b` -/

/-- Action of the row-sparse matrix on the source vector. -/
theorem rowSparseA_mulVec_b {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (βA βb : ℝ)
    (u : Fin k → Fin n → ℝ) (w : Fin n → ℝ) :
    (rowSparseA βA u)ᵀ *ᵥ rowSparseb βb w =
      fun i : Fin k => if i.val = 0 then βA * βb else (n : ℝ) * innerVec (u i) w := by
  funext i
  simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct, Fintype.sum_prod_type]
  have hblock : ∀ j : Fin k,
      (∑ l : Fin n, rowSparseA βA u (j, l) i * rowSparseb βb w (j, l))
        = if j.val = 0 then (if i.val = 0 then βA * βb else 0)
          else (if i = j then (n : ℝ) * innerVec (u j) w else 0) := by
    intro j
    by_cases hj : j.val = 0
    · have hb : ∀ l : Fin n, rowSparseA βA u (j, l) i
          = if i.val = 0 then (if l.val = 0 then βA else 0) else 0 := by
        intro l; simp [rowSparseA, hj]
      have hbv : ∀ l : Fin n, rowSparseb βb w (j, l) = if l.val = 0 then βb else 0 := by
        intro l; simp [rowSparseb, hj]
      simp only [hb, hbv, sum_firstB hn, hj, if_true]
    · have hb : ∀ l : Fin n, rowSparseA βA u (j, l) i = if i = j then u j l else 0 := by
        intro l; simp [rowSparseA, hj]
      have hbv : ∀ l : Fin n, rowSparseb βb w (j, l) = (n : ℝ) * w l := by
        intro l; simp [rowSparseb, hj]
      simp only [hb, hbv, sum_secondB, hj, if_false]
  simp only [hblock]
  by_cases hi : i.val = 0
  · have hii : i = ⟨0, hk⟩ := Fin.ext (by simpa using hi)
    rw [Finset.sum_eq_single (⟨0, hk⟩)]
    · simp [hii, hi]
    · intro j _ hj
      have hj0 : j.val ≠ 0 := fun h => hj (Fin.ext (by simpa using h))
      rw [if_neg hj0, if_neg (fun h => hj (h.symm.trans hii))]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_single i]
    · simp [hi]
    · intro j _ hj
      by_cases hj0 : j.val = 0
      · rw [if_pos hj0]; simp [hi]
      · rw [if_neg hj0, if_neg (Ne.symm hj)]
    · intro h; exact absurd (Finset.mem_univ i) h

/-! ## §5. `A x*` and the normal equations -/

/-- Action on the planted least-squares solution. -/
theorem rowSparseA_mulVec_xStar {k n : ℕ} (hk : 0 < k) (βA βb : ℝ)
    (u : Fin k → Fin n → ℝ) (w : Fin n → ℝ) (hβA : βA ≠ 0) :
    rowSparseA βA u *ᵥ xStar βA βb u w =
      fun r : Fin k × Fin n =>
        if r.1.val = 0 then (if r.2.val = 0 then βb else 0)
        else (n : ℝ) * (innerVec (u r.1) w * u r.1 r.2) := by
  funext r
  simp only [Matrix.mulVec, dotProduct, rowSparseA, xStar]
  by_cases hr : r.1.val = 0
  · rw [Finset.sum_eq_single (⟨0, hk⟩)]
    · by_cases hr2 : r.2.val = 0
      · simp [hr, hr2]
        field_simp
      · simp [hr, hr2]
    · intro i _ hi
      have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext (by simpa using h))
      simp [hr, hi0]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_single r.1]
    · simp [hr]
      ring
    · intro i _ hi; simp [hr, hi]
    · intro h; exact absurd (Finset.mem_univ r.1) h

/-- The block sum appearing in the normal equations. -/
theorem inner_normal {n : ℕ} (u w : Fin n → ℝ) (h : frobSqVec u = 1) :
    (∑ l : Fin n, u l * (innerVec u w * u l - w l)) = 0 := by
  have h1 : ∀ l : Fin n, u l * (innerVec u w * u l - w l)
      = innerVec u w * (u l ^ 2) - u l * w l := fun l => by ring
  simp only [h1]
  rw [Finset.sum_sub_distrib]
  have h2 : (∑ l : Fin n, innerVec u w * u l ^ 2) = innerVec u w * frobSqVec u := by
    rw [← Finset.mul_sum]
    rfl
  have h3 : (∑ l : Fin n, u l * w l) = innerVec u w := rfl
  rw [h2, h3, h, mul_one, sub_self]

/-- The normal equations hold for the planted solution. -/
theorem rowSparse_normal_eq {k n : ℕ} (hk : 0 < k) (_hn : 0 < n) (βA βb : ℝ)
    (u : Fin k → Fin n → ℝ) (hunit : ∀ j : Fin k, frobSqVec (u j) = 1) (w : Fin n → ℝ)
    (hβA : βA ≠ 0) :
    (rowSparseA βA u)ᵀ *ᵥ (rowSparseA βA u *ᵥ xStar βA βb u w - rowSparseb βb w) = 0 := by
  funext i
  have hx := rowSparseA_mulVec_xStar (k := k) (n := n) hk (βA := βA) (βb := βb) (u := u) (w := w) hβA
  rw [hx]
  simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct, Fintype.sum_prod_type, Pi.sub_apply,
    rowSparseb]
  have hblock : ∀ j : Fin k,
      (∑ l : Fin n, rowSparseA βA u (j, l) i *
        ((if j.val = 0 then (if l.val = 0 then βb else 0) else (n : ℝ) * (innerVec (u j) w * u j l))
         - (if j.val = 0 then (if l.val = 0 then βb else 0) else (n : ℝ) * w l))) = 0 := by
    intro j
    by_cases hj : j.val = 0
    · have hb : ∀ l : Fin n, rowSparseA βA u (j, l) i
          = if i.val = 0 then (if l.val = 0 then βA else 0) else 0 := by
        intro l; simp [rowSparseA, hj]
      simp only [hb, hj, if_true, sub_self, mul_zero, Finset.sum_const_zero]
    · have hb : ∀ l : Fin n, rowSparseA βA u (j, l) i = if i = j then u j l else 0 := by
        intro l; simp [rowSparseA, hj]
      simp only [hb, hj, if_false]
      by_cases hij : i = j
      · simp only [hij, if_true]
        have hterm : ∀ l : Fin n, u j l * ((n : ℝ) * (innerVec (u j) w * u j l) - (n : ℝ) * w l)
            = (n : ℝ) * (u j l * (innerVec (u j) w * u j l - w l)) := fun l => by ring
        simp only [hterm, ← Finset.mul_sum, inner_normal (u j) w (hunit j), mul_zero]
      · simp [hij]
  simp only [hblock, Finset.sum_const_zero, Pi.zero_apply]

/-- **Proposition 12, least-squares optimality (p. 8).**  `x*` is the minimiser of
`‖Ax - b‖`: every other `y` gives `‖Ay - b‖² = ‖Ax* - b‖² + ‖A(y - x*)‖²`. -/
theorem rowSparse_leastSquares {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (βA βb : ℝ)
    (u : Fin k → Fin n → ℝ) (hunit : ∀ j : Fin k, frobSqVec (u j) = 1) (w : Fin n → ℝ)
    (hβA : βA ≠ 0) (y : Fin k → ℝ) :
    frobSqFun (rowSparseA βA u *ᵥ y - rowSparseb βb w) =
      frobSqFun (rowSparseA βA u *ᵥ xStar βA βb u w - rowSparseb βb w) +
      frobSqFun (rowSparseA βA u *ᵥ (y - xStar βA βb u w)) :=
  frobSqFun_leastSquares _ _ (rowSparse_normal_eq hk hn βA βb u hunit w hβA) y

/-! ## §6. The sampling gap between the two Set-Disjointness cases -/

/-- Without an intersection the solution is proportional to the public direction. -/
theorem rowSparse_xStar_noIntersection {k n : ℕ} (βA βb : ℝ)
    (u : Fin k → Fin n → ℝ) (w : Fin n → ℝ)
    (hno : ∀ j : Fin k, j.val ≠ 0 → innerVec (u j) w = 0) :
    xStar βA βb u w = fun i : Fin k => if i.val = 0 then βb / βA else 0 := by
  funext i
  unfold xStar
  by_cases hi : i.val = 0
  · simp [hi]
  · simp [hi, hno i hi]

/-- With an intersection at block `j` the `j`-th coordinate of `x*` is the overlap. -/
theorem rowSparse_xStar_intersection {k n : ℕ} (βA βb : ℝ)
    (u : Fin k → Fin n → ℝ) (w : Fin n → ℝ) (j : Fin k) (hj : j.val ≠ 0) :
    xStar βA βb u w j = (n : ℝ) * innerVec (u j) w := by
  unfold xStar
  simp [hj]

/-- **Proposition 12, sampling gap (p. 8).**  If the overlap at block `j` is nonzero, then
the sampling law of `x*` puts mass `(n·⟨t_1|t_j⟩)²/‖x*‖²` on `j`; for the Set-Disjointness
instances with `α_1 α_j = Θ(n)` this is a constant. -/
theorem rowSparse_intersection_mass {k n : ℕ} (βA βb : ℝ)
    (u : Fin k → Fin n → ℝ) (w : Fin n → ℝ) (j : Fin k) (hj : j.val ≠ 0) :
    vecDist (xStar βA βb u w) j =
      ((n : ℝ) * innerVec (u j) w) ^ 2 / frobSqVec (xStar βA βb u w) := by
  unfold vecDist
  rw [rowSparse_xStar_intersection βA βb u w j hj]

/-! ## §7. The parameters `‖A‖_F²`, `σ_min`, `κ²`, `κ_F²`, `γ²` -/

/-- Squared Frobenius norm of the row-sparse matrix. -/
theorem rowSparseA_frobSq {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (βA : ℝ)
    (u : Fin k → Fin n → ℝ) (hunit : ∀ j : Fin k, frobSqVec (u j) = 1) :
    frobSqPair (rowSparseA βA u) = βA ^ 2 + ((k : ℝ) - 1) := by
  unfold frobSqPair
  have hblock : ∀ j : Fin k,
      (∑ l : Fin n, ∑ i : Fin k, rowSparseA βA u (j, l) i ^ 2)
        = if j.val = 0 then βA ^ 2 else 1 := by
    intro j
    by_cases hj : j.val = 0
    · have hinner : ∀ l : Fin n, (∑ i : Fin k, rowSparseA βA u (j, l) i ^ 2)
          = if l.val = 0 then βA ^ 2 else 0 := by
        intro l
        rw [Finset.sum_eq_single (⟨0, hk⟩)]
        · by_cases hl : l.val = 0 <;> simp [rowSparseA, hj, hl]
        · intro i _ hi
          have hi0 : i.val ≠ 0 := fun h => hi (Fin.ext (by simpa using h))
          simp [rowSparseA, hj, hi0]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hsum : (∑ l : Fin n, ∑ i : Fin k, rowSparseA βA u (j, l) i ^ 2) = βA ^ 2 := by
        rw [Finset.sum_congr rfl fun l _ => hinner l]
        rw [Finset.sum_eq_single (⟨0, hn⟩)]
        · have h0 : ((⟨0, hn⟩ : Fin n)).val = 0 := rfl
          rw [h0]; simp
        · intro l _ hl
          have hl0 : l.val ≠ 0 := fun h => hl (Fin.ext (by simpa using h))
          simp [hl0]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hsum]
      simp [hj]
    · have hinner : ∀ l : Fin n, (∑ i : Fin k, rowSparseA βA u (j, l) i ^ 2) = u j l ^ 2 := by
        intro l
        rw [Finset.sum_eq_single j]
        · simp [rowSparseA, hj]
        · intro i _ hi; simp [rowSparseA, hj, hi]
        · intro h; exact absurd (Finset.mem_univ j) h
      have hsum : (∑ l : Fin n, ∑ i : Fin k, rowSparseA βA u (j, l) i ^ 2) = frobSqVec (u j) := by
        rw [Finset.sum_congr rfl fun l _ => hinner l]
        rfl
      rw [hsum, hunit j]
      simp [hj]
  simp only [hblock, sum_fin_ite_zero hk]
  ring

/-- Squared norm of the row-sparse source vector. -/
theorem rowSparseb_frobSq {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (βb : ℝ)
    (w : Fin n → ℝ) (hw : frobSqVec w = 1) :
    frobSqPairVec (rowSparseb (k := k) βb w) = βb ^ 2 + ((k : ℝ) - 1) * (n : ℝ) ^ 2 := by
  unfold frobSqPairVec
  have hblock : ∀ j : Fin k,
      (∑ l : Fin n, rowSparseb (k := k) βb w (j, l) ^ 2)
        = if j.val = 0 then βb ^ 2 else (n : ℝ) ^ 2 := by
    intro j
    by_cases hj : j.val = 0
    · have hinner : ∀ l : Fin n, rowSparseb (k := k) βb w (j, l) ^ 2
          = if l.val = 0 then βb ^ 2 else 0 := by
        intro l; simp [rowSparseb, hj, sq]
      have hsum : (∑ l : Fin n, rowSparseb (k := k) βb w (j, l) ^ 2) = βb ^ 2 := by
        rw [Finset.sum_congr rfl fun l _ => hinner l]
        rw [Finset.sum_eq_single (⟨0, hn⟩)]
        · have h0 : ((⟨0, hn⟩ : Fin n)).val = 0 := rfl
          rw [h0]; simp
        · intro l _ hl
          have hl0 : l.val ≠ 0 := fun h => hl (Fin.ext (by simpa using h))
          simp [hl0]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hsum]
      simp [hj]
    · have hinner : ∀ l : Fin n, rowSparseb (k := k) βb w (j, l) ^ 2
          = (n : ℝ) ^ 2 * (w l) ^ 2 := by
        intro l; simp [rowSparseb, hj]; ring
      simp only [hinner]
      rw [← Finset.mul_sum]
      have hsum : (∑ l : Fin n, (w l) ^ 2) = frobSqVec w := rfl
      rw [hsum, hw, mul_one]
      simp [hj]
  simp only [hblock, sum_fin_ite_zero hk]

/-- Squared norm of the planted image. -/
theorem rowSparse_AxStar_frobSq {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (βA βb : ℝ)
    (u : Fin k → Fin n → ℝ) (hunit : ∀ j : Fin k, frobSqVec (u j) = 1) (w : Fin n → ℝ)
    (hβA : βA ≠ 0) :
    frobSqPairVec (rowSparseA βA u *ᵥ xStar βA βb u w) =
      βb ^ 2 + (n : ℝ) ^ 2 *
        (∑ j : Fin k, if j.val = 0 then 0 else (innerVec (u j) w) ^ 2) := by
  unfold frobSqPairVec
  have hx := rowSparseA_mulVec_xStar (k := k) (n := n) hk (βA := βA) (βb := βb) (u := u) (w := w) hβA
  have hblock : ∀ j : Fin k,
      (∑ l : Fin n, (rowSparseA βA u *ᵥ xStar βA βb u w) (j, l) ^ 2)
        = if j.val = 0 then βb ^ 2 else (n : ℝ) ^ 2 * (innerVec (u j) w) ^ 2 := by
    intro j
    by_cases hj : j.val = 0
    · have hinner : ∀ l : Fin n, (rowSparseA βA u *ᵥ xStar βA βb u w) (j, l) ^ 2
          = if l.val = 0 then βb ^ 2 else 0 := by
        intro l; rw [hx]; simp [hj, sq]
      have hsum : (∑ l : Fin n, (rowSparseA βA u *ᵥ xStar βA βb u w) (j, l) ^ 2) = βb ^ 2 := by
        rw [Finset.sum_congr rfl fun l _ => hinner l]
        rw [Finset.sum_eq_single (⟨0, hn⟩)]
        · have h0 : ((⟨0, hn⟩ : Fin n)).val = 0 := rfl
          rw [h0]; simp
        · intro l _ hl
          have hl0 : l.val ≠ 0 := fun h => hl (Fin.ext (by simpa using h))
          simp [hl0]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [hsum]
      simp [hj]
    · have hinner : ∀ l : Fin n, (rowSparseA βA u *ᵥ xStar βA βb u w) (j, l) ^ 2
          = (n : ℝ) ^ 2 * ((innerVec (u j) w) ^ 2 * (u j l) ^ 2) := by
        intro l; rw [hx]; simp [hj]; ring
      simp only [hinner]
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      rw [show (∑ i : Fin n, u j i ^ 2) = frobSqVec (u j) from rfl, hunit j, mul_one,
        if_neg hj]
  simp only [hblock]
  have hdecomp : ∀ j : Fin k,
      (if j.val = 0 then βb ^ 2 else (n : ℝ) ^ 2 * (innerVec (u j) w) ^ 2)
        = (if j.val = 0 then βb ^ 2 else 0) +
          (n : ℝ) ^ 2 * (if j.val = 0 then 0 else (innerVec (u j) w) ^ 2) := by
    intro j
    by_cases h : j.val = 0 <;> simp [h]
  simp only [hdecomp, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_fin_ite_zero_single hk (βb ^ 2)]

/-- `σ_min² = min{β_A², 1}`: the eigenvalues of `AᵀA` are `β_A²` and `1`. -/
def sigmaMinSq (βA : ℝ) : ℝ := min (βA ^ 2) 1

/-- `κ² = max(β_A²,1)/min(β_A²,1)`. -/
def condSq (βA : ℝ) : ℝ := max (βA ^ 2) 1 / sigmaMinSq βA

/-- `κ_F² = ‖A‖_F²/σ_min² = (β_A² + k - 1)/min(β_A²,1)`. -/
def condFSq (k : ℕ) (βA : ℝ) : ℝ := (βA ^ 2 + ((k : ℝ) - 1)) / sigmaMinSq βA

/-- Squared condition number of the row-sparse instance. -/
theorem rowSparse_condSq_eq {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (βA : ℝ)
    (u : Fin k → Fin n → ℝ) (hunit : ∀ j : Fin k, frobSqVec (u j) = 1) :
    condSq βA = max (βA ^ 2) 1 / sigmaMinSq βA ∧
    condFSq k βA = frobSqPair (rowSparseA βA u) / sigmaMinSq βA := by
  refine ⟨rfl, ?_⟩
  unfold condFSq
  rw [rowSparseA_frobSq hk hn βA u hunit]

/-- **Proposition 12, unit parameter choice (p. 8).**  With `β_A = β_b = 1` one has
`κ² = 1` and `κ_F² = k`. -/
theorem rowSparse_cond_unit {k : ℕ} (_hk : 0 < k) :
    condSq 1 = 1 ∧ condFSq k 1 = (k : ℝ) := by
  constructor
  · unfold condSq sigmaMinSq
    norm_num
  · unfold condFSq sigmaMinSq
    norm_num

/-- `κ_F ≥ κ` when `β_A ≥ 1`, as used at the end of the proof of Proposition 12 (p. 8). -/
theorem condFSq_ge_condSq {k : ℕ} (hk : 0 < k) {βA : ℝ} (hβA : 1 ≤ βA) :
    condSq βA ≤ condFSq k βA := by
  have h1 : βA ^ 2 ≥ 1 := by nlinarith
  unfold condSq condFSq sigmaMinSq
  rw [min_eq_right h1, max_eq_left h1]
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have : ((k : ℝ) - 1) ≥ 0 := by linarith
  have hnum : βA ^ 2 ≤ βA ^ 2 + ((k : ℝ) - 1) := by linarith
  exact div_le_div_of_nonneg_right hnum (by linarith)

/-- **Proposition 12, `γ²` (p. 9).**  The overlap of `b` with the column space of `A` is
`γ² = ‖Ax*‖²/‖b‖²`. -/
theorem rowSparse_gamma_sq {k n : ℕ} (hk : 0 < k) (hn : 0 < n) (βA βb : ℝ)
    (u : Fin k → Fin n → ℝ) (hunit : ∀ j : Fin k, frobSqVec (u j) = 1) (w : Fin n → ℝ)
    (hw : frobSqVec w = 1) (hβA : βA ≠ 0) :
    frobSqPairVec (rowSparseA βA u *ᵥ xStar βA βb u w) /
        frobSqPairVec (rowSparseb (k := k) βb w) =
      (βb ^ 2 + (n : ℝ) ^ 2 * (∑ j : Fin k, if j.val = 0 then 0 else (innerVec (u j) w) ^ 2)) /
        (βb ^ 2 + ((k : ℝ) - 1) * (n : ℝ) ^ 2) := by
  rw [rowSparse_AxStar_frobSq hk hn βA βb u hunit w hβA,
    rowSparseb_frobSq hk hn βb w hw]

/-- **Proposition 12, `γ²` in the disjoint case (p. 9).**  When `b` uses the first player's
vector `w = |t_1⟩` and no other player shares a coordinate with player 1, the overlap sum
vanishes, so `γ² = β_b²/(β_b² + (k-1)n²)`. -/
theorem rowSparse_gamma_sq_noIntersection {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (βA βb : ℝ) (u : Fin k → Fin n → ℝ) (hunit : ∀ j : Fin k, frobSqVec (u j) = 1)
    (hno : ∀ j : Fin k, j.val ≠ 0 → innerVec (u j) (u ⟨0, hk⟩) = 0) (hβA : βA ≠ 0) :
    frobSqPairVec (rowSparseA βA u *ᵥ xStar βA βb u (u ⟨0, hk⟩)) /
        frobSqPairVec (rowSparseb (k := k) βb (u ⟨0, hk⟩)) =
      βb ^ 2 / (βb ^ 2 + ((k : ℝ) - 1) * (n : ℝ) ^ 2) := by
  rw [rowSparse_gamma_sq hk hn βA βb u hunit (u ⟨0, hk⟩) (hunit ⟨0, hk⟩) hβA]
  have hS : (∑ j : Fin k, if j.val = 0 then 0 else (innerVec (u j) (u ⟨0, hk⟩)) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj0 : j.val = 0
    · simp [hj0]
    · simp [hj0, hno j hj0]
  rw [hS, mul_zero, add_zero]

/-- **Proposition 12, `γ = Ω(1/(√k n))` at unit parameters (p. 9).**  With `β_b = 1` the
disjoint-case value `1/(1 + (k-1)n²)` is at least `1/(k n²)`, matching the paper's
`γ² = Θ(1/(kn²))`. -/
theorem rowSparse_gamma_sq_unit_ge {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    (1 : ℝ) / ((k : ℝ) * (n : ℝ) ^ 2) ≤ 1 / (1 + ((k : ℝ) - 1) * (n : ℝ) ^ 2) := by
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hden : (1 : ℝ) + ((k : ℝ) - 1) * (n : ℝ) ^ 2 ≤ (k : ℝ) * (n : ℝ) ^ 2 := by
    nlinarith
  have hpos : (0 : ℝ) < 1 + ((k : ℝ) - 1) * (n : ℝ) ^ 2 := by nlinarith
  exact one_div_le_one_div_of_le hpos hden

/-! ## §8. Composing with Theorem 10 and Set-Disjointness hardness -/

/-- **Proposition 12, lower bound (p. 9), in the shape of the paper's argument.**  If `T`
`SQ` calls suffice for the row-sparse instance, then Theorem 10 turns any protocol for
`k`-player Set-Disjointness built from it into one with at most `6(T+k)log(q·kn)` bits, and
Proposition 5 (the named hypothesis `SetDisjointnessHardness`) forces
`kn ≤ 6·C·(T+k)·log(q·kn)`.

The step "an ε-approximate sampler gives a Set-Disjointness protocol" is the source's
constant-overhead reduction of p. 8; here it is represented by the existence of the
protocol `p` over the same Set-Disjointness inputs, which is what the paper's reduction
constructs. -/
theorem rowSparse_query_lower_bound
    (CSD : ℝ) (hSD : SetDisjointnessHardness CSD) (hCSD : 0 ≤ CSD)
    (k n T q : ℕ) (hk : 3200 * k ≤ n)
    (p : RandProtocol k (SetDJInput k n))
    (hs : p.Succeeds setDJAnswer (1 - (1 : ℚ) / (k : ℚ) ^ 3))
    (hcost : (p.worstCost : ℝ) ≤ 6 * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ)) :
    (k : ℝ) * n ≤ 6 * CSD * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ) := by
  have h := hSD k n hk p hs
  calc (k : ℝ) * n ≤ CSD * (p.worstCost : ℝ) := h
    _ ≤ CSD * (6 * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ)) :=
        mul_le_mul_of_nonneg_left hcost hCSD
    _ = 6 * CSD * ((T : ℝ) + (k : ℝ)) * (logBits (q * (k * n)) : ℝ) := by ring

end Qatlib.Papers.QInspired25.MainResults.Reductions
