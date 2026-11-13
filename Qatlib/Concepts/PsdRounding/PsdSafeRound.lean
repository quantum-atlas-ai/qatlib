/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DyadicFloor.FloorRounding.RationalFloor
import Mathlib.Algebra.Order.Chebyshev

/-!
# Positive definite dyadic matrix rounding

Shows that symmetric dyadic rounding preserves positive definiteness when the spectral margin
exceeds the dimension times the entrywise rounding error. The proof bounds quadratic forms of
the rounding error and applies these estimates in `g1`; matrix positivity provides the
background in [Bhatia2007].

## Main statements

* `abs_entry_le`: bounds each rounded entry error by `2⁻ᵖ`.
* `abs_quad_le`: controls a quadratic form using an entrywise bound.
* `g1`: proves symmetry, positive definiteness, and entrywise accuracy after rounding.

## References

* [Bhatia, 2007][Bhatia2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.PsdRounding.PsdSafeRound
open Qatlib.Concepts.DyadicFloor.FloorRounding Matrix
open scoped BigOperators

/-- The matrix returned by `roundMatrix` is symmetric for every input matrix. -/
lemma roundMatrix_isSymm {n : ℕ} (p : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) :
    (roundMatrix p A).IsSymm := by
  refine IsSymm.ext fun i j => ?_
  simp only [roundMatrix]
  ring

/-- For a symmetric rational matrix, each entry of `roundMatrix` is the corresponding dyadic
floor. -/
lemma roundMatrix_eq_floor {n : ℕ} (p : ℕ) {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : A.IsSymm) (i j : Fin n) :
    roundMatrix p A i j = floorDyadic p (A i j) := by
  have hij : A j i = A i j := (IsSymm.ext_iff.mp hA) i j
  simp only [roundMatrix, hij]
  ring

/-- Every entry of a symmetric rational matrix changes by at most `1 / 2 ^ p` under
`roundMatrix`, after coercion to the reals. -/
lemma abs_entry_le {n : ℕ} (p : ℕ) {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : A.IsSymm) (i j : Fin n) :
    |(roundMatrix p A i j : ℝ) - (A i j : ℝ)| ≤ 1 / (2 : ℝ) ^ p := by
  rw [roundMatrix_eq_floor p hA, abs_sub_comm]
  have h0 : 0 ≤ (A i j : ℝ) - (floorDyadic p (A i j) : ℝ) := by
    exact_mod_cast error_nonneg p (A i j)
  have hlt : (A i j : ℝ) - (floorDyadic p (A i j) : ℝ) < 1 / (2 : ℝ) ^ p := by
    have hrat := error_lt p (A i j)
    have hcast : ((A i j - floorDyadic p (A i j) : ℚ) : ℝ) <
        ((1 / (2 : ℚ) ^ p : ℚ) : ℝ) := by
      exact_mod_cast hrat
    rw [Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_pow] at hcast
    simpa [show ((2 : ℚ) : ℝ) = 2 by norm_cast] using hcast
  rw [abs_of_nonneg h0]
  exact le_of_lt hlt

/-- The real interpretation of a symmetric rational matrix is Hermitian. -/
lemma interpret_isHermitian {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ} (hA : A.IsSymm) :
    (interpret A).IsHermitian := by
  ext i j
  simp [interpret, conjTranspose_apply, star_trivial]
  exact_mod_cast (IsSymm.ext_iff.mp hA) i j

/-- The real quadratic form associated with a matrix, evaluated on a finitely supported vector. -/
def quad {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n →₀ ℝ) : ℝ :=
  x.sum fun i xi => x.sum fun j xj => star xi * M i j * xj

/-- Expands `quad M x` as the double sum of `x i * M i j * x j` over all indices. -/
lemma quad_finset {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n →₀ ℝ) :
    quad M x = ∑ i : Fin n, ∑ j : Fin n, x i * M i j * x j := by
  classical
  unfold quad
  rw [Finsupp.sum_fintype x (fun i xi => x.sum fun j xj => star xi * M i j * xj)
    (fun i => by simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.sum_fintype x (fun j xj => star (x i) * M i j * xj) (fun _ => by simp)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [star_trivial]

/-- The quadratic form of a matrix difference is the difference of the quadratic forms. -/
lemma quad_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (x : Fin n →₀ ℝ) :
    quad (A - B) x = quad A x - quad B x := by
  rw [quad_finset, quad_finset, quad_finset, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Matrix.sub_apply]
  ring

/-- The quadratic form of `μ` times the identity is `μ` times the sum of squared coordinates. -/
lemma quad_smul_one {n : ℕ} (μ : ℝ) (x : Fin n →₀ ℝ) :
    quad (μ • (1 : Matrix (Fin n) (Fin n) ℝ)) x = μ * ∑ i : Fin n, x i ^ 2 := by
  classical
  rw [quad_finset]
  have hrow : ∀ i, ∑ j, x i * (μ • (1 : Matrix (Fin n) (Fin n) ℝ)) i j * x j
      = x i * μ * x i := by
    intro i
    have hinner : ∑ j, x i * (μ • (1 : Matrix (Fin n) (Fin n) ℝ)) i j * x j
        = ∑ j, if i = j then x i * μ * x j else 0 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hij : i = j
      · simp [hij, Matrix.smul_apply, Matrix.one_apply, mul_assoc]
      · simp [hij, Matrix.smul_apply, Matrix.one_apply]
    rw [hinner, Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
  simp_rw [hrow, pow_two, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- An entrywise absolute bound `δ` bounds the absolute quadratic form by `δ` times the square
of the sum of absolute coordinates. -/
lemma abs_quad_le {n : ℕ} {E : Matrix (Fin n) (Fin n) ℝ} {δ : ℝ}
    (hδ : ∀ i j, |E i j| ≤ δ) (x : Fin n →₀ ℝ) :
    |quad E x| ≤ δ * (∑ i : Fin n, |x i|) ^ 2 := by
  rw [quad_finset]
  have hsum : |∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j|
      ≤ ∑ i : Fin n, ∑ j : Fin n, |x i| * |E i j| * |x j| := by
    calc
      |∑ i, ∑ j, x i * E i j * x j| ≤ ∑ i, |∑ j, x i * E i j * x j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |x i * E i j * x j| :=
        Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i, ∑ j, |x i| * |E i j| * |x j| := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [abs_mul, abs_mul, mul_assoc]
  refine hsum.trans ?_
  have hentry : ∑ i : Fin n, ∑ j : Fin n, |x i| * |E i j| * |x j|
      ≤ ∑ i : Fin n, ∑ j : Fin n, |x i| * δ * |x j| := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have := hδ i j
    gcongr
  refine hentry.trans ?_
  have hfactor : ∑ i : Fin n, ∑ j : Fin n, |x i| * δ * |x j|
      = δ * (∑ i : Fin n, |x i|) ^ 2 := by
    have hinner : ∀ i, ∑ j, |x i| * δ * |x j| = |x i| * δ * ∑ j, |x j| := by
      intro i
      rw [← Finset.mul_sum]
    simp_rw [hinner, ← Finset.sum_mul]
    ring
  rw [hfactor]

/-- The square of the sum of absolute coordinates is at most the dimension times the sum of
squared coordinates. -/
lemma sum_abs_sq_le {n : ℕ} (x : Fin n →₀ ℝ) :
    (∑ i : Fin n, |x i|) ^ 2 ≤ (n : ℝ) * ∑ i : Fin n, x i ^ 2 := by
  have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
  calc
    (∑ i : Fin n, |x i|) ^ 2 ≤ (Finset.univ : Finset (Fin n)).card * ∑ i : Fin n, |x i| ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ = (n : ℝ) * ∑ i : Fin n, x i ^ 2 := by
      simp [hcard, sq_abs]

/-- The sum of squared coordinates of a nonzero real vector is strictly positive. -/
lemma sum_sq_pos {n : ℕ} {x : Fin n →₀ ℝ} (hx : x ≠ 0) :
    0 < ∑ i : Fin n, x i ^ 2 := by
  by_contra hle
  have hsum : ∑ i : Fin n, x i ^ 2 = 0 :=
    le_antisymm (le_of_not_gt hle) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hzero : ∀ i, x i = 0 := by
    intro i
    have hsq : (x i) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hsum i (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp hsq
  exact hx (Finsupp.ext hzero)

/-- If a symmetric rational matrix has positive spectral margin `μ` and `n / 2 ^ p < μ`, dyadic
rounding yields a symmetric matrix with positive definite real interpretation and entrywise
error at most `1 / 2 ^ p`. -/
theorem g1 :
    ∀ (n p : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (μ : ℝ),
      A.IsSymm → 0 < μ →
      (interpret A - μ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef →
      (n : ℝ) / (2 : ℝ) ^ p < μ →
      (roundMatrix p A).IsSymm ∧ (interpret (roundMatrix p A)).PosDef ∧
      (∀ i j, |(roundMatrix p A i j : ℝ) - (A i j : ℝ)| ≤ 1 / (2 : ℝ) ^ p) := by
  intro n p A μ hA hμ hpsd hscale
  refine ⟨roundMatrix_isSymm p A, ?_, abs_entry_le p hA⟩
  refine ⟨interpret_isHermitian (roundMatrix_isSymm p A), ?_⟩
  intro x hx
  let C : Matrix (Fin n) (Fin n) ℝ := interpret A
  let B : Matrix (Fin n) (Fin n) ℝ := interpret (roundMatrix p A)
  let E : Matrix (Fin n) (Fin n) ℝ := C - B
  have hE : ∀ i j, |E i j| ≤ 1 / (2 : ℝ) ^ p := by
    intro i j
    simpa [E, C, B, interpret, abs_sub_comm] using abs_entry_le p hA i j
  have hquad : quad B x = quad C x - quad E x := by
    have hsub : quad E x = quad C x - quad B x := by
      simpa [E] using quad_sub C B x
    linarith
  have hdiag : quad (μ • (1 : Matrix (Fin n) (Fin n) ℝ)) x = μ * ∑ i, x i ^ 2 :=
    quad_smul_one μ x
  have hsplit : quad C x = quad (C - μ • 1) x + quad (μ • 1) x := by
    have hsub := quad_sub C (μ • (1 : Matrix (Fin n) (Fin n) ℝ)) x
    linarith
  have hbase : μ * ∑ i, x i ^ 2 ≤ quad C x := by
    have hnn : 0 ≤ quad (C - μ • 1) x := by
      simpa [C, quad] using hpsd.2 x
    rw [hsplit, hdiag]
    linarith
  have herr : |quad E x| ≤ (n : ℝ) / (2 : ℝ) ^ p * ∑ i, x i ^ 2 := by
    calc
      |quad E x| ≤ (1 / (2 : ℝ) ^ p) * (∑ i, |x i|) ^ 2 := abs_quad_le hE x
      _ ≤ (1 / (2 : ℝ) ^ p) * ((n : ℝ) * ∑ i, x i ^ 2) := by
        gcongr
        exact sum_abs_sq_le x
      _ = (n : ℝ) / (2 : ℝ) ^ p * ∑ i, x i ^ 2 := by ring
  have hpos : 0 < (μ - (n : ℝ) / (2 : ℝ) ^ p) * ∑ i, x i ^ 2 :=
    mul_pos (sub_pos.mpr hscale) (sum_sq_pos hx)
  have hlower : (μ - (n : ℝ) / (2 : ℝ) ^ p) * ∑ i, x i ^ 2 ≤ quad B x := by
    have habs : quad E x ≤ |quad E x| := le_abs_self _
    calc
      (μ - (n : ℝ) / (2 : ℝ) ^ p) * ∑ i, x i ^ 2
          = μ * ∑ i, x i ^ 2 - (n : ℝ) / (2 : ℝ) ^ p * ∑ i, x i ^ 2 := by ring
      _ ≤ quad C x - |quad E x| := by linarith
      _ ≤ quad C x - quad E x := by linarith
      _ = quad B x := by linarith
  exact lt_of_lt_of_le hpos hlower

end Qatlib.Concepts.PsdRounding.PsdSafeRound
