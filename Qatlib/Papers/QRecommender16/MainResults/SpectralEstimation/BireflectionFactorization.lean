/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Rank

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 5.3 — isometric factorization and the bireflection walk

Source: Iordanis Kerenidis, Anupam Prakash, *Quantum Recommendation Systems*,
fixed version arXiv:1603.08675v3 (22 Sep 2016), Lemma 5.3, printed p. 14
(Section 5.2 "Quantum Singular Value Estimation").

For `A ∈ ℝ^{m×n}` the paper constructs isometries `P ∈ ℝ^{mn×m}` and
`Q ∈ ℝ^{mn×n}`:

* `P (i,j) k = [k = i] · A i j / ‖A_i‖`;
* `Q (i,j) l = [l = j] · ‖A_i‖ / ‖A‖_F`.

Then Lemma 5.3 asserts
(i)   `A / ‖A‖_F = Pᵀ Q`, `Pᵀ P = 1`, `Qᵀ Q = 1`;
(ii)  `W = U V` with `U = 2 P Pᵀ − 1`, `V = 2 Q Qᵀ − 1` is unitary and can be
      implemented in time `O(polylog(mn))`;
(iii) `Q v_i` is an eigenvector of `W` with eigenvalue `e^{iθ_i}` where
      `cos(θ_i/2) = σ_i / ‖A‖_F`.

This file proves parts (i) and (ii) in full, and the operative cosine identity
of part (iii): the inner product of the two isometric images `P u` and `Q v` of
a singular pair `(u, v, σ)` equals `σ / ‖A‖_F`. That identity is exactly the
paper's `cos(θ_i/2) = σ_i/‖A‖_F` once `θ_i/2` is taken to be the angle between
`P u_i` and `Q v_i` (as in the proof, p. 14–15). The `O(polylog(mn))`
implementation time of part (ii) is algorithmic and not modelled here.

Boundary: `P`/`Q` divide by `‖A_i‖` and `‖A‖_F`, so the construction assumes
nonzero rows and `A ≠ 0` (the paper's implicit nondegeneracy).
-/

open scoped Matrix.Norms.Frobenius
open Matrix

namespace Qatlib.Papers.QRecommender16.MainResults.SpectralEstimation

set_option autoImplicit false

noncomputable section

variable {m n : ℕ}

/-- The squared Euclidean norm of row `i`, i.e. `‖A_i‖²`. -/
def rowNormSq (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) : ℝ := ∑ j, A i j ^ 2

/-- The squared Euclidean norm of a row is nonnegative. -/
lemma rowNormSq_nonneg (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    0 ≤ rowNormSq A i := by
  unfold rowNormSq
  exact Finset.sum_nonneg fun j _ => sq_nonneg _

/-- The squared Frobenius norm as the entrywise sum of squares. -/
def frobSq (A : Matrix (Fin m) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, A i j ^ 2

/-- The square of the Frobenius norm equals the entrywise sum of squares. -/
lemma frobSq_eq_norm_sq (A : Matrix (Fin m) (Fin n) ℝ) : frobSq A = ‖A‖ ^ 2 := by
  have hS : (0 : ℝ) ≤ ∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Real.rpow_nonneg (norm_nonneg _) 2
  rw [frobSq, Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt hS]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]

/-- Summing the squared row norms gives the squared Frobenius norm. -/
lemma sum_rowNormSq (A : Matrix (Fin m) (Fin n) ℝ) : ∑ i, rowNormSq A i = ‖A‖ ^ 2 := by
  rw [← frobSq_eq_norm_sq]
  rfl

/-- The isometry `P` of Lemma 5.3: `P (i,j) k = [k = i] · A i j / ‖A_i‖`. -/
def isometryP (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m × Fin n) (Fin m) ℝ :=
  fun p k => if k = p.1 then A p.1 p.2 / Real.sqrt (rowNormSq A p.1) else 0

/-- The isometry `Q` of Lemma 5.3: `Q (i,j) l = [l = j] · ‖A_i‖ / ‖A‖_F`. -/
def isometryQ (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m × Fin n) (Fin n) ℝ :=
  fun p l => if l = p.2 then Real.sqrt (rowNormSq A p.1) / ‖A‖ else 0

/-- The bireflection walk `W = U V` with `U = 2 P Pᵀ − 1` and `V = 2 Q Qᵀ − 1`. -/
def bireflectionWalk (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℝ :=
  (2 • (isometryP A * (isometryP A)ᵀ) - 1) * (2 • (isometryQ A * (isometryQ A)ᵀ) - 1)

/-- Part (i) of Lemma 5.3: `Pᵀ P = 1`. Each column of `P` places a normalised
row of `A` in its `i`-block, so columns within one block and across blocks are
orthogonal. -/
theorem isometryP_orthonormal (A : Matrix (Fin m) (Fin n) ℝ)
    (hrow : ∀ i, 0 < rowNormSq A i) :
    (isometryP A)ᵀ * isometryP A = 1 := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  have hinner : ∀ i, (∑ j, isometryP A (i, j) k * isometryP A (i, j) l)
      = if k = i then (if l = i then (1 : ℝ) else 0) else 0 := by
    intro i
    by_cases hk : k = i
    · rw [if_pos hk]
      by_cases hl : l = i
      · rw [if_pos hl]
        have hterm : ∀ j, (A i j / Real.sqrt (rowNormSq A i)) *
            (A i j / Real.sqrt (rowNormSq A i)) = A i j ^ 2 / rowNormSq A i := by
          intro j
          rw [div_mul_div_comm, Real.mul_self_sqrt (le_of_lt (hrow i))]
          ring
        have hsum : (∑ j, isometryP A (i, j) k * isometryP A (i, j) l)
            = ∑ j, A i j ^ 2 / rowNormSq A i :=
          Finset.sum_congr rfl (fun j _ => by
            simp only [isometryP]
            rw [if_pos hk, if_pos hl]
            exact hterm j)
        rw [hsum, ← Finset.sum_div]
        exact div_self (hrow i).ne'
      · rw [if_neg hl]
        refine Finset.sum_eq_zero fun j _ => ?_
        simp only [isometryP]
        rw [if_pos hk, if_neg hl]
        simp
    · rw [if_neg hk]
      refine Finset.sum_eq_zero fun j _ => ?_
      simp only [isometryP]
      rw [if_neg hk]
      simp
  rw [Finset.sum_congr rfl (fun i _ => hinner i)]
  rw [Fintype.sum_ite_eq]
  by_cases h : k = l
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (fun e => h e.symm), if_neg h]

/-- Part (i) of Lemma 5.3: `Qᵀ Q = 1`. The squared norm of column `k` is
`∑_i ‖A_i‖² / ‖A‖_F² = 1`. -/
theorem isometryQ_orthonormal (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : 0 < ‖A‖) :
    (isometryQ A)ᵀ * isometryQ A = 1 := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  rw [Fintype.sum_prod_type]
  have hinner : ∀ i, (∑ j, isometryQ A (i, j) k * isometryQ A (i, j) l)
      = if k = l then (Real.sqrt (rowNormSq A i) / ‖A‖) ^ 2 else 0 := by
    intro i
    by_cases hkl : k = l
    · rw [if_pos hkl]
      rw [Finset.sum_eq_single k]
      · have e1 : isometryQ A (i, k) k = Real.sqrt (rowNormSq A i) / ‖A‖ := by
          simp [isometryQ]
        have e2 : isometryQ A (i, k) l = Real.sqrt (rowNormSq A i) / ‖A‖ := by
          simp [isometryQ, hkl]
        rw [e1, e2]
        ring
      · intro j _ hj
        have hne : ¬ (k = j) := by intro h; exact hj (by rw [h])
        rw [isometryQ]
        simp only [if_neg hne, zero_mul]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    · rw [if_neg hkl]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hkj : k = j
      · have hlj : ¬ (l = j) := by intro h; exact hkl (hkj.trans h.symm)
        simp only [isometryQ]
        rw [if_pos hkj, if_neg hlj]
        simp
      · simp only [isometryQ]
        rw [if_neg hkj]
        simp
  rw [Finset.sum_congr rfl (fun i _ => hinner i)]
  by_cases hkl : k = l
  · rw [if_pos hkl]
    have hterm : ∀ i, (Real.sqrt (rowNormSq A i) / ‖A‖) ^ 2 = rowNormSq A i / ‖A‖ ^ 2 := by
      intro i
      rw [div_pow, Real.sq_sqrt (rowNormSq_nonneg A i)]
    have hcongr : (∑ i, (if k = l then (Real.sqrt (rowNormSq A i) / ‖A‖) ^ 2 else 0))
        = ∑ i, (Real.sqrt (rowNormSq A i) / ‖A‖) ^ 2 :=
      Finset.sum_congr rfl (fun i _ => by rw [if_pos hkl])
    rw [hcongr]
    have hsum : (∑ i, (Real.sqrt (rowNormSq A i) / ‖A‖) ^ 2)
        = ∑ i, rowNormSq A i / ‖A‖ ^ 2 :=
      Finset.sum_congr rfl (fun i _ => hterm i)
    rw [hsum, ← Finset.sum_div, sum_rowNormSq, div_self (pow_ne_zero 2 hA.ne')]
  · rw [if_neg hkl]
    simp [hkl]

/-- Part (i) of Lemma 5.3: `A / ‖A‖_F = Pᵀ Q`, written `(‖A‖_F)⁻¹ • A`. The only
surviving term of the matrix product pairs `P (k,l) k` with `Q (k,l) l`. -/
theorem P_transpose_mul_Q (A : Matrix (Fin m) (Fin n) ℝ)
    (hrow : ∀ i, 0 < rowNormSq A i) (hA : 0 < ‖A‖) :
    (isometryP A)ᵀ * isometryQ A = (‖A‖)⁻¹ • A := by
  ext k l
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single k]
  · rw [Finset.sum_eq_single l]
    · have e1 : isometryP A (k, l) k = A k l / Real.sqrt (rowNormSq A k) := by
        simp [isometryP]
      have e2 : isometryQ A (k, l) l = Real.sqrt (rowNormSq A k) / ‖A‖ := by
        simp [isometryQ]
      rw [e1, e2]
      have hsne : Real.sqrt (rowNormSq A k) ≠ 0 := (Real.sqrt_pos.mpr (hrow k)).ne'
      field_simp [hsne, hA.ne']
    · intro j _ hj
      have hne : ¬ (l = j) := by intro h; exact hj (by rw [h])
      rw [isometryQ]
      simp only [if_neg hne, mul_zero]
    · intro hl
      exact absurd (Finset.mem_univ l) hl
  · intro i _ hi
    have hne : ¬ (k = i) := by intro h; exact hi (by rw [h])
    simp [isometryP, hne]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- A square matrix `X` with `X * X = X` yields an orthogonal reflection
`2 • X - 1`: its square is the identity. -/
lemma two_smul_sub_one_mul_self {N : Type*} [Fintype N] [DecidableEq N]
    (X : Matrix N N ℝ) (hX : X * X = X) :
    (2 • X - 1) * (2 • X - 1) = 1 := by
  rw [two_smul]
  calc
    (X + X - 1) * (X + X - 1)
        = X * X + X * X + X * X + X * X - X - X - X - X + 1 := by
          noncomm_ring
    _ = 1 := by rw [hX]; noncomm_ring

/-- Part (ii) of Lemma 5.3, algebraic content: `W = U V` with
`U = 2 P Pᵀ − 1`, `V = 2 Q Qᵀ − 1` is orthogonal, `Wᵀ W = 1`. (The
`O(polylog(mn))` implementation time is algorithmic and not modelled.)

The reflections are symmetric, and `Pᵀ P = 1` / `Qᵀ Q = 1` make `P Pᵀ` and
`Q Qᵀ` idempotent, so `U * U = 1` and `V * V = 1`; then
`Wᵀ W = V * (U * U) * V = V * V = 1`. -/
theorem bireflectionWalk_orthogonal (A : Matrix (Fin m) (Fin n) ℝ)
    (hrow : ∀ i, 0 < rowNormSq A i) (hA : 0 < ‖A‖) :
    (bireflectionWalk A)ᵀ * bireflectionWalk A = 1 := by
  let P := isometryP A
  let Q := isometryQ A
  have hP : Pᵀ * P = 1 := isometryP_orthonormal A hrow
  have hQ : Qᵀ * Q = 1 := isometryQ_orthonormal A hA
  have hPP : (P * Pᵀ) * (P * Pᵀ) = P * Pᵀ := by
    rw [Matrix.mul_assoc P Pᵀ (P * Pᵀ)]
    rw [← Matrix.mul_assoc Pᵀ P Pᵀ]
    rw [hP, Matrix.one_mul]
  have hQQ : (Q * Qᵀ) * (Q * Qᵀ) = Q * Qᵀ := by
    rw [Matrix.mul_assoc Q Qᵀ (Q * Qᵀ)]
    rw [← Matrix.mul_assoc Qᵀ Q Qᵀ]
    rw [hQ, Matrix.one_mul]
  have hU : (2 • (P * Pᵀ) - 1) * (2 • (P * Pᵀ) - 1) = 1 :=
    two_smul_sub_one_mul_self (P * Pᵀ) hPP
  have hV : (2 • (Q * Qᵀ) - 1) * (2 • (Q * Qᵀ) - 1) = 1 :=
    two_smul_sub_one_mul_self (Q * Qᵀ) hQQ
  have hPt : (P * Pᵀ)ᵀ = P * Pᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hQt : (Q * Qᵀ)ᵀ = Q * Qᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hUt : (2 • (P * Pᵀ) - 1)ᵀ = 2 • (P * Pᵀ) - 1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, hPt, Matrix.transpose_one]
  have hVt : (2 • (Q * Qᵀ) - 1)ᵀ = 2 • (Q * Qᵀ) - 1 := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, hQt, Matrix.transpose_one]
  show ((2 • (P * Pᵀ) - 1) * (2 • (Q * Qᵀ) - 1))ᵀ *
      ((2 • (P * Pᵀ) - 1) * (2 • (Q * Qᵀ) - 1)) = 1
  rw [Matrix.transpose_mul, hUt, hVt]
  calc
    (2 • (Q * Qᵀ) - 1) * (2 • (P * Pᵀ) - 1) * ((2 • (P * Pᵀ) - 1) * (2 • (Q * Qᵀ) - 1))
        = (2 • (Q * Qᵀ) - 1) * ((2 • (P * Pᵀ) - 1) * (2 • (P * Pᵀ) - 1)) *
            (2 • (Q * Qᵀ) - 1) := by
          noncomm_ring
    _ = (2 • (Q * Qᵀ) - 1) * 1 * (2 • (Q * Qᵀ) - 1) := by rw [hU]
    _ = 1 := by rw [Matrix.mul_one, hV]

/-- Part (iii) of Lemma 5.3, cosine form (fixed arXiv:1603.08675v3, p. 14–15,
equation (13)): for a singular pair `(u, v, σ)` with `A v = σ u` and
`‖u‖² = 1`, the inner product of the isometric images `P u` and `Q v` equals
`σ / ‖A‖_F`. This is the paper's `cos(θ/2) = σ/‖A‖_F`. -/
theorem singular_cosine_relation (A : Matrix (Fin m) (Fin n) ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ) (σ : ℝ)
    (hrow : ∀ i, 0 < rowNormSq A i) (hA : 0 < ‖A‖)
    (hu : ∑ i, u i ^ 2 = 1) (hAv : A *ᵥ v = σ • u) :
    (∑ p : Fin m × Fin n,
        (isometryP A *ᵥ u) p * (isometryQ A *ᵥ v) p) = σ / ‖A‖ := by
  have hPu : ∀ p : Fin m × Fin n,
      (isometryP A *ᵥ u) p = (A p.1 p.2 / Real.sqrt (rowNormSq A p.1)) * u p.1 := by
    intro p
    rw [Matrix.mulVec, dotProduct]
    have hcongr : (∑ k, isometryP A p k * u k)
        = ∑ k, (if k = p.1 then (A p.1 p.2 / Real.sqrt (rowNormSq A p.1)) * u k else 0) :=
      Finset.sum_congr rfl (fun k _ => by simp only [isometryP, ite_mul, zero_mul])
    rw [hcongr, Fintype.sum_ite_eq']
  have hQv : ∀ p : Fin m × Fin n,
      (isometryQ A *ᵥ v) p = (Real.sqrt (rowNormSq A p.1) / ‖A‖) * v p.2 := by
    intro p
    rw [Matrix.mulVec, dotProduct]
    have hcongr : (∑ l, isometryQ A p l * v l)
        = ∑ l, (if l = p.2 then (Real.sqrt (rowNormSq A p.1) / ‖A‖) * v l else 0) :=
      Finset.sum_congr rfl (fun l _ => by simp only [isometryQ, ite_mul, zero_mul])
    rw [hcongr, Fintype.sum_ite_eq']
  have hterm : ∀ p : Fin m × Fin n,
      (isometryP A *ᵥ u) p * (isometryQ A *ᵥ v) p
        = u p.1 * (A p.1 p.2 * v p.2) / ‖A‖ := by
    intro p
    rw [hPu p, hQv p]
    have hsne : Real.sqrt (rowNormSq A p.1) ≠ 0 := (Real.sqrt_pos.mpr (hrow p.1)).ne'
    field_simp [hsne, hA.ne']
  rw [Finset.sum_congr rfl (fun p _ => hterm p)]
  rw [← Finset.sum_div]
  have hinner : (∑ p : Fin m × Fin n, u p.1 * (A p.1 p.2 * v p.2))
      = σ * (∑ i, u i ^ 2) := by
    rw [Fintype.sum_prod_type]
    have hrowfac : ∀ i, (∑ j, u i * (A i j * v j)) = u i * (∑ j, A i j * v j) := by
      intro i; rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun i _ => hrowfac i)]
    have hAv_i : ∀ i, (∑ j, A i j * v j) = σ * u i := by
      intro i
      have h := congrFun hAv i
      simp only [Pi.smul_apply, smul_eq_mul] at h
      simpa [Matrix.mulVec, dotProduct] using h
    rw [Finset.sum_congr rfl (fun i _ => by rw [hAv_i i])]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hinner, hu]
  ring

end

end Qatlib.Papers.QRecommender16.MainResults.SpectralEstimation
