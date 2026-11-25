/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HeatEquation20.MainResults.SpectralAppendix

@[expose] public section


/-!
# HeatEquation20 — the closed form of the tridiagonal determinant (B21), p. 30

Fixed source: arXiv:2004.06516v2.

Lemma 26 (p. 30, eqs. (B20)–(B22)) computes the determinant of the `m × m`
tridiagonal matrix with `λ` on the diagonal and `1` on the two off-diagonals:

`f_m = det A_m`, `f_0 = 1`, `f_1 = λ`, `f_{m+2} = λ f_{m+1} − f_m`, and
consequently `f_m = (x₁^{m+1} − x₂^{m+1})/(x₁ − x₂)` for the roots
`x₁,₂ = (λ ± √(λ² − 4))/2` of `x² − λx + 1 = 0`.

The locked layer fixes `tridiagDet`, `triX1`, `triX2` and the two root
relations `triX1_add_triX2`, `triX1_mul_triX2`, but not the recursion (B21).
This file supplies it:

* `tridiagMat_det_succ_succ`: the recursion, by Laplace expansion along the
  first row (the two surviving minors are `A_{m+1}` and the corner-modified
  matrix whose first column is `e₀`);
* `triClosedForm_succ_succ` and the base cases: the closed form satisfies the
  same recursion with the same two initial values;
* `tridiagDet_closedForm`: the closed form (B21) for `2 < |λ|`.

The corner-modified matrix of Lemma 26, eq. (B22), is not treated separately:
only its determinant is used, and the first-column expansion
`det_of_firstColumn_eq_single` identifies it with `f_m`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace Qatlib.Papers.HeatEquation20.MainResults

open Qatlib.Papers.HeatEquation20.MainResults
open Matrix

open scoped BigOperators

/-! ## The matrix of (B20) -/

/-- The `m × m` tridiagonal matrix of (B20), p. 30: `λ` on the diagonal and
`1` on the two off-diagonals. -/
def tridiagMat (m : ℕ) (lam : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j : Fin m =>
    if i = j then lam else if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0

/-- `tridiagDet` is the determinant of `tridiagMat`. -/
lemma tridiagDet_eq_det (m : ℕ) (lam : ℝ) : tridiagDet m lam = (tridiagMat m lam).det := rfl

/-- The matrix of (B20) is symmetric. -/
lemma tridiagMat_transpose (m : ℕ) (lam : ℝ) : (tridiagMat m lam)ᵀ = tridiagMat m lam := by
  ext i j
  simp only [Matrix.transpose_apply, tridiagMat, Matrix.of_apply]
  by_cases h : i = j
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right (fun hh => h hh.symm)]
    by_cases hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val
    · rw [ite_eq_left hadj, ite_eq_left (by tauto)]
    · rw [ite_eq_right hadj, ite_eq_right (by tauto)]

/-! ## Deleting the first row and column -/

/-- Shifting both indices by one leaves the entry of (B20) unchanged. -/
lemma tridiagMat_succ_apply (m : ℕ) (lam : ℝ) (i j : Fin m) :
    tridiagMat (m + 1) lam (Fin.succ i) (Fin.succ j) = tridiagMat m lam i j := by
  simp only [tridiagMat, Matrix.of_apply, Fin.val_succ]
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl, ite_eq_left rfl]
  · have hne : ¬ (Fin.succ i = Fin.succ j) := fun h => hij (Fin.succ_inj.mp h)
    rw [ite_eq_right hne, ite_eq_right hij]
    by_cases hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val
    · rw [ite_eq_left (by omega), ite_eq_left hadj]
    · rw [ite_eq_right (by omega), ite_eq_right hadj]

/-- Shifting both indices by two leaves the entry of (B20) unchanged. -/
lemma tridiagMat_succ_succ_apply (m : ℕ) (lam : ℝ) (i j : Fin m) :
    tridiagMat (m + 2) lam (Fin.succ (Fin.succ i)) (Fin.succ (Fin.succ j))
      = tridiagMat m lam i j := by
  rw [tridiagMat_succ_apply (m + 1) lam (Fin.succ i) (Fin.succ j),
    tridiagMat_succ_apply m lam i j]

/-- Deleting the first row and column of (B20) leaves the same matrix one size
smaller. -/
lemma tridiagMat_submatrix_succ (m : ℕ) (lam : ℝ) :
    (tridiagMat (m + 1) lam).submatrix Fin.succ Fin.succ = tridiagMat m lam := by
  ext i j
  simp only [Matrix.submatrix_apply]
  exact tridiagMat_succ_apply m lam i j

/-- Deleting the first two rows and columns of (B20) leaves the same matrix two
sizes smaller. -/
lemma tridiagMat_submatrix_doubleSucc (m : ℕ) (lam : ℝ) :
    (tridiagMat (m + 2) lam).submatrix (Fin.succ ∘ Fin.succ) (Fin.succ ∘ Fin.succ)
      = tridiagMat m lam := by
  ext i j
  simp only [Matrix.submatrix_apply, Function.comp_apply]
  exact tridiagMat_succ_succ_apply m lam i j

/-! ## The corner-modified minor of (B22) -/

/-- Embedding `Fin m` into `Fin (m+2)` around the hole `1` shifts the indices
`j ≥ 1` by one. -/
lemma succAbove_one_succ (m : ℕ) (j : Fin m) :
    (Fin.succAbove (1 : Fin (m + 2))) (Fin.succ j) = Fin.succ (Fin.succ j) := by
  refine Fin.succAbove_of_lt_succ (1 : Fin (m + 2)) (Fin.succ j) ?_
  rw [Fin.lt_def, show (((1 : Fin (m + 2)) : ℕ)) = 1 from rfl]
  simp only [Fin.val_succ]
  omega

/-- Deleting the first row and column of the corner-modified minor of (B22)
recovers (B20) two sizes smaller. -/
lemma tridiagMat_submatrix_minor_first (m : ℕ) (lam : ℝ) :
    ((tridiagMat (m + 2) lam).submatrix (Fin.succ : Fin (m + 1) → Fin (m + 2))
        (Fin.succAbove (1 : Fin (m + 2)))).submatrix Fin.succ Fin.succ
      = tridiagMat m lam := by
  ext a b
  simp only [Matrix.submatrix_apply, succAbove_one_succ]
  exact tridiagMat_succ_succ_apply m lam a b

/-- If the first column of a square matrix is `e₀`, the determinant equals
that of the matrix with its first row and column deleted. -/
lemma det_of_firstColumn_eq_single {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (h0 : M 0 0 = 1) (h : ∀ i, i ≠ 0 → M i 0 = 0) :
    M.det = (M.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero M]
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp [h0]
  · intro b _ hb
    rw [h b hb, mul_zero, zero_mul]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- The first column of the corner-modified minor of (B22) is `e₀`. -/
lemma tridiagMat_minor_first_column (m : ℕ) (lam : ℝ) (i : Fin (m + 1)) :
    ((tridiagMat (m + 2) lam).submatrix (Fin.succ : Fin (m + 1) → Fin (m + 2))
        (Fin.succAbove (1 : Fin (m + 2)))) i 0 = if i = 0 then 1 else 0 := by
  have h0 : (Fin.succAbove (1 : Fin (m + 2))) (0 : Fin (m + 1)) = 0 :=
    Fin.succAbove_ne_zero_zero (by simp)
  simp only [Matrix.submatrix_apply, h0, tridiagMat, Matrix.of_apply]
  by_cases hi : i = 0
  · subst hi
    simp
  · rw [ite_eq_right hi]
    have hiv : i.val ≠ 0 := fun h => hi (Fin.ext (by simpa using h))
    have hne : (Fin.succ i : Fin (m + 2)) ≠ 0 := Fin.succ_ne_zero i
    have hne2 : ¬ ((Fin.succ i : Fin (m + 2)).val + 1 = (0 : Fin (m + 2)).val
        ∨ (0 : Fin (m + 2)).val + 1 = (Fin.succ i).val) := by
      simp only [Fin.val_zero, Fin.val_succ]
      omega
    rw [ite_eq_right hne, ite_eq_right hne2]

/-- The determinant of the corner-modified minor of (B22) is `f_m`. -/
lemma tridiagMat_minor_first_det (m : ℕ) (lam : ℝ) :
    ((tridiagMat (m + 2) lam).submatrix (Fin.succ : Fin (m + 1) → Fin (m + 2))
        (Fin.succAbove (1 : Fin (m + 2)))).det = (tridiagMat m lam).det := by
  rw [det_of_firstColumn_eq_single _
    (by simpa using tridiagMat_minor_first_column m lam 0)
    (fun i hi => by rw [tridiagMat_minor_first_column m lam i, ite_eq_right hi])]
  rw [tridiagMat_submatrix_minor_first]

/-! ## The first row of (B20) -/

/-- The first row of (B20) of size `m+2`: `λ` at the origin, `1` at the first
neighbour, `0` elsewhere. -/
lemma tridiagMat_zero_row {m : ℕ} (lam : ℝ) (j : Fin (m + 2)) :
    tridiagMat (m + 2) lam 0 j = if j = 0 then lam else if j = 1 then 1 else 0 := by
  have hA : ((0 : Fin (m + 2)).val + 1 = j.val
      ∨ j.val + 1 = (0 : Fin (m + 2)).val) ↔ j = 1 := by
    have hv : (0 : Fin (m + 2)).val = 0 := rfl
    constructor
    · intro h
      rcases h with h | h
      · exact Fin.ext (by rw [← h]; simp)
      · omega
    · intro h
      subst h
      exact Or.inl rfl
  simp only [tridiagMat, Matrix.of_apply]
  by_cases h0 : (0 : Fin (m + 2)) = j
  · rw [ite_eq_left h0, ite_eq_left h0.symm]
  · have hj0 : j ≠ 0 := fun h => h0 h.symm
    rw [ite_eq_right h0, ite_eq_right hj0]
    by_cases h1 : j = 1
    · rw [ite_eq_left (hA.mpr h1), ite_eq_left h1]
    · rw [ite_eq_right (fun h => h1 (hA.mp h)), ite_eq_right h1]

/-! ## The recursion (B21) -/

/-- **Lemma 26, recursion (B21)** (arXiv:2004.06516v2, p. 30).  The determinant
of (B20) satisfies `f_{m+2} = λ f_{m+1} − f_m`.  The proof is the Laplace
expansion along the first row: the diagonal minor is `f_{m+1}`, and the
off-diagonal minor is the corner-modified matrix (B22) whose first column is
`e₀`, hence has determinant `f_m`. -/
lemma tridiagMat_det_succ_succ (m : ℕ) (lam : ℝ) :
    (tridiagMat (m + 2) lam).det
      = lam * (tridiagMat (m + 1) lam).det - (tridiagMat m lam).det := by
  rw [Matrix.det_succ_row_zero]
  rw [← Finset.sum_subset (Finset.subset_univ ({0, 1} : Finset (Fin (m + 2)))) ?_]
  · rw [Finset.sum_pair (by simp : (0 : Fin (m + 2)) ≠ 1)]
    have h0 : (-1 : ℝ) ^ (((0 : Fin (m + 2)) : ℕ)) * tridiagMat (m + 2) lam 0 0
        * ((tridiagMat (m + 2) lam).submatrix Fin.succ
            ((0 : Fin (m + 2)).succAbove)).det
        = lam * (tridiagMat (m + 1) lam).det := by
      rw [tridiagMat_zero_row, ite_eq_left rfl, Fin.succAbove_zero,
        tridiagMat_submatrix_succ (m + 1) lam,
        show (((0 : Fin (m + 2)) : ℕ)) = 0 from rfl]
      ring
    have h1 : (-1 : ℝ) ^ (((1 : Fin (m + 2)) : ℕ)) * tridiagMat (m + 2) lam 0 1
        * ((tridiagMat (m + 2) lam).submatrix Fin.succ
            ((1 : Fin (m + 2)).succAbove)).det
        = - (tridiagMat m lam).det := by
      rw [tridiagMat_zero_row, ite_eq_right (by simp : ¬ ((1 : Fin (m + 2)) = 0)),
        ite_eq_left rfl, tridiagMat_minor_first_det,
        show (((1 : Fin (m + 2)) : ℕ)) = 1 from rfl]
      norm_num
    rw [h0, h1]
    ring
  · intro j _ hj
    have hj0 : j ≠ 0 := fun h => hj (by rw [h]; simp)
    have hj1 : j ≠ 1 := fun h => hj (by rw [h]; simp)
    simp [tridiagMat_zero_row, hj0, hj1]

/-! ## The closed form of (B21) -/

/-- The closed form `(x₁^{m+1} − x₂^{m+1})/(x₁ − x₂)` of (B21), p. 30. -/
def triClosedForm (m : ℕ) (lam : ℝ) : ℝ :=
  (triX1 lam ^ (m + 1) - triX2 lam ^ (m + 1)) / (triX1 lam - triX2 lam)

/-- The closed form at `m = 0` equals `f_0 = 1`. -/
lemma triClosedForm_zero (lam : ℝ) (hlam : 2 < |lam|) : triClosedForm 0 lam = 1 := by
  have hne : triX1 lam - triX2 lam ≠ 0 :=
    sub_ne_zero.mpr (triX1_ne_triX2 lam hlam)
  simp only [triClosedForm, Nat.zero_add, pow_one]
  exact div_self hne

/-- The closed form at `m = 1` equals `f_1 = λ`. -/
lemma triClosedForm_one (lam : ℝ) (hlam : 2 < |lam|) : triClosedForm 1 lam = lam := by
  have hne : triX1 lam - triX2 lam ≠ 0 :=
    sub_ne_zero.mpr (triX1_ne_triX2 lam hlam)
  have hfac : triX1 lam ^ (1 + 1) - triX2 lam ^ (1 + 1) = (triX1 lam - triX2 lam) * lam := by
    have h : triX1 lam ^ (1 + 1) - triX2 lam ^ (1 + 1)
        = (triX1 lam - triX2 lam) * (triX1 lam + triX2 lam) := by ring
    rw [h, triX1_add_triX2]
  simp only [triClosedForm]
  rw [hfac]
  exact mul_div_cancel_left₀ lam hne

/-- The elementary identity `x^{(m+2)+1} = (x+y) x^{(m+1)+1} − x y x^{m+1}`. -/
lemma pow_three_factor (x y : ℝ) (m : ℕ) :
    x ^ ((m + 2) + 1) = (x + y) * x ^ ((m + 1) + 1) - (x * y) * x ^ (m + 1) := by
  have h1 : x ^ ((m + 2) + 1) = x ^ (m + 1) * x ^ 2 := by
    rw [show (m + 2) + 1 = (m + 1) + 2 by omega, pow_add]
  have h2 : x ^ ((m + 1) + 1) = x ^ (m + 1) * x := by
    rw [pow_add, pow_one]
  rw [h1, h2]
  ring

/-- The closed form satisfies the recursion (B21). -/
lemma triClosedForm_succ_succ (m : ℕ) (lam : ℝ) (hlam : 2 < |lam|) :
    triClosedForm (m + 2) lam = lam * triClosedForm (m + 1) lam - triClosedForm m lam := by
  have hne : triX1 lam - triX2 lam ≠ 0 :=
    sub_ne_zero.mpr (triX1_ne_triX2 lam hlam)
  have hmul : triX1 lam * triX2 lam = 1 := triX1_mul_triX2 lam (le_of_lt hlam)
  have hsum : triX1 lam + triX2 lam = lam := triX1_add_triX2 lam
  have hkey : triX1 lam ^ ((m + 2) + 1) - triX2 lam ^ ((m + 2) + 1)
      = lam * (triX1 lam ^ ((m + 1) + 1) - triX2 lam ^ ((m + 1) + 1))
        - (triX1 lam * triX2 lam) * (triX1 lam ^ (m + 1) - triX2 lam ^ (m + 1)) := by
    rw [pow_three_factor (triX1 lam) (triX2 lam) m,
      pow_three_factor (triX2 lam) (triX1 lam) m, add_comm (triX2 lam) (triX1 lam), hsum]
    ring
  simp only [triClosedForm]
  rw [hkey, hmul, one_mul, ← mul_div_assoc, ← sub_div]

/-- **Lemma 26, closed form (B21)** (arXiv:2004.06516v2, p. 30).  For
`2 < |λ|` the determinant of the tridiagonal matrix of (B20) is
`(x₁^{m+1} − x₂^{m+1})/(x₁ − x₂)`, where `x₁, x₂` are the two roots of
`x² − λx + 1` fixed in `Qatlib/Papers/HeatEquation20/MainResults/SpectralAppendix.lean`. -/
theorem tridiagDet_closedForm (m : ℕ) (_hm : 0 < m) (lam : ℝ) (hlam : 2 < |lam|) :
    tridiagDet m lam
      = (triX1 lam ^ (m + 1) - triX2 lam ^ (m + 1)) / (triX1 lam - triX2 lam) := by
  have hdet0 : tridiagDet 0 lam = 1 := by simp [tridiagDet]
  have hdet1 : tridiagDet 1 lam = lam := by
    rw [tridiagDet_eq_det, Matrix.det_fin_one]
    simp [tridiagMat]
  have hrec : ∀ n : ℕ, tridiagDet (n + 2) lam
      = lam * tridiagDet (n + 1) lam - tridiagDet n lam := by
    intro n
    rw [tridiagDet_eq_det, tridiagDet_eq_det, tridiagDet_eq_det,
      tridiagMat_det_succ_succ n lam]
  have key : ∀ n : ℕ, tridiagDet n lam = triClosedForm n lam := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => rw [hdet0, triClosedForm_zero lam hlam]
    | one => rw [hdet1, triClosedForm_one lam hlam]
    | more k ih1 ih2 =>
        rw [hrec k, ih1, ih2, triClosedForm_succ_succ k lam hlam]
  exact key m

end Qatlib.Papers.HeatEquation20.MainResults
