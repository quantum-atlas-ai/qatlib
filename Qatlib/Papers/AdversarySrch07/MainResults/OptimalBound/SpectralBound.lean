/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Int.NatAbs
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Qatlib.Papers.AdversarySrch07.MainResults.OptimalBound.OptimalAdversary

/-!
# Spectral norm of the even ordered-search matrix

Proves that the explicit even Toeplitz matrix of [ChildsLee2008] has operator norm exactly one
for positive `m`. The positive vector `uEven m` is fixed by the matrix, and a comparison
argument bounds all real eigenvalues in absolute value by one.

General lemmas convert positive-eigenvector comparisons into eigenvalue bounds and Hermitian
spectral bounds into bounds for the Euclidean operator norm.

## Main statements

* `toeplitz_mulVec_uEven`: Shows that the explicit positive vector is fixed by the Toeplitz
  matrix.
* `toeplitz_eigenvalue_mem_Icc`: Places every real eigenvalue in `[-1, 1]`.
* `toeplitz_l2_opNorm_eq_one`: Proves that the Euclidean operator norm equals one.

## References

* [Childs and Lee, 2008][ChildsLee2008]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators ENNReal Matrix.Norms.L2Operator
open Finset Matrix

namespace Qatlib.Papers.AdversarySrch07.MainResults.OptimalBound

open Qatlib.Papers.AdversarySrch07.MainResults
open Qatlib.Papers.AdversarySrch07.MainResults.XiSequence

/-- For an entrywise nonnegative real matrix, the absolute value of a row applied to `v` is at
most the same row applied to the coordinatewise absolute values of `v`. -/
theorem abs_sum_mul_le {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (v : ι → ℝ)
    (hMnn : ∀ i j, 0 ≤ M i j) (i : ι) :
    |∑ j, M i j * v j| ≤ ∑ j, M i j * |v j| := by
  calc |∑ j, M i j * v j| ≤ ∑ j, |M i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, M i j * |v j| := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [abs_mul, abs_of_nonneg (hMnn i j)]

/-- If an entrywise nonnegative matrix `M` is bounded above by `B` and `B` has a strictly
positive eigenvector with positive eigenvalue `μ`, every real eigenvalue of `M` has absolute
value at most `μ`. See [ChildsLee2008]. -/
theorem abs_eigenvalue_le_of_pos_eigenvector {ι : Type*} [Fintype ι] [Nonempty ι]
    (M B : Matrix ι ι ℝ) (u : ι → ℝ) (μ : ℝ)
    (hMnn : ∀ i j, 0 ≤ M i j) (hMB : ∀ i j, M i j ≤ B i j)
    (hu : ∀ i, 0 < u i) (_hμ : 0 < μ) (hBu : B.mulVec u = μ • u)
    (lam : ℝ) (hlam : ∃ v : ι → ℝ, v ≠ 0 ∧ M.mulVec v = lam • v) : |lam| ≤ μ := by
  obtain ⟨v, hvne, hv⟩ := hlam
  have hBnn : ∀ i j, 0 ≤ B i j := fun i j => (hMnn i j).trans (hMB i j)
  have hu0 : ∀ i, u i ≠ 0 := fun i => (hu i).ne'
  set w : ι → ℝ := fun i => |v i| / u i with hwdef
  obtain ⟨k, -, hkmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι) w Finset.univ_nonempty
  have hkmax' : ∀ i, w i ≤ w k := fun i => hkmax i (Finset.mem_univ i)
  have hwk : 0 < w k := by
    obtain ⟨m, hm⟩ : ∃ m, v m ≠ 0 := by
      by_contra h
      apply hvne
      funext i
      by_contra hi
      exact h ⟨i, hi⟩
    have hmpos : 0 < w m := by
      rw [hwdef]
      exact div_pos (abs_pos.mpr hm) (hu m)
    exact lt_of_lt_of_le hmpos (hkmax' m)
  have key : ∀ i, |lam| * w i ≤ ∑ j, (B i j * u j / u i) * w j := by
    intro i
    have hMv : (M.mulVec v) i = lam * v i := by rw [hv]; simp
    have h2 : |lam * v i| ≤ ∑ j, M i j * |v j| := by
      have hMvi : (M.mulVec v) i = ∑ j, M i j * v j := by
        simp [Matrix.mulVec, dotProduct]
      rw [← hMv, hMvi]
      exact abs_sum_mul_le M v hMnn i
    have h4 : |lam| * |v i| ≤ ∑ j, B i j * |v j| := by
      rw [abs_mul] at h2
      exact h2.trans (Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (hMB i j) (abs_nonneg _))
    have hui : (0 : ℝ) < u i := hu i
    have h5 : |lam| * w i ≤ (∑ j, B i j * |v j|) / u i := by
      rw [hwdef]
      simp only
      rw [show |lam| * (|v i| / u i) = (|lam| * |v i|) / u i by ring]
      exact div_le_div_of_nonneg_right h4 hui.le
    have h6 : (∑ j, B i j * |v j|) / u i = ∑ j, (B i j * u j / u i) * w j := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hwdef]
      simp only
      have huj : u j ≠ 0 := hu0 j
      have hui' : u i ≠ 0 := hu0 i
      field_simp
    simpa only [h6] using! h5
  have hrow : ∑ j, (B k j * u j / u k) = μ := by
    have hBuk : ∑ j, B k j * u j = μ * u k := by
      have := congrFun hBu k
      simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using! this
    rw [← Finset.sum_div, hBuk, mul_div_cancel_right₀ μ (hu0 k)]
  have hbound : |lam| * w k ≤ μ * w k := by
    calc |lam| * w k ≤ ∑ j, (B k j * u j / u k) * w j := key k
      _ ≤ ∑ j, (B k j * u j / u k) * w k :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hkmax' j)
              (div_nonneg (mul_nonneg (hBnn k j) (hu j).le) (hu k).le)
      _ = (∑ j, B k j * u j / u k) * w k := by rw [Finset.sum_mul]
      _ = μ * w k := by rw [hrow]
  exact le_of_mul_le_mul_right hbound hwk

/-- The even weight `gammaEven m k` vanishes when `m < k`. -/
theorem gammaEven_eq_zero_of_lt {m k : ℕ} (hk : m < k) : gammaEven m k = 0 := by
  unfold gammaEven
  rw [AM_eq_zero (by omega : m ≤ k - 1), AM_eq_zero hk.le]
  ring

/-- The even Toeplitz matrix is entrywise nonnegative. -/
theorem toeplitz_gammaEven_nonneg (m : ℕ) (i j : Fin (2 * m)) :
    0 ≤ toeplitz (2 * m) (gammaEven m) i j :=
  gammaEven_nonneg m _

/-- Every coordinate of the reflected even vector `uEven m` is strictly positive. -/
theorem uEven_pos (m : ℕ) (i : Fin (2 * m)) : 0 < uEven m i := by
  unfold uEven
  split_ifs with h
  · exact xi_pos _
  · exact xi_pos _

/-- The even Toeplitz matrix is Hermitian. See [ChildsLee2008]. -/
theorem toeplitz_isHermitian (m : ℕ) :
    (toeplitz (2 * m) (gammaEven m)).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [toeplitz, star_trivial]
  rw [show ((i.val : ℤ) - (j.val : ℤ)) = -(((j.val : ℤ) - (i.val : ℤ))) by ring,
    Int.natAbs_neg]

/-- For a row index `p < 2 * m`, any function `G` with the specified Toeplitz-row summands sums
to the corresponding coordinate of the reflected `xi` vector. -/
theorem toeplitz_row_sum_aux (m p : ℕ) (_hp : p < 2 * m) (G : ℕ → ℝ)
    (hG : ∀ q, G q = gammaEven m (2 * m - Int.natAbs ((p : ℤ) - (q : ℤ))) *
      (if q < m then xi q else xi (2 * m - 1 - q))) :
    ∑ q ∈ Finset.range (2 * m), G q = (if p < m then xi p else xi (2 * m - 1 - p)) := by
  rcases lt_or_ge p m with hpm | hpm
  · have hzero : ∀ q ∈ Finset.range (2 * m), q ∉ Finset.Ico (p + m) (2 * m) → G q = 0 := by
      intro q hq hqnot
      have hq2 : q < 2 * m := Finset.mem_range.mp hq
      have hqlt : q < p + m := by
        by_contra h
        exact hqnot (Finset.mem_Ico.mpr ⟨by omega, hq2⟩)
      have hd : Int.natAbs ((p : ℤ) - (q : ℤ)) < m := by
        by_cases hqp : q ≤ p
        · rw [Int.natAbs_natCast_sub_natCast_of_ge hqp]; omega
        · rw [Int.natAbs_natCast_sub_natCast_of_le (by omega : p ≤ q)]; omega
      have hk : m < 2 * m - Int.natAbs ((p : ℤ) - (q : ℤ)) := by omega
      rw [hG q, gammaEven_eq_zero_of_lt hk, zero_mul]
    have hstep1 : ∑ q ∈ Finset.range (2 * m), G q = ∑ q ∈ Finset.Ico (p + m) (2 * m), G q := by
      refine (Finset.sum_subset ?_ hzero).symm
      intro x hx
      exact Finset.mem_range.mpr (Finset.mem_Ico.mp hx).2
    have hmap : ∑ q ∈ Finset.Ico (p + m) (2 * m), G q
        = ∑ i ∈ Finset.range (m - p), G (2 * m - 1 - i) := by
      have h := Finset.sum_Ico_reflect G 0 (m := m - p) (n := 2 * m - 1) (by omega)
      rw [Nat.Ico_zero_eq_range] at h
      have h1 : 2 * m - 1 + 1 - (m - p) = p + m := by omega
      have h2 : 2 * m - 1 + 1 - 0 = 2 * m := by omega
      rw [h1, h2] at h
      exact h.symm
    have hstep3 : ∑ i ∈ Finset.range (m - p), G (2 * m - 1 - i)
        = ∑ i ∈ Finset.range (m - p), (AM m (i + p) - AM m (i + p + 1)) * xi i := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi' : i < m - p := Finset.mem_range.mp hi
      rw [hG (2 * m - 1 - i)]
      rw [if_neg (by omega : ¬(2 * m - 1 - i < m))]
      rw [Int.natAbs_natCast_sub_natCast_of_le (by omega : p ≤ 2 * m - 1 - i)]
      rw [show 2 * m - ((2 * m - 1 - i) - p) = (i + p) + 1 by omega]
      rw [show 2 * m - 1 - (2 * m - 1 - i) = i by omega]
      rw [gammaEven_apply_succ m (i + p)]
    rw [hstep1, hmap, hstep3, if_pos hpm]
    exact eigen_identity m p hpm
  · have hzero : ∀ q ∈ Finset.range (2 * m), q ∉ Finset.range (p - m + 1) → G q = 0 := by
      intro q hq hqnot
      have hq2 : q < 2 * m := Finset.mem_range.mp hq
      have hqgt : p - m < q := by
        by_contra h
        exact hqnot (Finset.mem_range.mpr (by omega))
      have hd : Int.natAbs ((p : ℤ) - (q : ℤ)) < m := by
        by_cases hqp : q ≤ p
        · rw [Int.natAbs_natCast_sub_natCast_of_ge hqp]; omega
        · rw [Int.natAbs_natCast_sub_natCast_of_le (by omega : p ≤ q)]; omega
      have hk : m < 2 * m - Int.natAbs ((p : ℤ) - (q : ℤ)) := by omega
      rw [hG q, gammaEven_eq_zero_of_lt hk, zero_mul]
    have hstep1 : ∑ q ∈ Finset.range (2 * m), G q = ∑ q ∈ Finset.range (p - m + 1), G q := by
      refine (Finset.sum_subset ?_ hzero).symm
      intro x hx
      exact Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega)
    have hstep2 : ∑ q ∈ Finset.range (p - m + 1), G q
        = ∑ q ∈ Finset.range (p - m + 1),
            (AM m (q + (m - (p - m) - 1)) -
              AM m (q + (m - (p - m) - 1) + 1)) * xi q := by
      refine Finset.sum_congr rfl (fun q hq => ?_)
      have hqle : q ≤ p - m := by have := Finset.mem_range.mp hq; omega
      have hqm : q < m := by omega
      have hqle' : q ≤ p := by omega
      have hd : Int.natAbs ((p : ℤ) - (q : ℤ)) = p - q :=
        Int.natAbs_natCast_sub_natCast_of_ge hqle'
      rw [hG q, if_pos hqm, hd]
      rw [show 2 * m - (p - q) = (q + (m - (p - m) - 1)) + 1 by omega]
      rw [gammaEven_apply_succ m (q + (m - (p - m) - 1))]
    rw [hstep1, hstep2, if_neg (by omega : ¬ p < m)]
    have hj : m - (p - m) - 1 < m := by omega
    have hrange : m - (m - (p - m) - 1) = p - m + 1 := by omega
    have harg : m - (p - m) - 1 = 2 * m - 1 - p := by omega
    have h := eigen_identity m (m - (p - m) - 1) hj
    rw [hrange] at h
    rw [← harg]
    exact h

/-- For `p < 2 * m`, the Toeplitz row applied to the reflected `xi` coordinates equals the
corresponding reflected coordinate. See [ChildsLee2008]. -/
theorem toeplitz_row_sum (m p : ℕ) (hp : p < 2 * m) :
    ∑ q ∈ Finset.range (2 * m),
        gammaEven m (2 * m - Int.natAbs ((p : ℤ) - (q : ℤ))) *
          (if q < m then xi q else xi (2 * m - 1 - q))
      = (if p < m then xi p else xi (2 * m - 1 - p)) :=
  toeplitz_row_sum_aux m p hp
    (fun q => gammaEven m (2 * m - Int.natAbs ((p : ℤ) - (q : ℤ))) *
      (if q < m then xi q else xi (2 * m - 1 - q)))
    (fun _ => rfl)

/-- The even Toeplitz matrix fixes `uEven m` under matrix-vector multiplication. See
[ChildsLee2008]. -/
theorem toeplitz_mulVec_uEven (m : ℕ) :
    (toeplitz (2 * m) (gammaEven m)).mulVec (uEven m) = uEven m := by
  funext p
  calc ((toeplitz (2 * m) (gammaEven m)).mulVec (uEven m)) p
      = ∑ i : Fin (2 * m),
          (toeplitz (2 * m) (gammaEven m) p i) * (uEven m i) := rfl
    _ = ∑ q ∈ Finset.range (2 * m),
          gammaEven m (2 * m - Int.natAbs ((p.val : ℤ) - (q : ℤ))) *
            (if q < m then xi q else xi (2 * m - 1 - q)) := by
        rw [Finset.sum_fin_eq_sum_range]
        refine Finset.sum_congr rfl (fun q hq => ?_)
        rw [dif_pos (Finset.mem_range.mp hq)]
        simp [toeplitz, uEven]
    _ = (if p.val < m then xi p.val else xi (2 * m - 1 - p.val)) :=
        toeplitz_row_sum m p.val p.isLt
    _ = uEven m p := by simp [uEven]

/-- For `m > 0`, every real eigenvalue of the even Toeplitz matrix has absolute value at most
one. See [ChildsLee2008]. -/
theorem toeplitz_eigenvalue_abs_le_one (m : ℕ) (hm : 0 < m) (lam : ℝ)
    (hlam : ∃ v : Fin (2 * m) → ℝ, v ≠ 0 ∧
      (toeplitz (2 * m) (gammaEven m)).mulVec v = lam • v) : |lam| ≤ 1 := by
  haveI : Nonempty (Fin (2 * m)) := ⟨⟨0, by omega⟩⟩
  exact abs_eigenvalue_le_of_pos_eigenvector (toeplitz (2 * m) (gammaEven m))
    (toeplitz (2 * m) (gammaEven m)) (uEven m) 1
    (toeplitz_gammaEven_nonneg m) (fun i j => le_rfl) (uEven_pos m) zero_lt_one
    (by rw [toeplitz_mulVec_uEven]; simp) lam hlam

/-- For `m > 0`, the even Toeplitz matrix has eigenvalue one with a nonzero real eigenvector.
See [ChildsLee2008]. -/
theorem toeplitz_hasEigenvalue_one (m : ℕ) (hm : 0 < m) :
    ∃ v : Fin (2 * m) → ℝ, v ≠ 0 ∧
      (toeplitz (2 * m) (gammaEven m)).mulVec v = (1 : ℝ) • v := by
  refine ⟨uEven m, ?_, by rw [toeplitz_mulVec_uEven]; simp⟩
  intro h
  have hpos := uEven_pos m ⟨0, by omega⟩
  rw [h] at hpos
  simp at hpos

/-- For `m > 0`, every real eigenvalue of the even Toeplitz matrix lies in `[-1, 1]`. See
[ChildsLee2008]. -/
theorem toeplitz_eigenvalue_mem_Icc (m : ℕ) (hm : 0 < m) (lam : ℝ)
    (hlam : ∃ v : Fin (2 * m) → ℝ, v ≠ 0 ∧
      (toeplitz (2 * m) (gammaEven m)).mulVec v = lam • v) : lam ∈ Set.Icc (-1 : ℝ) 1 := by
  have h := abs_le.mp (toeplitz_eigenvalue_abs_le_one m hm lam hlam)
  exact ⟨h.1, h.2⟩

/-- A real Hermitian matrix whose real eigenvalues all have absolute value at most one has
Euclidean operator norm at most one. See [ChildsLee2008]. -/
theorem l2_opNorm_le_one_of_eigenvalue_mem {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (h : ∀ lam : ℝ, (∃ v : ι → ℝ, v ≠ 0 ∧ A *ᵥ v = lam • v) → |lam| ≤ 1) :
    ‖A‖ ≤ 1 := by
  have hU : ‖(((hA.eigenvectorUnitary : unitary (Matrix ι ι ℝ)) : Matrix ι ι ℝ))‖ = 1 := by
    have h1 := Matrix.l2_opNorm_conjTranspose_mul_self
      (((hA.eigenvectorUnitary : unitary (Matrix ι ι ℝ)) : Matrix ι ι ℝ))
    have h2 : (((hA.eigenvectorUnitary : unitary (Matrix ι ι ℝ)) : Matrix ι ι ℝ))ᴴ *
        ((hA.eigenvectorUnitary : unitary (Matrix ι ι ℝ)) : Matrix ι ι ℝ) = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      simp
    rw [h2, norm_one] at h1
    nlinarith [norm_nonneg (((hA.eigenvectorUnitary : unitary (Matrix ι ι ℝ)) : Matrix ι ι ℝ))]
  have hUs : ‖star (((hA.eigenvectorUnitary : unitary (Matrix ι ι ℝ)) : Matrix ι ι ℝ))‖ = 1 := by
    rw [Matrix.star_eq_conjTranspose, Matrix.l2_opNorm_conjTranspose, hU]
  have hspec : ‖A‖ = ‖((hA.eigenvectorUnitary : unitary (Matrix ι ι ℝ)) : Matrix ι ι ℝ) *
      diagonal (hA.eigenvalues) *
      star (((hA.eigenvectorUnitary : unitary (Matrix ι ι ℝ)) : Matrix ι ι ℝ))‖ := by
    nth_rewrite 1 [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply]
  have hD : ‖(diagonal (hA.eigenvalues) : Matrix ι ι ℝ)‖ = ‖hA.eigenvalues‖ :=
    Matrix.l2_opNorm_diagonal _
  have hne : ∀ i : ι, (fun j => hA.eigenvectorBasis i j) ≠ 0 := by
    intro i h0
    have h1 : hA.eigenvectorBasis i = 0 := by
      ext j
      exact congrFun h0 j
    have h2 := hA.eigenvectorBasis.orthonormal.1 i
    rw [h1, norm_zero] at h2
    exact zero_ne_one h2
  have hlam : ‖hA.eigenvalues‖ ≤ 1 := by
    refine pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun i => ?_
    rw [Real.norm_eq_abs]
    refine h _ ⟨fun j => hA.eigenvectorBasis i j, hne i, ?_⟩
    simpa using! hA.mulVec_eigenvectorBasis i
  rw [hspec]
  calc ‖((hA.eigenvectorUnitary : unitary (Matrix ι ι ℝ)) : Matrix ι ι ℝ) *
        diagonal (hA.eigenvalues) *
        star (((hA.eigenvectorUnitary : unitary (Matrix ι ι ℝ)) : Matrix ι ι ℝ))‖
      ≤ ‖((hA.eigenvectorUnitary : unitary (Matrix ι ι ℝ)) : Matrix ι ι ℝ) *
          diagonal (hA.eigenvalues)‖ *
          ‖star (((hA.eigenvectorUnitary : unitary (Matrix ι ι ℝ)) : Matrix ι ι ℝ))‖ :=
        Matrix.l2_opNorm_mul _ _
    _ ≤ (‖((hA.eigenvectorUnitary : unitary (Matrix ι ι ℝ)) : Matrix ι ι ℝ)‖ *
          ‖(diagonal (hA.eigenvalues) : Matrix ι ι ℝ)‖) *
          ‖star (((hA.eigenvectorUnitary : unitary (Matrix ι ι ℝ)) : Matrix ι ι ℝ))‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ = ‖hA.eigenvalues‖ := by rw [hU, hUs, hD]; ring
    _ ≤ 1 := hlam

/-- For `m > 0`, the even Toeplitz matrix has Euclidean operator norm at most one. See
[ChildsLee2008]. -/
theorem toeplitz_l2_opNorm_le_one (m : ℕ) (hm : 0 < m) :
    ‖(toeplitz (2 * m) (gammaEven m) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)‖ ≤ 1 := by
  haveI : Nonempty (Fin (2 * m)) := ⟨⟨0, by omega⟩⟩
  exact l2_opNorm_le_one_of_eigenvalue_mem _
    (toeplitz_isHermitian m) (fun lam hlam => toeplitz_eigenvalue_abs_le_one m hm lam hlam)

/-- A real matrix fixing a nonzero vector has Euclidean operator norm at least one. See
[ChildsLee2008]. -/
theorem l2_opNorm_ge_one_of_unit_eigenvector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (u : ι → ℝ) (hu : u ≠ 0) (hAu : A *ᵥ u = u) :
    1 ≤ ‖A‖ := by
  have hnorm := ContinuousLinearMap.le_opNorm
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A)
    (WithLp.toLp 2 u : EuclideanSpace ℝ ι)
  have hTx : Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A
      (WithLp.toLp 2 u : EuclideanSpace ℝ ι) = (WithLp.toLp 2 u : EuclideanSpace ℝ ι) := by
    rw [Matrix.toEuclideanCLM_toLp, hAu]
  rw [hTx, Matrix.l2_opNorm_toEuclideanCLM] at hnorm
  have hxne : (WithLp.toLp 2 u : EuclideanSpace ℝ ι) ≠ 0 := by
    intro h
    exact hu ((WithLp.toLp_eq_zero (p := 2) (x := u)).mp h)
  have hpos : 0 < ‖(WithLp.toLp 2 u : EuclideanSpace ℝ ι)‖ := norm_pos_iff.mpr hxne
  nlinarith [hnorm, hpos]

/-- For `m > 0`, the even Toeplitz matrix has Euclidean operator norm at least one. See
[ChildsLee2008]. -/
theorem toeplitz_l2_opNorm_ge_one (m : ℕ) (hm : 0 < m) :
    1 ≤ ‖(toeplitz (2 * m) (gammaEven m) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)‖ :=
  l2_opNorm_ge_one_of_unit_eigenvector _
    (uEven m) (by
      intro h
      have hpos := uEven_pos m ⟨0, by omega⟩
      rw [h] at hpos
      simp at hpos)
    (toeplitz_mulVec_uEven m)

/-- For `m > 0`, the even Toeplitz matrix has Euclidean operator norm exactly one. See
[ChildsLee2008]. -/
theorem toeplitz_l2_opNorm_eq_one (m : ℕ) (hm : 0 < m) :
    ‖(toeplitz (2 * m) (gammaEven m) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)‖ = 1 :=
  le_antisymm (toeplitz_l2_opNorm_le_one m hm) (toeplitz_l2_opNorm_ge_one m hm)

end Qatlib.Papers.AdversarySrch07.MainResults.OptimalBound
