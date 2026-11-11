/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Real.Pi.Bounds

set_option backward.isDefEq.respectTransparency false

/-!
# The periodic second-derivative spectral matrix of Childs--Liu--Ostrander

Source: A. M. Childs, J.-P. Liu, A. Ostrander, *High-precision quantum algorithms for
partial differential equations*, fixed arXiv:2002.07868v2 (published Quantum 5, 574 (2021)).
Equation (4.59) defines the matrix `D_n^(2)` of the pseudo-spectral linear system for periodic
boundary conditions: every off-centre diagonal entry is the symbol value `-((k - ⌊n/2⌋)π)^2`,
while the centre row `⌊n/2⌋` is the all-ones row that carries the constant mode.

The source Lemma 7 (Section 4.3, Appendix B) computes the extreme singular values of this
matrix.  The present module sets up the matrix and proves the two norm bounds on which the
source proof rests:

* the largest singular value bound `σ_max(D_n^(2)) ≤ (2n)^{5/2}` from the `ℓ∞` row-sum bound
  (`(B.1)`) and the Frobenius/`ℓ∞` comparison;
* the smallest singular value bound `σ_min(D_n^(2)) ≥ 1/√2`, from the explicit inverse
  (`(B.2)`) and its Frobenius bound (`(B.3)`).

The singular values of a square matrix `A` over `EuclideanSpace` are the eigenvalues of
`√(Aᴴ A)`, so `σ_max(A)` is the `ℓ²` operator norm of `A` and, when `A` is invertible,
`σ_min(A) = 1 / ‖A⁻¹‖`.  Both statements are proved in that operator-norm form.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.QuantumPDE20.MainResults

/-- The centre node `⌊n/2⌋` of the `n+1` grid points of (4.59). -/
def center (n : ℕ) : Fin (n + 1) := ⟨n / 2, by omega⟩

/-- The centre index evaluates to `n / 2`. -/
@[simp] lemma center_val (n : ℕ) : (center n : ℕ) = n / 2 := rfl

/-- The periodic second-derivative spectral matrix `D_n^(2)` of (4.59). -/
def periodicSecondDerivative (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun k l =>
    if k = center n then 1
    else if k = l then -(((k : ℝ) - (center n : ℝ)) * Real.pi) ^ 2
    else 0

/-- The explicit inverse `(D_n^(2))⁻¹` of (B.2).  The centre row is the all-ones row of the
inverse: its centre entry is `1` and its `j`-th entry is `1/((j-⌊n/2⌋)π)^2`. -/
def periodicSecondDerivativeInv (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun k l =>
    if k = center n then
      (if l = center n then 1 else (((l : ℝ) - (center n : ℝ)) * Real.pi) ^ 2)⁻¹
    else if k = l then -((((k : ℝ) - (center n : ℝ)) * Real.pi) ^ 2)⁻¹
    else 0

/-- The centre row of `D_n^(2)` is the all-ones row, as in (4.59). -/
@[simp] lemma periodicSecondDerivative_center_row (n : ℕ) (l : Fin (n + 1)) :
    periodicSecondDerivative n (center n) l = 1 := by
  simp [periodicSecondDerivative]

/-- Every off-centre row of `D_n^(2)` has its single nonzero entry on the diagonal. -/
@[simp] lemma periodicSecondDerivative_off_row {n : ℕ} {k : Fin (n + 1)} (hk : k ≠ center n)
    (l : Fin (n + 1)) :
    periodicSecondDerivative n k l =
      if k = l then -(((k : ℝ) - (center n : ℝ)) * Real.pi) ^ 2 else 0 := by
  simp [periodicSecondDerivative, hk]

/-- The diagonal entry of an off-centre row is the symbol value `-((k-⌊n/2⌋)π)^2`. -/
@[simp] lemma periodicSecondDerivative_diag {n : ℕ} {k : Fin (n + 1)} (hk : k ≠ center n) :
    periodicSecondDerivative n k k = -(((k : ℝ) - (center n : ℝ)) * Real.pi) ^ 2 := by
  simp [periodicSecondDerivative, hk]

/-- Off-centre off-diagonal entries of `D_n^(2)` vanish. -/
@[simp] lemma periodicSecondDerivative_off_diag {n : ℕ} {k l : Fin (n + 1)}
    (hk : k ≠ center n) (hkl : k ≠ l) : periodicSecondDerivative n k l = 0 := by
  simp [periodicSecondDerivative, hk, hkl]

/-- The centre entry of the inverse `(B.2)` is `1`. -/
@[simp] lemma periodicSecondDerivativeInv_center_center (n : ℕ) :
    periodicSecondDerivativeInv n (center n) (center n) = 1 := by
  simp [periodicSecondDerivativeInv]

/-- The centre row of the inverse carries the values `1/((l-⌊n/2⌋)π)^2`. -/
@[simp] lemma periodicSecondDerivativeInv_center_off {n : ℕ} {l : Fin (n + 1)}
    (hl : l ≠ center n) :
    periodicSecondDerivativeInv n (center n) l =
      ((((l : ℝ) - (center n : ℝ)) * Real.pi) ^ 2)⁻¹ := by
  simp [periodicSecondDerivativeInv, hl]

/-- The diagonal entries of the inverse off the centre row are `-1/((k-⌊n/2⌋)π)^2`. -/
@[simp] lemma periodicSecondDerivativeInv_off_diag {n : ℕ} {k : Fin (n + 1)}
    (hk : k ≠ center n) :
    periodicSecondDerivativeInv n k k = -((((k : ℝ) - (center n : ℝ)) * Real.pi) ^ 2)⁻¹ := by
  simp [periodicSecondDerivativeInv, hk]

/-- Off-centre off-diagonal entries of the inverse vanish. -/
@[simp] lemma periodicSecondDerivativeInv_off_off {n : ℕ} {k l : Fin (n + 1)}
    (hk : k ≠ center n) (hkl : k ≠ l) : periodicSecondDerivativeInv n k l = 0 := by
  simp [periodicSecondDerivativeInv, hk, hkl]

/-! ## Generic operator-norm bounds -/

/-- **Operator norm from row sums.**  If every row of `A` has absolute sum at most `R`, then the
`ℓ²` operator norm of `A` is at most `√N · R`.  This is the row-sum comparison used for the
`ℓ∞`-norm step `(B.1)` of the source proof. -/
theorem opNorm_le_of_row_sums {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hrow : ∀ i, ∑ j, |A i j| ≤ R) : ‖A‖ ≤ Real.sqrt N * R := by
  refine (Matrix.l2_opNorm_toEuclideanCLM (𝕜 := ℝ) A).symm.trans_le ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun x => ?_)
  have hx : ∀ i, |(A *ᵥ x) i| ≤ R * ‖x‖ := by
    intro i
    calc |(A *ᵥ x) i| ≤ (∑ j, |A i j|) * ‖x‖ := by
          rw [Matrix.mulVec, dotProduct]
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          calc ∑ j, |A i j * x j| = ∑ j, |A i j| * |x j| := by simp [abs_mul]
            _ ≤ ∑ j, |A i j| * ‖x‖ := by
                refine Finset.sum_le_sum (fun j _ => ?_)
                exact mul_le_mul_of_nonneg_left (by simpa using PiLp.norm_apply_le x j) (abs_nonneg _)
            _ = (∑ j, |A i j|) * ‖x‖ := by rw [Finset.sum_mul]
      _ ≤ R * ‖x‖ := by
          exact mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg _)
  have hsq : ∑ i, ((A *ᵥ x) i) ^ 2 ≤ (N : ℝ) * (R * ‖x‖) ^ 2 := by
    calc ∑ i, ((A *ᵥ x) i) ^ 2 ≤ ∑ _i : Fin N, (R * ‖x‖) ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [show (R * ‖x‖) ^ 2 = |R * ‖x‖| ^ 2 from (sq_abs _).symm]
          exact (sq_le_sq).mpr (by simpa [abs_of_nonneg (mul_nonneg hR (norm_nonneg x))] using hx i)
      _ = (N : ℝ) * (R * ‖x‖) ^ 2 := by simp
  have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A x‖ = Real.sqrt (∑ i, ((A *ᵥ x) i) ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    simp
  rw [hnorm]
  have hN : (0:ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hsq' : Real.sqrt (∑ i, ((A *ᵥ x) i) ^ 2) ≤ Real.sqrt ((N : ℝ) * (R * ‖x‖) ^ 2) :=
    Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_mul (Nat.cast_nonneg N), Real.sqrt_sq (by positivity)] at hsq'
  calc Real.sqrt (∑ i, ((A *ᵥ x) i) ^ 2) ≤ Real.sqrt (N : ℝ) * (R * ‖x‖) := hsq'
    _ = Real.sqrt (N : ℝ) * R * ‖x‖ := by ring

/-- **Operator norm from the entrywise square sum.**  If the sum of the squares of the entries of
`A` is at most `C²`, then the `ℓ²` operator norm of `A` is at most `C`; this is the
operator-norm/Frobenius comparison behind `(B.4)`. -/
theorem opNorm_le_of_sum_sq {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hsum : ∑ i, ∑ j, (A i j) ^ 2 ≤ C ^ 2) : ‖A‖ ≤ C := by
  refine (Matrix.l2_opNorm_toEuclideanCLM (𝕜 := ℝ) A).symm.trans_le ?_
  refine ContinuousLinearMap.opNorm_le_bound _ hC (fun x => ?_)
  have hrow : ∀ i, ((A *ᵥ x) i) ^ 2 ≤ (∑ j, (A i j) ^ 2) * ‖x‖ ^ 2 := by
    intro i
    have h1 : |(A *ᵥ x) i| ≤ ∑ j, |A i j| * |x j| := by
      rw [Matrix.mulVec, dotProduct]
      calc |∑ j, A i j * x j| ≤ ∑ j, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j, |A i j| * |x j| := by simp [abs_mul]
    have h2 : (∑ j, |A i j| * |x j|) ^ 2 ≤ (∑ j, (A i j) ^ 2) * ∑ j, (x j) ^ 2 := by
      have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin N))
        (fun j => |A i j|) (fun j => |x j|)
      simpa [sq_abs, mul_comm] using this
    have h3 : ∑ j, (x j) ^ 2 = ‖x‖ ^ 2 := by
      simpa using (EuclideanSpace.real_norm_sq_eq x).symm
    calc ((A *ᵥ x) i) ^ 2 = |(A *ᵥ x) i| ^ 2 := (sq_abs _).symm
      _ ≤ (∑ j, |A i j| * |x j|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ ≤ (∑ j, (A i j) ^ 2) * ‖x‖ ^ 2 := by rw [← h3]; exact h2
  have hsum' : ∑ i, ((A *ᵥ x) i) ^ 2 ≤ C ^ 2 * ‖x‖ ^ 2 := by
    calc ∑ i, ((A *ᵥ x) i) ^ 2 ≤ ∑ i, (∑ j, (A i j) ^ 2) * ‖x‖ ^ 2 :=
          Finset.sum_le_sum (fun i _ => hrow i)
      _ = (∑ i, ∑ j, (A i j) ^ 2) * ‖x‖ ^ 2 := by rw [Finset.sum_mul]
      _ ≤ C ^ 2 * ‖x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hsum (by positivity)
  have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A x‖ = Real.sqrt (∑ i, ((A *ᵥ x) i) ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    simp
  rw [hnorm]
  calc Real.sqrt (∑ i, ((A *ᵥ x) i) ^ 2) ≤ Real.sqrt (C ^ 2 * ‖x‖ ^ 2) :=
        Real.sqrt_le_sqrt hsum'
    _ = C * ‖x‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hC, Real.sqrt_sq (norm_nonneg _)]

/-! ## The explicit inverse `(B.2)` -/

/-- **The centre column of the inverse.**  The `⌊n/2⌋`-th column of `(D_n^(2))⁻¹` sums to `1`,
because the only nonzero entry is the centre entry `1`. -/
lemma sum_inv_col_center (n : ℕ) :
    (∑ l, periodicSecondDerivativeInv n l (center n)) = 1 := by
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ (center n)),
      Finset.sum_eq_zero]
  · simp
  · intro a ha
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at ha
    simp [ha]

/-- **An off-centre column of the inverse.**  Every off-centre column has exactly the two entries
`1/((j-⌊n/2⌋)π)^2` (centre row) and `-1/((j-⌊n/2⌋)π)^2` (diagonal), hence sums to zero. -/
lemma sum_inv_col_off (n : ℕ) {j : Fin (n + 1)} (hj : j ≠ center n) :
    (∑ l, periodicSecondDerivativeInv n l j) = 0 := by
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ (center n)),
      Finset.sum_eq_single j]
  · simp [hj]
  · intro a ha haj
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and] at ha
    simp [ha, haj]
  · intro h
    exact absurd (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simpa using hj⟩) h

/-- **The centre offset is nonzero away from the centre.**  Used to clear the `(k-⌊n/2⌋)`
denominators of `(B.2)`. -/
lemma sub_center_ne_zero {n : ℕ} {i : Fin (n + 1)} (hi : i ≠ center n) :
    ((i : ℝ) - (center n : ℝ)) ≠ 0 := by
  rw [sub_ne_zero]
  exact fun h => hi (Fin.ext (by exact_mod_cast h))

/-- **`D · D⁻¹ = 1`.**  The explicit inversion formula `(B.2)` really inverts `D_n^(2)`. -/
theorem periodicSecondDerivative_mul_inv (n : ℕ) :
    periodicSecondDerivative n * periodicSecondDerivativeInv n = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  rcases eq_or_ne i (center n) with hi | hi
  · subst hi
    simp only [periodicSecondDerivative_center_row, one_mul]
    rcases eq_or_ne j (center n) with hj | hj
    · subst hj
      rw [sum_inv_col_center, if_pos rfl]
    · rw [sum_inv_col_off n hj, if_neg (Ne.symm hj)]
  · rw [Finset.sum_eq_single i]
    · rw [periodicSecondDerivative_diag hi]
      rcases eq_or_ne i j with hij | hij
      · subst hij
        rw [periodicSecondDerivativeInv_off_diag hi, if_pos rfl]
        have h : ((i : ℝ) - (center n : ℝ)) ≠ 0 := sub_center_ne_zero hi
        field_simp
      · rw [periodicSecondDerivativeInv_off_off hi hij, if_neg hij, mul_zero]
    · intro a _ hai
      rw [periodicSecondDerivative_off_diag hi (Ne.symm hai), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h

/-- **`D⁻¹ · D = 1`.**  The other side of the inversion identity `(B.2)`; it follows from
`D · D⁻¹ = 1` because square matrices over a field are Dedekind finite. -/
theorem periodicSecondDerivative_inv_mul (n : ℕ) :
    periodicSecondDerivativeInv n * periodicSecondDerivative n = 1 :=
  mul_eq_one_comm.mp (periodicSecondDerivative_mul_inv n)

/-! ## Row sums of `D_n^(2)` and the `ℓ∞` step `(B.1)` -/

/-- The absolute row sums of the centre row, which is the all-ones row. -/
lemma row_sum_center (n : ℕ) :
    (∑ j, |periodicSecondDerivative n (center n) j|) = ((n : ℝ) + 1) := by
  simp

/-- The absolute row sums of an off-centre row: only the diagonal entry survives. -/
lemma row_sum_off (n : ℕ) {i : Fin (n + 1)} (hi : i ≠ center n) :
    (∑ j, |periodicSecondDerivative n i j|) =
      (((i : ℝ) - (center n : ℝ)) * Real.pi) ^ 2 := by
  rw [Finset.sum_eq_single i]
  · simp only [periodicSecondDerivative_diag hi, abs_neg, abs_pow, abs_mul, abs_of_pos Real.pi_pos,
      mul_pow, sq_abs]
  · intro a _ hai
    simp [hi, Ne.symm hai]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **Distance to the centre.**  Every grid point is within `(n+1)/2` of `⌊n/2⌋`. -/
lemma abs_sub_center_le (n : ℕ) (i : Fin (n + 1)) :
    |(i : ℝ) - (center n : ℝ)| ≤ ((n : ℝ) + 1) / 2 := by
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
  have hin : (i : ℝ) ≤ (n : ℝ) := by
    have : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.2
    exact_mod_cast this
  have hc0 : (0 : ℝ) ≤ (center n : ℝ) := Nat.cast_nonneg _
  have hcn : (center n : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.div_le_self n 2
  have hc_half : (center n : ℝ) ≤ (n : ℝ) / 2 := by
    have h : (n / 2) * 2 ≤ n := Nat.div_mul_le_self n 2
    have h' : ((n / 2 : ℕ) : ℝ) * 2 ≤ (n : ℝ) := by exact_mod_cast h
    have hcval : (center n : ℝ) = ((n / 2 : ℕ) : ℝ) := rfl
    rw [hcval]; linarith
  have hc2 : ((n : ℝ) - 1) / 2 ≤ (center n : ℝ) := by
    have h2 : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2
    have h2r : 2 * ((n / 2 : ℕ) : ℝ) + ((n % 2 : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast h2
    have hmodr : ((n % 2 : ℕ) : ℝ) ≤ 1 := by
      have := Nat.le_of_lt_succ (Nat.mod_lt n (by norm_num : 0 < 2))
      exact_mod_cast this
    have hkey : ((n : ℝ) - 1) / 2 = ((n / 2 : ℕ) : ℝ) + (((n % 2 : ℕ) : ℝ) - 1) / 2 := by
      linarith
    rw [hkey]
    have hcval : (center n : ℝ) = ((n / 2 : ℕ) : ℝ) := rfl
    have : (((n % 2 : ℕ) : ℝ) - 1) / 2 ≤ 0 := by linarith
    linarith
  by_cases hle : (i : ℝ) ≤ (center n : ℝ)
  · rw [abs_of_nonpos (by linarith), neg_sub]
    linarith
  · rw [abs_of_pos (by linarith)]
    linarith

/-- **The `ℓ∞`-norm bound `(B.1)`.**  For `n ≥ 4` every absolute row sum of `D_n^(2)` is at most
`((n+1)π/2)^2`. -/
lemma row_sum_le (n : ℕ) (hn : 4 ≤ n) (i : Fin (n + 1)) :
    (∑ j, |periodicSecondDerivative n i j|) ≤ ((((n : ℝ) + 1) * Real.pi) / 2) ^ 2 := by
  rcases eq_or_ne i (center n) with hi | hi
  · subst hi
    rw [row_sum_center]
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have hsq : (9 : ℝ) / 4 ≤ (Real.pi / 2) ^ 2 := by nlinarith
    nlinarith [hsq, hn1, sq_nonneg ((n : ℝ) + 1)]
  · rw [row_sum_off n hi]
    have hd := abs_sub_center_le n i
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    have hsq : |((i : ℝ) - (center n : ℝ)) * Real.pi| ≤ (((n : ℝ) + 1) / 2) * Real.pi := by
      rw [abs_mul, abs_of_pos hpi]
      exact mul_le_mul_of_nonneg_right hd hpi.le
    rw [← sq_abs (((i : ℝ) - (center n : ℝ)) * Real.pi)]
    have hpos : (0 : ℝ) ≤ (((n : ℝ) + 1) / 2) * Real.pi := by positivity
    calc |((i : ℝ) - (center n : ℝ)) * Real.pi| ^ 2
        ≤ ((((n : ℝ) + 1) / 2) * Real.pi) ^ 2 := by
          exact pow_le_pow_left₀ (abs_nonneg _) hsq 2
      _ = ((((n : ℝ) + 1) * Real.pi) / 2) ^ 2 := by ring

/-- **Lemma 7, first bound (`(4.61)`, `(B.4)`).**  For `n ≥ 4` the largest singular value of
`D_n^(2)` is at most `(2n)^{5/2}`.  Stated as the `ℓ²` operator-norm bound
`‖D_n^(2)‖ ≤ √((2n)^5)`. -/
theorem lemma7_sigmaMax (n : ℕ) (hn : 4 ≤ n) :
    ‖periodicSecondDerivative n‖ ≤ Real.sqrt ((2 * (n : ℝ)) ^ 5) := by
  have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hR : (0 : ℝ) ≤ ((((n : ℝ) + 1) * Real.pi) / 2) ^ 2 := by positivity
  have h1 : ‖periodicSecondDerivative n‖ ≤
      Real.sqrt ((n : ℝ) + 1) * ((((n : ℝ) + 1) * Real.pi) / 2) ^ 2 := by
    have := opNorm_le_of_row_sums (N := n + 1) (A := periodicSecondDerivative n) hR
      (row_sum_le n hn)
    simpa using this
  refine h1.trans ?_
  rw [Real.le_sqrt (by positivity) (by positivity)]
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hpi4 : Real.pi ^ 4 ≤ 99 := by
    have h4 : Real.pi < 3.15 := Real.pi_lt_d2
    have h0 : (0 : ℝ) < Real.pi := Real.pi_pos
    have h : Real.pi ^ 4 < (3.15 : ℝ) ^ 4 := pow_lt_pow_left₀ h4 h0.le (by norm_num)
    nlinarith
  have hn4 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hR2 : (((((n : ℝ) + 1) * Real.pi) / 2) ^ 2) ^ 2 ≤ (99 / 16) * ((n : ℝ) + 1) ^ 4 := by
    rw [show (((((n : ℝ) + 1) * Real.pi) / 2) ^ 2) ^ 2
        = ((n : ℝ) + 1) ^ 4 * Real.pi ^ 4 / 16 by ring]
    have h4 : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 4 := by positivity
    nlinarith
  have hstep : ((n : ℝ) + 1) * (((((n : ℝ) + 1) * Real.pi) / 2) ^ 2) ^ 2
      ≤ (99 / 16) * ((n : ℝ) + 1) ^ 5 := by
    nlinarith [hR2, hn1]
  have hpow : ((n : ℝ) + 1) ^ 5 ≤ ((5 / 4) * (n : ℝ)) ^ 5 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hconst : (99 / 16) * (5 / 4 : ℝ) ^ 5 ≤ 32 := by norm_num
  have hfinal : (99 / 16) * ((n : ℝ) + 1) ^ 5 ≤ 32 * (n : ℝ) ^ 5 := by
    have h5 : (0 : ℝ) ≤ (n : ℝ) := by linarith
    have hp : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 5 := by positivity
    have := mul_le_mul_of_nonneg_left hpow (by norm_num : (0:ℝ) ≤ 99/16)
    have hrew : ((5 / 4) * (n : ℝ)) ^ 5 = (5 / 4 : ℝ) ^ 5 * (n : ℝ) ^ 5 := by ring
    rw [hrew] at this
    nlinarith
  calc ((n : ℝ) + 1) * (((((n : ℝ) + 1) * Real.pi) / 2) ^ 2) ^ 2
      ≤ (99 / 16) * ((n : ℝ) + 1) ^ 5 := hstep
    _ ≤ 32 * (n : ℝ) ^ 5 := hfinal
    _ = (2 * (n : ℝ)) ^ 5 := by ring

/-! ## The inverse sum `(B.3)` and the smallest singular value -/

/-- A telescoping bound: `∑_{k<m} 1/(k+1)^2 ≤ 2`.  This is the elementary harmonic-type estimate
behind the Frobenius bound `(B.3)` of the inverse. -/
lemma sum_range_inv_sq_succ_le_two (m : ℕ) :
    (∑ k ∈ Finset.range m, (((k : ℝ) + 1) ^ 2)⁻¹) ≤ 2 := by
  rcases m with _ | m
  · simp
  · rw [Finset.sum_range_succ']
    have hshift : (∑ k ∈ Finset.range m, (((↑(k+1) : ℝ) + 1) ^ 2)⁻¹)
        = ∑ k ∈ Finset.range m, (((k:ℝ) + 2) ^ 2)⁻¹ := by
      apply Finset.sum_congr rfl
      intro k _
      push_cast
      ring_nf
    rw [hshift]
    have hterm : ∀ k ∈ Finset.range m, (((k:ℝ) + 2) ^ 2)⁻¹ ≤ ((k:ℝ)+1)⁻¹ - ((k:ℝ)+2)⁻¹ := by
      intro k _
      have h1 : (0:ℝ) < (k:ℝ) + 1 := by positivity
      have h2 : (0:ℝ) < (k:ℝ) + 2 := by positivity
      have h3 : ((k:ℝ) + 2) ≠ 0 := ne_of_gt h2
      have h4 : ((k:ℝ) + 1) ≠ 0 := ne_of_gt h1
      field_simp
      nlinarith
    have htel : (∑ k ∈ Finset.range m, (((k:ℝ)+1)⁻¹ - ((k:ℝ)+2)⁻¹)) = 1 - ((m:ℝ)+1)⁻¹ := by
      have h := Finset.sum_range_sub (fun k : ℕ => (((k : ℝ) + 1)⁻¹)) m
      have h2 : (∑ k ∈ Finset.range m, (((k:ℝ)+1)⁻¹ - ((k:ℝ)+2)⁻¹))
          = - (∑ k ∈ Finset.range m, (((↑(k+1) : ℝ) + 1)⁻¹ - ((k:ℝ) + 1)⁻¹)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro k _
        push_cast
        ring
      rw [h2, h]
      push_cast
      ring
    have hle := Finset.sum_le_sum hterm
    rw [htel] at hle
    have hpos : (0:ℝ) ≤ ((m:ℝ)+1)⁻¹ := by positivity
    have h0 : (((↑(0:ℕ) : ℝ) + 1) ^ 2)⁻¹ = 1 := by norm_num
    rw [h0]
    linarith

/-- **The distance sum `(B.3)`.**  The squared inverse distances to the centre sum to at most
`4`, which is the two-sided version of `∑_{k≥1} 1/k² ≤ 2`. -/
lemma sum_inv_sq_erase_center_le (n : ℕ) :
    (∑ i ∈ Finset.univ.erase (center n), (((i : ℝ) - (center n : ℝ)) ^ 2)⁻¹) ≤ 4 := by
  have hzero : (((center n : ℝ) - (center n : ℝ)) ^ 2)⁻¹ = 0 := by norm_num
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), hzero, sub_zero]
  have hconv : (∑ i : Fin (n+1), (((i : ℝ) - (center n : ℝ)) ^ 2)⁻¹)
      = ∑ i ∈ Finset.range (n+1), ((((i:ℕ) : ℝ) - ((n/2 : ℕ) : ℝ)) ^ 2)⁻¹ := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (((i : ℝ) - (center n : ℝ)) ^ 2)⁻¹) (n+1)]
    simp [center]
  rw [hconv]
  set c := n / 2 with hcdef
  have hcn : c ≤ n := Nat.div_le_self n 2
  have hsplit : n + 1 = c + (n + 1 - c) := by omega
  rw [hsplit, Finset.sum_range_add]
  have hA : (∑ i ∈ Finset.range c, ((((i : ℝ) - (c : ℝ)) ^ 2)⁻¹))
      = ∑ k ∈ Finset.range c, ((((k : ℝ) + 1) ^ 2)⁻¹) := by
    have h := Finset.sum_range_reflect (fun j : ℕ => ((((c : ℝ) - (j : ℝ)) ^ 2)⁻¹)) c
    have hL : (∑ i ∈ Finset.range c, ((((i : ℝ) - (c : ℝ)) ^ 2)⁻¹))
        = ∑ i ∈ Finset.range c, ((((c : ℝ) - (i : ℝ)) ^ 2)⁻¹) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show ((i:ℝ) - (c:ℝ)) = -((c:ℝ) - (i:ℝ)) by ring, neg_sq]
    rw [hL, ← h]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < c := Finset.mem_range.mp hj
    have hcast : ((c - 1 - j : ℕ) : ℝ) = (c:ℝ) - 1 - (j:ℝ) := by
      rw [Nat.cast_sub (by omega : j ≤ c - 1), Nat.cast_sub (by omega : 1 ≤ c)]
      push_cast
      ring
    rw [hcast]
    ring_nf
  have hB : (∑ k ∈ Finset.range (n + 1 - c), (((↑(c + k) : ℝ) - (c:ℝ)) ^ 2)⁻¹)
      = ∑ k ∈ Finset.range (n - c), ((((k:ℝ) + 1) ^ 2)⁻¹) := by
    have h1 : n + 1 - c = (n - c) + 1 := by omega
    rw [h1, Finset.sum_range_succ']
    have hz : (((↑(c + 0) : ℝ) - (c:ℝ)) ^ 2)⁻¹ = 0 := by norm_num
    rw [hz, add_zero]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring_nf
  rw [hA, hB]
  have h1 := sum_range_inv_sq_succ_le_two c
  have h2 := sum_range_inv_sq_succ_le_two (n - c)
  linarith

/-- The square of an off-centre inverse entry, in terms of the inverse distance. -/
lemma inv_entry_sq_le (n : ℕ) {j : Fin (n + 1)} (hj : j ≠ center n) :
    (((((j : ℝ) - (center n : ℝ)) * Real.pi) ^ 2)⁻¹) ^ 2
      ≤ (Real.pi ^ 4)⁻¹ * (((j : ℝ) - (center n : ℝ)) ^ 2)⁻¹ := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hx2 : (1 : ℝ) ≤ ((j : ℝ) - (center n : ℝ)) ^ 2 := by
    have hz : ((j : ℤ) - ((center n : ℕ) : ℤ)) ≠ 0 := by
      intro h
      apply hj
      have : (j : ℕ) = (center n : ℕ) := by omega
      exact Fin.ext this
    have habs : (1 : ℝ) ≤ |(j : ℝ) - (center n : ℝ)| := by
      have hcast : |(j : ℝ) - (center n : ℝ)|
          = |(((j : ℤ) - ((center n : ℕ) : ℤ) : ℤ) : ℝ)| := by
        push_cast
        ring_nf
      rw [hcast]
      have h1 : (1 : ℤ) ≤ |((j : ℤ) - ((center n : ℕ) : ℤ))| := Int.one_le_abs hz
      exact_mod_cast h1
    rw [← sq_abs ((j : ℝ) - (center n : ℝ))]
    simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) habs 2
  have hxpos : (0 : ℝ) < ((j : ℝ) - (center n : ℝ)) ^ 2 := by nlinarith
  have hp4 : (0 : ℝ) < Real.pi ^ 4 := by positivity
  have h : ((j : ℝ) - (center n : ℝ)) ^ 2 ≤ ((j : ℝ) - (center n : ℝ)) ^ 4 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ ((j:ℝ) - (center n:ℝ))^2)
      (by linarith : (0:ℝ) ≤ ((j:ℝ) - (center n:ℝ))^2 - 1)]
  have key : (1:ℝ)/((((j : ℝ) - (center n : ℝ)) ^ 2) ^ 2 * Real.pi^4)
      ≤ 1/(((j : ℝ) - (center n : ℝ)) ^ 2 * Real.pi^4) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [h]
  have hl : (((((j : ℝ) - (center n : ℝ)) * Real.pi) ^ 2)⁻¹) ^ 2
      = (1:ℝ)/((((j : ℝ) - (center n : ℝ)) ^ 2) ^ 2 * Real.pi^4) := by
    field_simp
  have hr : (Real.pi ^ 4)⁻¹ * (((j : ℝ) - (center n : ℝ)) ^ 2)⁻¹
      = (1:ℝ)/(((j : ℝ) - (center n : ℝ)) ^ 2 * Real.pi^4) := by
    field_simp
  rw [hl, hr]
  exact key

/-- The `⌊n/2⌋`-th row of the inverse, squared: the centre entry contributes `1` and every other
entry contributes the squared inverse distance. -/
lemma row_sq_center (n : ℕ) :
    (∑ j, (periodicSecondDerivativeInv n (center n) j) ^ 2)
      = 1 + ∑ j ∈ Finset.univ.erase (center n),
          (((((j : ℝ) - (center n : ℝ)) * Real.pi) ^ 2)⁻¹) ^ 2 := by
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ (center n))]
  rw [Finset.erase_eq]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro j hj
    rw [periodicSecondDerivativeInv_center_off (by simpa using (Finset.mem_sdiff.mp hj).2)]

/-- An off-centre row of the inverse, squared: only the diagonal entry survives. -/
lemma row_sq_off (n : ℕ) {i : Fin (n + 1)} (hi : i ≠ center n) :
    (∑ j, (periodicSecondDerivativeInv n i j) ^ 2)
      = (((((i : ℝ) - (center n : ℝ)) * Real.pi) ^ 2)⁻¹) ^ 2 := by
  rw [Finset.sum_eq_single i]
  · rw [periodicSecondDerivativeInv_off_diag hi]
    ring
  · intro a _ hai
    rw [periodicSecondDerivativeInv_off_off hi (Ne.symm hai), zero_pow (by norm_num : (2:ℕ) ≠ 0)]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **The entrywise square sum of `D⁻¹` (`(B.3)`).**  The two nonzero diagonals contribute twice
the same sum of fourth powers. -/
lemma sum_sq_entries (n : ℕ) :
    (∑ i, ∑ j, (periodicSecondDerivativeInv n i j) ^ 2)
      = 1 + 2 * ∑ j ∈ Finset.univ.erase (center n),
          (((((j : ℝ) - (center n : ℝ)) * Real.pi) ^ 2)⁻¹) ^ 2 := by
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ (center n)),
      Finset.erase_eq]
  rw [row_sq_center]
  simp only [Finset.erase_eq]
  have hoff : (∑ i ∈ Finset.univ \ {center n},
        (∑ j, (periodicSecondDerivativeInv n i j) ^ 2))
      = ∑ i ∈ Finset.univ \ {center n},
          (((((i : ℝ) - (center n : ℝ)) * Real.pi) ^ 2)⁻¹) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    exact row_sq_off n (by simpa using (Finset.mem_sdiff.mp hi).2)
  rw [hoff]
  ring

/-- **The Frobenius bound `(B.3)`.**  The sum of the squares of the entries of `D⁻¹` is at most
`2`; the source proves `1 + 2ζ(4)/π⁴ ≤ 2`, and the harmonic-type bound `∑ 1/k² ≤ 2` suffices. -/
lemma sum_sq_entries_le_two (n : ℕ) :
    (∑ i, ∑ j, (periodicSecondDerivativeInv n i j) ^ 2) ≤ 2 := by
  rw [sum_sq_entries]
  have hstep : (∑ j ∈ Finset.univ.erase (center n),
        (((((j : ℝ) - (center n : ℝ)) * Real.pi) ^ 2)⁻¹) ^ 2)
      ≤ (Real.pi ^ 4)⁻¹ * ∑ j ∈ Finset.univ.erase (center n),
          (((j : ℝ) - (center n : ℝ)) ^ 2)⁻¹ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j hj =>
      inv_entry_sq_le n (by simpa using (Finset.mem_erase.mp hj).1))
  have hS := sum_inv_sq_erase_center_le n
  have hpi4 : (81 : ℝ) ≤ Real.pi ^ 4 := by
    have h3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3) h3.le 4
    norm_num at h
    linarith
  have hpi4pos : (0 : ℝ) < Real.pi ^ 4 := by positivity
  have h4 : (Real.pi ^ 4)⁻¹ * 4 ≤ 1/2 := by
    rw [inv_mul_le_iff₀ hpi4pos]
    linarith
  have hmid : (Real.pi ^ 4)⁻¹ * (∑ j ∈ Finset.univ.erase (center n),
          (((j : ℝ) - (center n : ℝ)) ^ 2)⁻¹) ≤ 1/2 := by
    calc (Real.pi ^ 4)⁻¹ * (∑ j ∈ Finset.univ.erase (center n),
          (((j : ℝ) - (center n : ℝ)) ^ 2)⁻¹)
        ≤ (Real.pi ^ 4)⁻¹ * 4 := by
          exact mul_le_mul_of_nonneg_left hS (by positivity)
      _ ≤ 1/2 := h4
  linarith

/-- **The inverse norm bound `(B.4)`.**  `‖(D_n^(2))⁻¹‖ ≤ √2`, i.e. the smallest singular value of
`D_n^(2)` is at least `1/√2`. -/
theorem periodicSecondDerivativeInv_opNorm_le (n : ℕ) :
    ‖periodicSecondDerivativeInv n‖ ≤ Real.sqrt 2 := by
  refine opNorm_le_of_sum_sq (C := Real.sqrt 2) (by positivity) ?_
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  exact sum_sq_entries_le_two n

/-- **Lemma 7, second bound (`(4.61)`, `(B.4)`).**  For every vector `x`, the second-derivative
matrix of `(4.59)` stretches `x` by at least `1/√2`: `‖x‖ ≤ √2 ‖D_n^(2) x‖`.  This is the
statement that the smallest singular value of `D_n^(2)` is at least `1/√2`, in operator-norm
form. -/
theorem lemma7_sigmaMin (n : ℕ) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    ‖x‖ ≤ Real.sqrt 2 *
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (periodicSecondDerivative n) x‖ := by
  have hcomp : Matrix.toEuclideanCLM (𝕜 := ℝ) (periodicSecondDerivativeInv n)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (periodicSecondDerivative n) x) = x := by
    have hm : Matrix.toEuclideanCLM (𝕜 := ℝ)
          (periodicSecondDerivativeInv n * periodicSecondDerivative n)
        = Matrix.toEuclideanCLM (𝕜 := ℝ) (periodicSecondDerivativeInv n) *
          Matrix.toEuclideanCLM (𝕜 := ℝ) (periodicSecondDerivative n) := map_mul _ _ _
    rw [periodicSecondDerivative_inv_mul, map_one] at hm
    rw [← ContinuousLinearMap.mul_apply, ← hm, ContinuousLinearMap.one_apply]
  have h := periodicSecondDerivativeInv_opNorm_le n
  calc ‖x‖ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (periodicSecondDerivativeInv n)
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (periodicSecondDerivative n) x)‖ := by rw [hcomp]
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (periodicSecondDerivativeInv n)‖ *
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (periodicSecondDerivative n) x‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ Real.sqrt 2 * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (periodicSecondDerivative n) x‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rwa [Matrix.l2_opNorm_toEuclideanCLM]

end Qatlib.Papers.QuantumPDE20.MainResults
