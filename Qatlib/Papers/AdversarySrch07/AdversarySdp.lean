/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdversarySrch07.MainResults.OptimalBound.SpectralBound
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Even-size ordered-search SDP certificates

Constructs the real outer-product dual matrix `outerVec (uEven m)` for the ordered-search
semidefinite formulation in [ChildsLee2008]. Its upper diagonal sums are at least one and its
trace equals the objective of the explicit even-size primal weights.

For positive `m`, `sdp_certificate_even` assembles nonnegative primal weights, the Toeplitz norm
bound, positive semidefiniteness and diagonal-sum constraints for the dual matrix, and the
matching trace identities.

## Main statements

* `dual_feasible_even`: Verifies the outer-product dual constraints and trace value.
* `trace_dual_eq_objective`: Matches the dual trace to the explicit primal objective.
* `sdp_certificate_even`: Collects the even-size primal and dual certificate properties.

## References

* [Childs and Lee, 2008][ChildsLee2008]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators ENNReal Matrix.Norms.L2Operator
open Finset Matrix

namespace Qatlib.Papers.AdversarySrch07.AdversarySdp

open Qatlib.Papers.AdversarySrch07.MainResults
open Qatlib.Papers.AdversarySrch07.MainResults.XiSequence
open Qatlib.Papers.AdversarySrch07.MainResults.OptimalBound

/-- The sum of the `i`th upper diagonal of a real matrix, indexed by positions `(j, j + i)`. See
[ChildsLee2008]. -/
def diagSum {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (i : ℕ) : ℝ :=
  ∑ j : Fin (n - i), P ⟨j.val, by omega⟩ ⟨j.val + i, by omega⟩

/-- The real outer-product matrix with entries `u i * u j`. -/
def outerVec {n : ℕ} (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.vecMulVec u u

/-- The `i`th upper diagonal sum of `outerVec u` is the sum of products `u j * u (j + i)` over
the valid indices. -/
theorem diagSum_outerVec {n : ℕ} (u : Fin n → ℝ) (i : ℕ) :
    diagSum (outerVec u) i =
      ∑ j : Fin (n - i), u ⟨j.val, by omega⟩ * u ⟨j.val + i, by omega⟩ := by
  simp [diagSum, outerVec, Matrix.vecMulVec_apply]

/-- The vector `uEven m` is invariant under reversal of its `2 * m` indices. -/
theorem uEven_symm (m : ℕ) (k : Fin (2 * m)) :
    uEven m k = uEven m ⟨2 * m - 1 - k.val, by omega⟩ := by
  unfold uEven
  by_cases hk : k.val < m
  · rw [if_pos hk, if_neg (by omega : ¬ 2 * m - 1 - k.val < m)]
    rw [show 2 * m - 1 - (2 * m - 1 - k.val) = k.val by omega]
  · rw [if_neg hk, if_pos (by omega : 2 * m - 1 - k.val < m)]

/-- The sequence `xi` is nonincreasing between any two ordered natural indices. -/
theorem xi_antitone_le {a b : ℕ} (h : a ≤ b) : xi b ≤ xi a := by
  induction b with
  | zero => rw [Nat.le_zero.mp h]
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hlt
    · exact le_rfl
    · exact (xi_antitone k).trans (ih (Nat.lt_succ_iff.mp hlt))

/-- Each coordinate of `uEven m` is at least `xi` at the same index. -/
theorem xi_le_uEven (m : ℕ) (k : Fin (2 * m)) : xi k.val ≤ uEven m k := by
  unfold uEven
  by_cases hk : k.val < m
  · rw [if_pos hk]
  · rw [if_neg hk]
    exact xi_antitone_le (by omega)

/-- The natural-indexed extension of the reflected sequence used to define `uEven m`. -/
def uVal (m i : ℕ) : ℝ := if i < m then xi i else xi (2 * m - 1 - i)

/-- The finite-indexed value `uEven m k` equals `uVal m k.val`. -/
theorem uEven_eq_uVal (m : ℕ) (k : Fin (2 * m)) : uEven m k = uVal m k.val := rfl

/-- The squared Euclidean length of `uEven m` equals twice the sum of `xi i ^ 2` for `i < m`. -/
theorem sum_uEven_sq (m : ℕ) :
    ∑ k : Fin (2 * m), uEven m k ^ 2 = 2 * ∑ i ∈ Finset.range m, xi i ^ 2 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rw [show (∑ k : Fin (2 * m), uEven m k ^ 2) = ∑ k : Fin (2 * m), uVal m k.val ^ 2 from by
    apply Finset.sum_congr rfl; intro k _; rw [uEven_eq_uVal]]
  rw [Fin.sum_univ_eq_sum_range (fun i => uVal m i ^ 2)]
  have hsplit : (∑ i ∈ Finset.range (2 * m), uVal m i ^ 2) =
      (∑ i ∈ Finset.range m, uVal m i ^ 2) +
        ∑ i ∈ Finset.Ico m (2 * m), uVal m i ^ 2 := by
    rw [Finset.sum_range_add_sum_Ico _ (by omega)]
  rw [hsplit]
  have hlow : (∑ i ∈ Finset.range m, uVal m i ^ 2) =
      ∑ i ∈ Finset.range m, xi i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    rw [uVal, if_pos him]
  have hhigh : (∑ i ∈ Finset.Ico m (2 * m), uVal m i ^ 2) =
      ∑ i ∈ Finset.range m, xi i ^ 2 := by
    have hstep : (∑ i ∈ Finset.Ico m (2 * m), uVal m i ^ 2) =
        ∑ i ∈ Finset.Ico m (2 * m), xi (2 * m - 1 - i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      have him : ¬ i < m := by have := (Finset.mem_Ico.mp hi).1; omega
      rw [uVal, if_neg him]
    rw [hstep]
    have hreflect := Finset.sum_Ico_reflect
      (fun j => xi j ^ 2) m (m := 2 * m) (n := 2 * m - 1) (by omega)
    rw [show 2 * m - 1 + 1 - (2 * m) = 0 by omega,
      show 2 * m - 1 + 1 - m = m by omega, Nat.Ico_zero_eq_range] at hreflect
    exact hreflect
  rw [hlow, hhigh]; ring

/-- The outer-product matrix of a real vector with itself is positive semidefinite. -/
theorem posSemidef_outerVec {n : ℕ} (u : Fin n → ℝ) : (outerVec u).PosSemidef := by
  simpa [outerVec] using! Matrix.posSemidef_vecMulVec_self_star (R := ℝ) u

/-- The trace of `outerVec u` equals the sum of the squares of the coordinates of `u`. -/
theorem trace_outerVec {n : ℕ} (u : Fin n → ℝ) :
    (outerVec u).trace = ∑ k : Fin n, u k ^ 2 := by
  simp [Matrix.trace, outerVec, Matrix.vecMulVec_apply, sq]

/-- The even dual outer-product matrix has trace `2 * ∑ i < m, xi i ^ 2`. -/
theorem trace_dual_even (m : ℕ) :
    (outerVec (uEven m)).trace = 2 * ∑ i ∈ Finset.range m, xi i ^ 2 := by
  rw [trace_outerVec, sum_uEven_sq]

/-- The trace of the even dual outer-product matrix equals the objective of `gammaEven m` at
size `2 * m`. -/
theorem trace_dual_eq_objective (m : ℕ) :
    (outerVec (uEven m)).trace = objective (2 * m) (gammaEven m) := by
  rw [trace_dual_even, objective_gammaEven, AM_zero]

/-- For every `i < 2 * m`, the `i`th upper diagonal sum of the even dual matrix is at least one. -/
theorem diagSum_outerVec_ge_one (m : ℕ) (i : ℕ) (hi : i < 2 * m) :
    1 ≤ diagSum (outerVec (uEven m)) i := by
  rw [diagSum_outerVec]

  have hterm : ∀ j : Fin (2 * m - i),
      xi j.val * xi (2 * m - 1 - i - j.val) ≤
        uEven m ⟨j.val, by omega⟩ * uEven m ⟨j.val + i, by omega⟩ := by
    intro j
    have hj : j.val < 2 * m - i := j.isLt
    have h1 : xi j.val ≤ uEven m ⟨j.val, by omega⟩ := xi_le_uEven m ⟨j.val, by omega⟩
    have h2 : xi (2 * m - 1 - i - j.val) ≤ uEven m ⟨j.val + i, by omega⟩ := by
      unfold uEven
      by_cases hc : j.val + i < m
      · rw [if_pos hc]
        exact xi_antitone_le (a := j.val + i) (b := 2 * m - 1 - i - j.val) (by omega)
      · rw [if_neg hc]
        rw [show 2 * m - 1 - (j.val + i) = 2 * m - 1 - i - j.val by omega]
    have hnn : 0 ≤ xi (2 * m - 1 - i - j.val) := le_of_lt (xi_pos _)
    exact mul_le_mul h1 h2 hnn (le_of_lt (uEven_pos m ⟨j.val, by omega⟩))

  have hconv : (∑ j : Fin (2 * m - i), xi j.val * xi (2 * m - 1 - i - j.val)) = 1 := by
    rw [Finset.sum_fin_eq_sum_range]
    have hsimp : ∀ j ∈ Finset.range (2 * m - i),
        (if h : j < 2 * m - i then xi j * xi (2 * m - 1 - i - j) else 0) =
          xi j * xi (2 * m - 1 - i - j) := by
      intro j hj; rw [dif_pos (Finset.mem_range.mp hj)]
    rw [Finset.sum_congr rfl hsimp]
    have h := source_proposition_four (2 * m - 1 - i)
    rw [show 2 * m - 1 - i + 1 = 2 * m - i by omega] at h
    exact h
  calc (1 : ℝ) = ∑ j : Fin (2 * m - i), xi j.val * xi (2 * m - 1 - i - j.val) :=
        hconv.symm
    _ ≤ ∑ j : Fin (2 * m - i),
          uEven m ⟨j.val, by omega⟩ * uEven m ⟨j.val + i, by omega⟩ :=
        Finset.sum_le_sum (fun j _ => hterm j)

/-- The even dual outer-product matrix is positive semidefinite, has every valid upper diagonal
sum at least one, and has trace twice the first `m` squared `xi` values. See
[ChildsLee2008]. -/
theorem dual_feasible_even (m : ℕ) :
    (outerVec (uEven m)).PosSemidef ∧
      (∀ i < 2 * m, 1 ≤ diagSum (outerVec (uEven m)) i) ∧
      (outerVec (uEven m)).trace = 2 * ∑ i ∈ Finset.range m, xi i ^ 2 :=
  ⟨posSemidef_outerVec _, fun i hi => diagSum_outerVec_ge_one m i hi, trace_dual_even m⟩

/-- The trace of the product of the even Toeplitz matrix and its dual outer-product matrix
equals the even primal objective. See [ChildsLee2008]. -/
theorem trace_toeplitz_mul_outerVec (m : ℕ) :
    (toeplitz (2 * m) (gammaEven m) * outerVec (uEven m)).trace =
      objective (2 * m) (gammaEven m) := by
  unfold outerVec
  rw [Matrix.mul_vecMulVec, toeplitz_mulVec_uEven, Matrix.trace_vecMulVec]
  rw [dotProduct]
  have hsq : ∑ i : Fin (2 * m), uEven m i * uEven m i =
      ∑ i : Fin (2 * m), uEven m i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsq, sum_uEven_sq, objective_gammaEven, AM_zero]

/-- The trace of the even Toeplitz matrix times the dual outer-product matrix equals the trace
of the dual matrix. -/
theorem trace_toeplitz_mul_outerVec_eq_trace (m : ℕ) :
    (toeplitz (2 * m) (gammaEven m) * outerVec (uEven m)).trace =
      (outerVec (uEven m)).trace := by
  rw [trace_toeplitz_mul_outerVec, trace_dual_eq_objective]

/-- For `m > 0`, collects nonnegative even weights, the Toeplitz operator-norm bound, positive
semidefiniteness and diagonal-sum feasibility of the dual matrix, and the matching objective
and product-trace identities. See [ChildsLee2008]. -/
theorem sdp_certificate_even (m : ℕ) (hm : 0 < m) :
    (∀ i, 0 ≤ gammaEven m i) ∧
      ‖(toeplitz (2 * m) (gammaEven m) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ)‖ ≤ 1 ∧
      (outerVec (uEven m)).PosSemidef ∧
      (∀ i < 2 * m, 1 ≤ diagSum (outerVec (uEven m)) i) ∧
      (outerVec (uEven m)).trace = objective (2 * m) (gammaEven m) ∧
      (toeplitz (2 * m) (gammaEven m) * outerVec (uEven m)).trace =
        (outerVec (uEven m)).trace :=
  ⟨gammaEven_nonneg m, by
      rw [toeplitz_l2_opNorm_eq_one m hm], posSemidef_outerVec _,
    fun i hi => diagSum_outerVec_ge_one m i hi, trace_dual_eq_objective m,
    trace_toeplitz_mul_outerVec_eq_trace m⟩

end Qatlib.Papers.AdversarySrch07.AdversarySdp
