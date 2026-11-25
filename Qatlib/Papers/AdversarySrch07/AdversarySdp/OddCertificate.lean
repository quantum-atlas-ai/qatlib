/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdversarySrch07.AdversarySdp
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-!
# Odd-size ordered-search SDP certificate

Builds the explicit odd-size primal weights `gammaOdd m` and the reflected vector `uOdd m` for
the ordered-search semidefinite formulation of [ChildsLee2008]. The central identity
`toeplitz_mulVec_uOdd` shows that the odd Toeplitz weight matrix fixes `uOdd m`; it is obtained
by averaging the two even-size correlation identities at sizes `m` and `m + 1`.

From this identity the module derives the operator-norm bound, the diagonal-sum constraints of
the outer-product dual matrix, and the matching primal and dual objective values. The resulting
`source_theorem_one_odd_certificate` collects primal feasibility, dual feasibility and the
pairing identity for odd `n = 2 * m + 1`.

The certificate does not formalize the external reduction from the adversary value to the
value of the semidefinite program, general strong duality, or the negative-weight programs
`(P±)` and `(D±)`.

## Main statements

* `toeplitz_mulVec_uOdd`: the odd Toeplitz matrix fixes the reflected vector `uOdd m`.
* `toeplitz_gammaOdd_l2_opNorm_le_one`: the odd primal operator-norm constraint holds.
* `diagSum_outerVec_uOdd_ge_one`: every valid upper diagonal sum of the dual matrix is at
  least one.
* `source_theorem_one_odd_certificate`: the odd-size primal and dual certificate.

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
open Qatlib.Papers.AdversarySrch07.AdversarySdp

/-- The odd weights are the average of the two adjacent even weight sequences. See
[ChildsLee2008], Theorem 1. -/
theorem gammaOdd_eq_average (m i : ℕ) :
    gammaOdd m i = (gammaEven m i + gammaEven (m + 1) i) / 2 := by
  unfold gammaOdd gammaEven
  ring

/-- Every coordinate of the reflected odd vector is strictly positive. -/
theorem uOdd_pos (m : ℕ) (i : Fin (2 * m + 1)) : 0 < uOdd m i := by
  unfold uOdd
  split_ifs with h
  · exact xi_pos _
  · exact xi_pos _

/-- Each coordinate of `uOdd m` is at least the corresponding term of `xi`. -/
theorem xi_le_uOdd (m : ℕ) (k : Fin (2 * m + 1)) : xi k.val ≤ uOdd m k := by
  unfold uOdd
  by_cases hk : k.val ≤ m
  · rw [ite_eq_left hk]
  · rw [ite_eq_right hk]
    exact xi_antitone_le (a := 2 * m - k.val) (b := k.val) (by omega)

/-- The natural-indexed reflection of the odd vector is invariant under reversal. -/
private theorem oddVec_symm (m q : ℕ) (hq : q ≤ 2 * m) :
    (if q ≤ m then xi q else xi (2 * m - q)) =
      (if 2 * m - q ≤ m then xi (2 * m - q) else xi (2 * m - (2 * m - q))) := by
  rcases lt_trichotomy q m with hlt | heq | hgt
  · rw [ite_eq_left (by omega), ite_eq_right (by omega),
      show 2 * m - (2 * m - q) = q by omega]
  · rw [heq, ite_eq_left (by omega), ite_eq_left (by omega),
      show 2 * m - m = m by omega]
  · rw [ite_eq_right (by omega), ite_eq_left (by omega)]

/-- The reflected odd vector is invariant under reversal of its `2 * m + 1` indices. -/
theorem uOdd_symm (m : ℕ) (k : Fin (2 * m + 1)) :
    uOdd m k = uOdd m ⟨2 * m - k.val, by omega⟩ := by
  simp only [uOdd]
  exact oddVec_symm m k.val (by omega)

/-- The squared Euclidean length of `uOdd m` equals `xi m ^ 2` plus twice the sum of
`xi i ^ 2` for `i < m`. -/
theorem sum_uOdd_sq (m : ℕ) :
    ∑ k : Fin (2 * m + 1), uOdd m k ^ 2 =
      xi m ^ 2 + 2 * ∑ i ∈ Finset.range m, xi i ^ 2 := by
  have hcongr : ∀ k : Fin (2 * m + 1), uOdd m k ^ 2 =
      (if k.val ≤ m then xi k.val else xi (2 * m - k.val)) ^ 2 := by
    intro k; simp [uOdd]
  rw [Finset.sum_congr rfl (fun k _ => hcongr k)]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (if i ≤ m then xi i else xi (2 * m - i)) ^ 2)]
  rw [← Finset.sum_range_add_sum_Ico _ (by omega : m + 1 ≤ 2 * m + 1)]
  have hlow : (∑ i ∈ Finset.range (m + 1),
      (if i ≤ m then xi i else xi (2 * m - i)) ^ 2) =
      ∑ i ∈ Finset.range m, xi i ^ 2 + xi m ^ 2 := by
    rw [Finset.sum_range_succ]
    have : ∀ i ∈ Finset.range m, (if i ≤ m then xi i else xi (2 * m - i)) ^ 2 = xi i ^ 2 := by
      intro i hi
      rw [ite_eq_left (by have := Finset.mem_range.mp hi; omega)]
    rw [Finset.sum_congr rfl this, ite_eq_left (by omega : m ≤ m)]
  have hhigh : (∑ i ∈ Finset.Ico (m + 1) (2 * m + 1),
      (if i ≤ m then xi i else xi (2 * m - i)) ^ 2) =
      ∑ i ∈ Finset.range m, xi i ^ 2 := by
    have hstep : (∑ i ∈ Finset.Ico (m + 1) (2 * m + 1),
        (if i ≤ m then xi i else xi (2 * m - i)) ^ 2) =
        ∑ i ∈ Finset.Ico (m + 1) (2 * m + 1), xi (2 * m - i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ite_eq_right (by have := (Finset.mem_Ico.mp hi).1; omega)]
    rw [hstep]
    have hreflect := Finset.sum_Ico_reflect (fun j => xi j ^ 2) (m + 1) (m := 2 * m + 1)
      (n := 2 * m) (by omega)
    rw [show 2 * m + 1 - (2 * m + 1) = 0 by omega,
      show 2 * m + 1 - (m + 1) = m by omega, Nat.Ico_zero_eq_range] at hreflect
    exact hreflect
  rw [hlow, hhigh]
  ring

/-- The `q`th summand of the row `p` of the odd Toeplitz matrix applied to the reflected
vector, written over natural indices. -/
private def oddRowTerm (m p q : ℕ) : ℝ :=
  gammaOdd m (2 * m + 1 - Int.natAbs ((p : ℤ) - (q : ℤ))) *
    (if q ≤ m then xi q else xi (2 * m - q))

/-- For `p < m`, the `gammaEven m` part of the odd row sum equals `xi p`. See
[ChildsLee2008], Theorem 1. -/
private theorem sum_gammaEven_odd_row (m p : ℕ) (hp : p < m) :
    ∑ q ∈ Finset.range (2 * m + 1),
        gammaEven m (2 * m + 1 - Int.natAbs ((p : ℤ) - (q : ℤ))) *
          (if q ≤ m then xi q else xi (2 * m - q)) = xi p := by
  have hsub : Finset.Ico (p + m + 1) (2 * m + 1) ⊆ Finset.range (2 * m + 1) := by
    intro x hx
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hx).2
  have hzero : ∀ q ∈ Finset.range (2 * m + 1), q ∉ Finset.Ico (p + m + 1) (2 * m + 1) →
      gammaEven m (2 * m + 1 - Int.natAbs ((p : ℤ) - (q : ℤ))) *
        (if q ≤ m then xi q else xi (2 * m - q)) = 0 := by
    intro q hq hqnot
    have hq2 : q < 2 * m + 1 := Finset.mem_range.mp hq
    have hqlt : q < p + m + 1 := by
      by_contra h
      exact hqnot (Finset.mem_Ico.mpr ⟨by omega, hq2⟩)
    have hd : Int.natAbs ((p : ℤ) - (q : ℤ)) ≤ m := by
      by_cases hqp : q ≤ p
      · rw [Int.natAbs_natCast_sub_natCast_of_ge (by omega : q ≤ p)]
        omega
      · rw [Int.natAbs_natCast_sub_natCast_of_le (by omega : p ≤ q)]
        omega
    have hk : m < 2 * m + 1 - Int.natAbs ((p : ℤ) - (q : ℤ)) := by omega
    rw [gammaEven_eq_zero_of_lt hk, zero_mul]
  have hterm : ∀ q ∈ Finset.Ico (p + m + 1) (2 * m + 1),
      gammaEven m (2 * m + 1 - Int.natAbs ((p : ℤ) - (q : ℤ))) *
        (if q ≤ m then xi q else xi (2 * m - q)) =
      (fun j => gammaEven m (j + p + 1) * xi j) (2 * m - q) := by
    intro q hq
    have hq1 : p + m + 1 ≤ q := (Finset.mem_Ico.mp hq).1
    have hq2 : q < 2 * m + 1 := (Finset.mem_Ico.mp hq).2
    rw [ite_eq_right (by omega : ¬ q ≤ m),
      Int.natAbs_natCast_sub_natCast_of_le (by omega : p ≤ q)]
    show gammaEven m (2 * m + 1 - (q - p)) * xi (2 * m - q) =
      gammaEven m ((2 * m - q) + p + 1) * xi (2 * m - q)
    rw [show 2 * m + 1 - (q - p) = (2 * m - q) + p + 1 by omega]
  calc ∑ q ∈ Finset.range (2 * m + 1),
        gammaEven m (2 * m + 1 - Int.natAbs ((p : ℤ) - (q : ℤ))) *
          (if q ≤ m then xi q else xi (2 * m - q))
      = ∑ q ∈ Finset.Ico (p + m + 1) (2 * m + 1),
          gammaEven m (2 * m + 1 - Int.natAbs ((p : ℤ) - (q : ℤ))) *
            (if q ≤ m then xi q else xi (2 * m - q)) :=
        (Finset.sum_subset hsub hzero).symm
    _ = ∑ q ∈ Finset.Ico (p + m + 1) (2 * m + 1),
          (fun j => gammaEven m (j + p + 1) * xi j) (2 * m - q) :=
        Finset.sum_congr rfl hterm
    _ = ∑ j ∈ Finset.Ico (2 * m + 1 - (2 * m + 1)) (2 * m + 1 - (p + m + 1)),
          gammaEven m (j + p + 1) * xi j :=
        Finset.sum_Ico_reflect (fun j => gammaEven m (j + p + 1) * xi j) (p + m + 1)
          (m := 2 * m + 1) (n := 2 * m) (by omega)
    _ = xi p := by
        rw [show 2 * m + 1 - (2 * m + 1) = 0 by omega,
          show 2 * m + 1 - (p + m + 1) = m - p by omega, Nat.Ico_zero_eq_range]
        simpa [gammaEven_apply_succ] using eigen_identity m p hp

/-- For `p < m`, the `gammaEven (m + 1)` part of the odd row sum equals `xi p`. See
[ChildsLee2008], Theorem 1. -/
private theorem sum_gammaEven_succ_odd_row (m p : ℕ) (hp : p < m) :
    ∑ q ∈ Finset.range (2 * m + 1),
        gammaEven (m + 1) (2 * m + 1 - Int.natAbs ((p : ℤ) - (q : ℤ))) *
          (if q ≤ m then xi q else xi (2 * m - q)) = xi p := by
  have hsub : Finset.Ico (p + m) (2 * m + 1) ⊆ Finset.range (2 * m + 1) := by
    intro x hx
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hx).2
  have hzero : ∀ q ∈ Finset.range (2 * m + 1), q ∉ Finset.Ico (p + m) (2 * m + 1) →
      gammaEven (m + 1) (2 * m + 1 - Int.natAbs ((p : ℤ) - (q : ℤ))) *
        (if q ≤ m then xi q else xi (2 * m - q)) = 0 := by
    intro q hq hqnot
    have hq2 : q < 2 * m + 1 := Finset.mem_range.mp hq
    have hqlt : q < p + m := by
      by_contra h
      exact hqnot (Finset.mem_Ico.mpr ⟨by omega, hq2⟩)
    have hd : Int.natAbs ((p : ℤ) - (q : ℤ)) ≤ m - 1 := by
      by_cases hqp : q ≤ p
      · rw [Int.natAbs_natCast_sub_natCast_of_ge (by omega : q ≤ p)]
        omega
      · rw [Int.natAbs_natCast_sub_natCast_of_le (by omega : p ≤ q)]
        omega
    have hk : m + 1 < 2 * m + 1 - Int.natAbs ((p : ℤ) - (q : ℤ)) := by omega
    rw [gammaEven_eq_zero_of_lt hk, zero_mul]
  have hterm : ∀ q ∈ Finset.Ico (p + m) (2 * m + 1),
      gammaEven (m + 1) (2 * m + 1 - Int.natAbs ((p : ℤ) - (q : ℤ))) *
        (if q ≤ m then xi q else xi (2 * m - q)) =
      (fun j => gammaEven (m + 1) (j + p + 1) * xi j) (2 * m - q) := by
    intro q hq
    have hq1 : p + m ≤ q := (Finset.mem_Ico.mp hq).1
    have hq2 : q < 2 * m + 1 := (Finset.mem_Ico.mp hq).2
    rw [Int.natAbs_natCast_sub_natCast_of_le (by omega : p ≤ q)]
    show gammaEven (m + 1) (2 * m + 1 - (q - p)) * (if q ≤ m then xi q else xi (2 * m - q)) =
      gammaEven (m + 1) ((2 * m - q) + p + 1) * xi (2 * m - q)
    rw [show 2 * m + 1 - (q - p) = (2 * m - q) + p + 1 by omega]
    by_cases hqm : q ≤ m
    · have hqeq : q = m := by omega
      rw [ite_eq_left hqm, hqeq]
      rw [show 2 * m - m = m by omega]
    · rw [ite_eq_right hqm]
  calc ∑ q ∈ Finset.range (2 * m + 1),
        gammaEven (m + 1) (2 * m + 1 - Int.natAbs ((p : ℤ) - (q : ℤ))) *
          (if q ≤ m then xi q else xi (2 * m - q))
      = ∑ q ∈ Finset.Ico (p + m) (2 * m + 1),
          gammaEven (m + 1) (2 * m + 1 - Int.natAbs ((p : ℤ) - (q : ℤ))) *
            (if q ≤ m then xi q else xi (2 * m - q)) :=
        (Finset.sum_subset hsub hzero).symm
    _ = ∑ q ∈ Finset.Ico (p + m) (2 * m + 1),
          (fun j => gammaEven (m + 1) (j + p + 1) * xi j) (2 * m - q) :=
        Finset.sum_congr rfl hterm
    _ = ∑ j ∈ Finset.Ico (2 * m + 1 - (2 * m + 1)) (2 * m + 1 - (p + m)),
          gammaEven (m + 1) (j + p + 1) * xi j :=
        Finset.sum_Ico_reflect (fun j => gammaEven (m + 1) (j + p + 1) * xi j) (p + m)
          (m := 2 * m + 1) (n := 2 * m) (by omega)
    _ = xi p := by
        rw [show 2 * m + 1 - (2 * m + 1) = 0 by omega,
          show 2 * m + 1 - (p + m) = m + 1 - p by omega, Nat.Ico_zero_eq_range]
        have h := eigen_identity (m + 1) p (by omega : p < m + 1)
        simpa [gammaEven_apply_succ] using h

/-- For `p = m`, the `gammaEven m` part of the odd row sum vanishes. -/
private theorem sum_gammaEven_odd_row_center (m : ℕ) :
    ∑ q ∈ Finset.range (2 * m + 1),
        gammaEven m (2 * m + 1 - Int.natAbs ((m : ℤ) - (q : ℤ))) *
          (if q ≤ m then xi q else xi (2 * m - q)) = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  have hq2 : q < 2 * m + 1 := Finset.mem_range.mp hq
  have hd : Int.natAbs ((m : ℤ) - (q : ℤ)) ≤ m := by
    by_cases hqm : q ≤ m
    · rw [Int.natAbs_natCast_sub_natCast_of_ge (by omega : q ≤ m)]
      omega
    · rw [Int.natAbs_natCast_sub_natCast_of_le (by omega : m ≤ q)]
      omega
  have hk : m < 2 * m + 1 - Int.natAbs ((m : ℤ) - (q : ℤ)) := by omega
  rw [gammaEven_eq_zero_of_lt hk, zero_mul]

/-- For `p = m`, the `gammaEven (m + 1)` part of the odd row sum equals `2 * xi m`. -/
private theorem sum_gammaEven_succ_odd_row_center (m : ℕ) (hm : 0 < m) :
    ∑ q ∈ Finset.range (2 * m + 1),
        gammaEven (m + 1) (2 * m + 1 - Int.natAbs ((m : ℤ) - (q : ℤ))) *
          (if q ≤ m then xi q else xi (2 * m - q)) = 2 * xi m := by
  have hzero : ∀ q ∈ Finset.range (2 * m + 1), q ≠ 0 → q ≠ 2 * m →
      gammaEven (m + 1) (2 * m + 1 - Int.natAbs ((m : ℤ) - (q : ℤ))) *
        (if q ≤ m then xi q else xi (2 * m - q)) = 0 := by
    intro q hq h0 hlast
    have hq2 : q < 2 * m + 1 := Finset.mem_range.mp hq
    have hd : Int.natAbs ((m : ℤ) - (q : ℤ)) ≤ m - 1 := by
      by_cases hqm : q ≤ m
      · rw [Int.natAbs_natCast_sub_natCast_of_ge (by omega : q ≤ m)]
        omega
      · rw [Int.natAbs_natCast_sub_natCast_of_le (by omega : m ≤ q)]
        omega
    have hk : m + 1 < 2 * m + 1 - Int.natAbs ((m : ℤ) - (q : ℤ)) := by omega
    rw [gammaEven_eq_zero_of_lt hk, zero_mul]
  have hpair : (∑ q ∈ ({0, 2 * m} : Finset ℕ),
        gammaEven (m + 1) (2 * m + 1 - Int.natAbs ((m : ℤ) - (q : ℤ))) *
          (if q ≤ m then xi q else xi (2 * m - q))) =
      ∑ q ∈ Finset.range (2 * m + 1),
        gammaEven (m + 1) (2 * m + 1 - Int.natAbs ((m : ℤ) - (q : ℤ))) *
          (if q ≤ m then xi q else xi (2 * m - q)) := by
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_range]
      rcases hx with rfl | rfl <;> omega
    · intro x hx hxnot
      have hx0 : x ≠ 0 := by
        intro h
        exact hxnot (by rw [h]; simp)
      have hx2 : x ≠ 2 * m := by
        intro h
        exact hxnot (by rw [h]; simp)
      exact hzero x hx hx0 hx2
  have h0 : gammaEven (m + 1) (2 * m + 1 - Int.natAbs ((m : ℤ) - ((0 : ℕ) : ℤ))) *
      (if (0 : ℕ) ≤ m then xi 0 else xi (2 * m - 0)) = xi m := by
    have hlag : 2 * m + 1 - Int.natAbs ((m : ℤ) - ((0 : ℕ) : ℤ)) = m + 1 := by
      rw [Int.natAbs_natCast_sub_natCast_of_ge (by omega : (0 : ℕ) ≤ m)]
      omega
    rw [hlag, ite_eq_left (by omega : (0 : ℕ) ≤ m), gammaEven_apply_succ (m + 1) m,
      AM_succ_diag m, AM_eq_zero (by omega : m + 1 ≤ m + 1), xi_zero]
    ring
  have hlast : gammaEven (m + 1) (2 * m + 1 - Int.natAbs ((m : ℤ) - ((2 * m : ℕ) : ℤ))) *
      (if (2 * m : ℕ) ≤ m then xi (2 * m) else xi (2 * m - 2 * m)) = xi m := by
    have hlag : 2 * m + 1 - Int.natAbs ((m : ℤ) - ((2 * m : ℕ) : ℤ)) = m + 1 := by
      rw [Int.natAbs_natCast_sub_natCast_of_le (by omega : m ≤ 2 * m)]
      omega
    rw [hlag, ite_eq_right (by omega : ¬ (2 * m : ℕ) ≤ m),
      show (2 * m : ℕ) - 2 * m = 0 by omega, xi_zero,
      gammaEven_apply_succ (m + 1) m, AM_succ_diag m,
      AM_eq_zero (by omega : m + 1 ≤ m + 1)]
    ring
  rw [← hpair, Finset.sum_pair (by omega : (0 : ℕ) ≠ 2 * m)]
  rw [h0, hlast]
  ring

/-- For `p ≤ m`, the odd row sum equals `xi p`. See [ChildsLee2008], Theorem 1. -/
private theorem oddRow_sum_le (m p : ℕ) (hm : 0 < m) (hp : p ≤ m) :
    ∑ q ∈ Finset.range (2 * m + 1), oddRowTerm m p q = xi p := by
  have hsplit : ∀ q, oddRowTerm m p q =
      (gammaEven m (2 * m + 1 - Int.natAbs ((p : ℤ) - (q : ℤ))) *
          (if q ≤ m then xi q else xi (2 * m - q)) +
        gammaEven (m + 1) (2 * m + 1 - Int.natAbs ((p : ℤ) - (q : ℤ))) *
          (if q ≤ m then xi q else xi (2 * m - q))) / 2 := by
    intro q
    rw [oddRowTerm, gammaOdd_eq_average]
    ring
  calc ∑ q ∈ Finset.range (2 * m + 1), oddRowTerm m p q
      = ∑ q ∈ Finset.range (2 * m + 1),
          (gammaEven m (2 * m + 1 - Int.natAbs ((p : ℤ) - (q : ℤ))) *
              (if q ≤ m then xi q else xi (2 * m - q)) +
            gammaEven (m + 1) (2 * m + 1 - Int.natAbs ((p : ℤ) - (q : ℤ))) *
              (if q ≤ m then xi q else xi (2 * m - q))) / 2 :=
        Finset.sum_congr rfl (fun q _ => hsplit q)
    _ = ((∑ q ∈ Finset.range (2 * m + 1),
            gammaEven m (2 * m + 1 - Int.natAbs ((p : ℤ) - (q : ℤ))) *
              (if q ≤ m then xi q else xi (2 * m - q))) +
          ∑ q ∈ Finset.range (2 * m + 1),
            gammaEven (m + 1) (2 * m + 1 - Int.natAbs ((p : ℤ) - (q : ℤ))) *
              (if q ≤ m then xi q else xi (2 * m - q))) / 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ = xi p := by
        rcases lt_or_eq_of_le hp with hlt | heq
        · rw [sum_gammaEven_odd_row m p hlt, sum_gammaEven_succ_odd_row m p hlt]
          ring
        · rw [heq]
          rw [sum_gammaEven_odd_row_center m, sum_gammaEven_succ_odd_row_center m hm]
          ring

/-- For `p > m`, the odd row sum equals the reflected coordinate `xi (2 * m - p)`. See
[ChildsLee2008], Theorem 1. -/
private theorem oddRow_sum_gt (m p : ℕ) (hm : 0 < m) (hmp : m < p) (hp : p < 2 * m + 1) :
    ∑ q ∈ Finset.range (2 * m + 1), oddRowTerm m p q = xi (2 * m - p) := by
  have hp' : 2 * m - p ≤ m := by omega
  have hEq : (∑ q ∈ Finset.range (2 * m + 1), oddRowTerm m p q) =
      ∑ q ∈ Finset.range (2 * m + 1), oddRowTerm m (2 * m - p) q := by
    rw [← Finset.sum_range_reflect (fun q => oddRowTerm m (2 * m - p) q) (2 * m + 1)]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro q hq
    have hq2 : q ≤ 2 * m := by have := Finset.mem_range.mp hq; omega
    have hG : (if q ≤ m then xi q else xi (2 * m - q)) =
        (if 2 * m - q ≤ m then xi (2 * m - q) else xi (2 * m - (2 * m - q))) :=
      oddVec_symm m q hq2
    have hlag : Int.natAbs ((p : ℤ) - (q : ℤ)) =
        Int.natAbs (((2 * m - p : ℕ) : ℤ) - ((2 * m - q : ℕ) : ℤ)) := by
      have hneg : ((p : ℤ) - (q : ℤ)) =
          -(((2 * m - p : ℕ) : ℤ) - ((2 * m - q : ℕ) : ℤ)) := by
        rw [Nat.cast_sub (by omega : p ≤ 2 * m), Nat.cast_sub (by omega : q ≤ 2 * m)]
        push_cast
        ring
      rw [hneg, Int.natAbs_neg]
    simp only [oddRowTerm]
    rw [hlag, hG]
  rw [hEq]
  exact oddRow_sum_le m (2 * m - p) hm hp'

/-- For `0 < m`, the odd row sum equals the corresponding coordinate of the reflected
vector. See [ChildsLee2008], Theorem 1. -/
private theorem toeplitz_row_sum_odd (m : ℕ) (hm : 0 < m) (p : ℕ) (hp : p < 2 * m + 1) :
    ∑ q ∈ Finset.range (2 * m + 1), oddRowTerm m p q =
      (if p ≤ m then xi p else xi (2 * m - p)) := by
  by_cases hpm : p ≤ m
  · rw [ite_eq_left hpm]
    exact oddRow_sum_le m p hm hpm
  · rw [ite_eq_right hpm]
    exact oddRow_sum_gt m p hm (by omega) hp

/-- For `0 < m`, the odd Toeplitz matrix fixes the reflected vector `uOdd m`. See
[ChildsLee2008], Theorem 1. -/
theorem toeplitz_mulVec_uOdd (m : ℕ) (hm : 0 < m) :
    (toeplitz (2 * m + 1) (gammaOdd m)).mulVec (uOdd m) = uOdd m := by
  funext p
  calc ((toeplitz (2 * m + 1) (gammaOdd m)).mulVec (uOdd m)) p
      = ∑ i : Fin (2 * m + 1),
          (toeplitz (2 * m + 1) (gammaOdd m) p i) * (uOdd m i) := rfl
    _ = ∑ q ∈ Finset.range (2 * m + 1), oddRowTerm m p.val q := by
        rw [Finset.sum_fin_eq_sum_range]
        refine Finset.sum_congr rfl (fun q hq => ?_)
        rw [dite_eq_left (Finset.mem_range.mp hq)]
        simp [oddRowTerm, toeplitz, uOdd]
    _ = (if p.val ≤ m then xi p.val else xi (2 * m - p.val)) :=
        toeplitz_row_sum_odd m hm p.val p.isLt
    _ = uOdd m p := by simp [uOdd]

/-- The odd Toeplitz weight matrix is Hermitian. -/
theorem toeplitz_isHermitian_gammaOdd (m : ℕ) :
    (toeplitz (2 * m + 1) (gammaOdd m)).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [toeplitz, star_trivial]
  rw [show ((i.val : ℤ) - (j.val : ℤ)) = -(((j.val : ℤ) - (i.val : ℤ))) by ring,
    Int.natAbs_neg]

/-- For `0 < m`, every real eigenvalue of the odd Toeplitz matrix has absolute value at most
one. See [ChildsLee2008], Theorem 1. -/
theorem toeplitz_gammaOdd_eigenvalue_abs_le_one (m : ℕ) (hm : 0 < m) (lam : ℝ)
    (hlam : ∃ v : Fin (2 * m + 1) → ℝ, v ≠ 0 ∧
      (toeplitz (2 * m + 1) (gammaOdd m)).mulVec v = lam • v) : |lam| ≤ 1 := by
  have : Nonempty (Fin (2 * m + 1)) := ⟨⟨0, by omega⟩⟩
  exact abs_eigenvalue_le_of_pos_eigenvector (toeplitz (2 * m + 1) (gammaOdd m))
    (toeplitz (2 * m + 1) (gammaOdd m)) (uOdd m) 1
    (fun i j => gammaOdd_nonneg m _) (fun i j => le_rfl) (fun i => uOdd_pos m i)
    zero_lt_one (by rw [toeplitz_mulVec_uOdd m hm]; simp) lam hlam

/-- For `0 < m`, the odd Toeplitz weight matrix has Euclidean operator norm at most one. See
[ChildsLee2008], Theorem 1. -/
theorem toeplitz_gammaOdd_l2_opNorm_le_one (m : ℕ) (hm : 0 < m) :
    ‖(toeplitz (2 * m + 1) (gammaOdd m) :
      Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ)‖ ≤ 1 := by
  have : Nonempty (Fin (2 * m + 1)) := ⟨⟨0, by omega⟩⟩
  exact l2_opNorm_le_one_of_eigenvalue_mem _
    (toeplitz_isHermitian_gammaOdd m)
    (fun lam hlam => toeplitz_gammaOdd_eigenvalue_abs_le_one m hm lam hlam)

/-- For `i < 2 * m + 1`, the `i`th upper diagonal sum of the odd dual outer-product matrix
is at least one. See [ChildsLee2008], Theorem 1. -/
theorem diagSum_outerVec_uOdd_ge_one (m : ℕ) (i : ℕ) (hi : i < 2 * m + 1) :
    1 ≤ diagSum (outerVec (uOdd m)) i := by
  rw [diagSum_outerVec]
  have hterm : ∀ j : Fin (2 * m + 1 - i),
      xi j.val * xi (2 * m - i - j.val) ≤
        uOdd m ⟨j.val, by omega⟩ * uOdd m ⟨j.val + i, by omega⟩ := by
    intro j
    have hj : j.val < 2 * m + 1 - i := j.isLt
    have h1 : xi j.val ≤ uOdd m ⟨j.val, by omega⟩ := xi_le_uOdd m ⟨j.val, by omega⟩
    have h2 : xi (2 * m - i - j.val) ≤ uOdd m ⟨j.val + i, by omega⟩ := by
      unfold uOdd
      by_cases hc : j.val + i ≤ m
      · rw [ite_eq_left hc]
        exact xi_antitone_le (by omega : j.val + i ≤ 2 * m - i - j.val)
      · rw [ite_eq_right hc]
        rw [show 2 * m - (j.val + i) = 2 * m - i - j.val by omega]
    have hnn : 0 ≤ xi (2 * m - i - j.val) := le_of_lt (xi_pos _)
    exact mul_le_mul h1 h2 hnn (le_of_lt (uOdd_pos m _))
  have hconv : (∑ j : Fin (2 * m + 1 - i), xi j.val * xi (2 * m - i - j.val)) = 1 := by
    rw [Finset.sum_fin_eq_sum_range]
    have hsimp : ∀ j ∈ Finset.range (2 * m + 1 - i),
        (if h : j < 2 * m + 1 - i then xi j * xi (2 * m - i - j) else 0) =
          xi j * xi (2 * m - i - j) := by
      intro j hj
      rw [dite_eq_left (Finset.mem_range.mp hj)]
    rw [Finset.sum_congr rfl hsimp]
    have h := source_proposition_four (2 * m - i)
    rw [show 2 * m - i + 1 = 2 * m + 1 - i by omega] at h
    exact h
  calc (1 : ℝ) = ∑ j : Fin (2 * m + 1 - i), xi j.val * xi (2 * m - i - j.val) :=
        hconv.symm
    _ ≤ ∑ j : Fin (2 * m + 1 - i),
          uOdd m ⟨j.val, by omega⟩ * uOdd m ⟨j.val + i, by omega⟩ :=
        Finset.sum_le_sum (fun j _ => hterm j)

/-- The trace of the odd dual outer-product matrix equals the odd primal objective. See
[ChildsLee2008], Theorem 1. -/
theorem trace_dual_eq_objective_odd (m : ℕ) (hm : 0 < m) :
    (outerVec (uOdd m)).trace = objective (2 * m + 1) (gammaOdd m) := by
  rw [trace_outerVec, sum_uOdd_sq, objective_gammaOdd m (by omega : 1 ≤ m),
    AM_zero (m + 1), AM_zero m]
  rw [Finset.sum_range_succ (fun i => xi i ^ 2) m]
  ring

/-- The trace of the odd Toeplitz matrix times the dual outer-product matrix equals the trace
of the dual matrix. See [ChildsLee2008], Theorem 1. -/
theorem trace_toeplitz_mul_outerVec_odd_eq_trace (m : ℕ) (hm : 0 < m) :
    (toeplitz (2 * m + 1) (gammaOdd m) * outerVec (uOdd m)).trace =
      (outerVec (uOdd m)).trace := by
  unfold outerVec
  rw [Matrix.mul_vecMulVec, toeplitz_mulVec_uOdd m hm]

/-- For `0 < m`, collects nonnegative odd weights, the odd Toeplitz operator-norm bound,
positive semidefiniteness and diagonal-sum feasibility of the odd dual matrix, and the
matching objective and product-trace identities. See [ChildsLee2008], Theorem 1. -/
theorem source_theorem_one_odd_certificate (m : ℕ) (hm : 0 < m) :
    (∀ i, 0 ≤ gammaOdd m i) ∧
      ‖(toeplitz (2 * m + 1) (gammaOdd m) :
        Matrix (Fin (2 * m + 1)) (Fin (2 * m + 1)) ℝ)‖ ≤ 1 ∧
      (outerVec (uOdd m)).PosSemidef ∧
      (∀ i < 2 * m + 1, 1 ≤ diagSum (outerVec (uOdd m)) i) ∧
      (outerVec (uOdd m)).trace = objective (2 * m + 1) (gammaOdd m) ∧
      (toeplitz (2 * m + 1) (gammaOdd m) * outerVec (uOdd m)).trace =
        (outerVec (uOdd m)).trace :=
  ⟨gammaOdd_nonneg m, toeplitz_gammaOdd_l2_opNorm_le_one m hm,
    posSemidef_outerVec _, fun i hi => diagSum_outerVec_uOdd_ge_one m i hi,
    trace_dual_eq_objective_odd m hm, trace_toeplitz_mul_outerVec_odd_eq_trace m hm⟩

end Qatlib.Papers.AdversarySrch07.AdversarySdp
