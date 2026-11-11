/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Qatlib.Papers.QLearningGeom03.MainResults.GroupAlgebraZN2

/-!
# Majority learning in the binary group algebra

This module defines the Hamming weight `wt`, majority phase `majPhi`, and normalized majority
matrix `majMatrix`. It proves the group-algebra representation and Hadamard diagonalization, and
shows that complementing the row label negates the matrix entries when the bit length is odd.

These identities provide the algebraic setup for the majority learning example in
[HunzikerEtAl2003].

## Main statements

* `majMatrix_eq_groupAlgebraElem`: Group-algebra representation of the majority matrix.
* `maj_diagonalization`: Hadamard diagonalization with eigenvalues `majEigen`.
* `majMatrix_add_ones`: Complementing a row label negates its entries for odd dimension.

## References

* [Hunziker et al., 2003][HunzikerEtAl2003]
-/

set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Qatlib.Papers.QLearningGeom03.MainResults

open Matrix
open scoped Matrix

/-- The Hamming weight of a binary string, counting its nonzero coordinates. -/
def wt {n : ℕ} (b : Bits n) : ℕ := (Finset.univ.filter (fun i => b i ≠ 0)).card

/-- The binary string of length `n` whose coordinates are all 1. -/
def ones (n : ℕ) : Bits n := fun _ => 1

/-- The Hamming weight of a binary string of length n is at most n. -/
lemma wt_le {n : ℕ} (b : Bits n) : wt b ≤ n := by
  unfold wt
  calc (Finset.univ.filter (fun i => b i ≠ 0)).card
      ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := by simp

/-- Every element of `ZMod 2` is either 0 or 1. -/
lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hlt : a.val < 2 := ZMod.val_lt a
  have h : a = ((a.val : ℕ) : ZMod 2) := (ZMod.natCast_zmod_val a).symm
  have hv : a.val = 0 ∨ a.val = 1 := by omega
  rcases hv with h0 | h1
  · left; rw [h, h0]; norm_num
  · right; rw [h, h1]; norm_num

/-- Adding the all-ones string changes the Hamming weight from `wt b` to `n - wt b`. -/
lemma wt_add_ones {n : ℕ} (b : Bits n) : wt (b + ones n) = n - wt b := by
  have hp : Finset.univ.filter (fun i : Fin n => (b + ones n) i ≠ 0)
      = Finset.univ.filter (fun i : Fin n => b i = 0) := by
    apply Finset.filter_congr
    intro i _
    simp only [ones, Pi.add_apply]
    constructor
    · intro h
      rcases zmod2_eq_zero_or_one (b i) with h0 | h1
      · exact h0
      · exfalso
        apply h
        rw [h1]
        decide
    · intro h0
      rw [h0]; norm_num
  unfold wt
  rw [hp]
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun i => b i = 0)
  rw [Finset.card_univ, Fintype.card_fin] at hcard
  have hnot : Finset.univ.filter (fun i : Fin n => ¬ (b i = 0))
      = Finset.univ.filter (fun i : Fin n => b i ≠ 0) := rfl
  rw [hnot] at hcard
  omega

/-- Negating a binary string preserves its Hamming weight. -/
lemma wt_neg {n : ℕ} (b : Bits n) : wt (-b) = wt b := by
  unfold wt
  congr 1
  apply Finset.filter_congr
  intro i _
  simp

/-- The majority phase, equal to -1 when twice the Hamming weight is at most n and 1 otherwise.
This is the phase convention for the majority example in [HunzikerEtAl2003]. -/
noncomputable def majPhi {n : ℕ} (b : Bits n) : ℂ :=
  if 2 * wt b ≤ n then -1 else 1

/-- Negating a binary string preserves its majority phase. -/
lemma majPhi_neg {n : ℕ} (b : Bits n) : majPhi (-b) = majPhi b := by
  unfold majPhi
  rw [wt_neg]

/-- For odd bit length, complementing every bit negates the majority phase, as used in
[HunzikerEtAl2003]. -/
lemma majPhi_add_ones {n m : ℕ} (hn : n = 2 * m + 1) (b : Bits n) :
    majPhi (b + ones n) = - majPhi b := by
  have harith : 2 * (n - wt b) ≤ n ↔ ¬ (2 * wt b ≤ n) := by
    have hw : wt b ≤ n := wt_le b
    omega
  have hiff : 2 * wt (b + ones n) ≤ n ↔ ¬ (2 * wt b ≤ n) := by
    rw [wt_add_ones]
    exact harith
  unfold majPhi
  by_cases h : 2 * wt b ≤ n
  · have h' : ¬ 2 * wt (b + ones n) ≤ n := by
      rw [hiff]
      intro hc
      exact hc h
    rw [if_neg h', if_pos h]
    norm_num
  · have h' : 2 * wt (b + ones n) ≤ n := by
      rw [hiff]
      exact h
    rw [if_pos h', if_neg h]

/-- The majority phase multiplied by the normalization factor 2^(-n/2). -/
noncomputable def majCoeff {n : ℕ} (b : Bits n) : ℂ :=
  (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ n * majPhi b

/-- The translation-invariant matrix whose (a, x) entry is `majCoeff (a - x)`. -/
noncomputable def majMatrix {n : ℕ} : Matrix (Bits n) (Bits n) ℂ :=
  fun a x => majCoeff (a - x)

/-- The majority matrix is the binary group-algebra matrix of `majCoeff`, providing the
representation used in [HunzikerEtAl2003]. -/
theorem majMatrix_eq_groupAlgebraElem {n : ℕ} :
    majMatrix (n := n) = groupAlgebraElem (majCoeff (n := n)) := by
  ext a x
  rw [groupAlgebraElem_apply]
  rfl

/-- The Fourier coefficient of the normalized majority phase at the binary frequency `c`. -/
noncomputable def majEigen {n : ℕ} (c : Bits n) : ℂ :=
  ∑ x, majCoeff x * chi c x

/-- The majority eigenvalue is 2^(-n/2) times the character sum of the unnormalized majority
phase, as used in [HunzikerEtAl2003]. -/
lemma majEigen_eq {n : ℕ} (c : Bits n) :
    majEigen c = (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ n * ∑ x, majPhi x * chi c x := by
  unfold majEigen majCoeff
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- Hadamard conjugation diagonalizes the majority matrix with diagonal entries `majEigen`, as
used in the majority analysis of [HunzikerEtAl2003]. -/
theorem maj_diagonalization {n : ℕ} :
    hadamard n * majMatrix (n := n) * hadamard n
      = Matrix.diagonal (majEigen (n := n)) := by
  rw [majMatrix_eq_groupAlgebraElem]
  exact hadamard_conj_groupAlgebraElem _

/-- For odd bit length, complementing the row label negates each entry of the majority matrix,
as used in [HunzikerEtAl2003]. -/
lemma majMatrix_add_ones {n m : ℕ} (hn : n = 2 * m + 1) (a x : Bits n) :
    majMatrix (a + ones n) x = - majMatrix a x := by
  unfold majMatrix majCoeff
  rw [show a + ones n - x = (a - x) + ones n by abel]
  rw [majPhi_add_ones hn]
  ring

/-- Every diagonal entry of the majority matrix is the majority coefficient at the zero string. -/
lemma majMatrix_diag {n : ℕ} (x : Bits n) :
    majMatrix x x = majCoeff (0 : Bits n) := by
  unfold majMatrix
  rw [sub_self]

/-- The majority matrix is symmetric, as used in the majority learning example of
[HunzikerEtAl2003]. -/
lemma majMatrix_symmetric {n : ℕ} : (majMatrix (n := n))ᵀ = majMatrix := by
  ext a x
  rw [Matrix.transpose_apply]
  unfold majMatrix majCoeff
  rw [show x - a = -(a - x) by abel, majPhi_neg]

end Qatlib.Papers.QLearningGeom03.MainResults
