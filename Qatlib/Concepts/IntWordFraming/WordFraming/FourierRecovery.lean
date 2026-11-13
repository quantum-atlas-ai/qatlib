/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.IntWordFraming.WordFraming.SmithNormalizationDefs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Smith normal form and abelian presentation recovery

This module proves correctness and uniqueness of rectangular Smith reduction over the integers
and constructs explicit cyclic coordinates for the resulting presentation modules. Normalization
removes trivial cyclic factors, yields word-equality tests, and recovers generators and
canonical invariant factors from valid compact abelian presentations.

The final results verify binary input and output encodings and bound recorded control
operations, Euclidean calls, and quotient-remainder pairs. These algebraic recovery results
support the finite abelian group decomposition setting of [CheungMosca2001]; the bounds refer to
the declared counters and their recorded input sizes.

## Main statements

* `rectangularSmith_form` and `rectangularSmith_unique`: correctness and uniqueness of Smith
  form.
* `rectangularSmithCyclicEquiv`: explicit cyclic coordinates for an integer presentation.
* `compactRecovery_factors_canonical`: presentation-independent factors for a finite abelian
  group.
* `smithRunBinaryEuclid_division_bound`: a bound on the recorded quotient-remainder pairs.

## References

* [Cheung and Mosca, 2001][CheungMosca2001]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.HspRecovery.CfOrder
open Qatlib.Concepts.HspRecovery.JointDlog
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.IntWordFraming.WordFraming

open Matrix

/-- Converting an integer matrix to a table and back returns the original matrix. -/
@[simp] theorem tableMatrix_matrixTable {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    tableMatrix (matrixTable A) = A := by
  ext r c
  simp [tableMatrix, matrixTable]

/-- Materializing an integer matrix leaves it unchanged. -/
@[simp] theorem materializeMatrix_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    materializeMatrix A = A := by
  exact tableMatrix_matrixTable A

/-- The Euclidean pair matrix and its specified inverse are mutual inverses, and the pair matrix
sends `![a,b]` to the vector consisting of their gcd and zero. -/
theorem euclidPair_correct (a b : ℤ) :
    euclidPair a b * euclidPairInverse a b = 1 ∧
    euclidPairInverse a b * euclidPair a b = 1 ∧
    euclidPair a b *ᵥ ![a,b] = ![(Int.gcd a b : ℤ),0] := by
  by_cases hz : Int.gcd a b = 0
  · obtain ⟨rfl, rfl⟩ := Int.gcd_eq_zero_iff.mp hz
    decide
  · have hg : (Int.gcd a b : ℤ) ≠ 0 := by exact_mod_cast hz
    have ha := Int.mul_ediv_cancel_of_dvd (Int.gcd_dvd_left a b)
    have hb := Int.mul_ediv_cancel_of_dvd (Int.gcd_dvd_right a b)
    have hbez := Int.gcd_eq_gcd_ab a b
    have hquot : Int.gcdA a b * (a / (Int.gcd a b : ℤ)) +
        Int.gcdB a b * (b / (Int.gcd a b : ℤ)) = 1 := by
      apply mul_left_cancel₀ hg
      calc
        _ = Int.gcdA a b * ((Int.gcd a b : ℤ) * (a / (Int.gcd a b : ℤ))) +
            Int.gcdB a b * ((Int.gcd a b : ℤ) * (b / (Int.gcd a b : ℤ))) := by ring
        _ = a * Int.gcdA a b + b * Int.gcdB a b := by rw [ha, hb]; ring
        _ = (Int.gcd a b : ℤ) * 1 := by rw [← hbez, mul_one]
    have hcross : -(b / (Int.gcd a b : ℤ)) * a +
        (a / (Int.gcd a b : ℤ)) * b = 0 := by
      calc
        _ = -(b / (Int.gcd a b : ℤ)) * ((Int.gcd a b : ℤ) * (a / (Int.gcd a b : ℤ))) +
            (a / (Int.gcd a b : ℤ)) * ((Int.gcd a b : ℤ) * (b / (Int.gcd a b : ℤ))) := by
              rw [ha, hb]
        _ = 0 := by ring
    refine ⟨?_, ?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [euclidPair, euclidPairInverse, hz, Matrix.mul_apply, Fin.sum_univ_two]
      all_goals first | linear_combination hquot | ring
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [euclidPair, euclidPairInverse, hz, Matrix.mul_apply, Fin.sum_univ_two]
      all_goals first | linear_combination hquot | ring
    · ext i
      fin_cases i <;> simp [euclidPair, hz, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      · linear_combination -hbez
      · simpa only [neg_mul] using! hcross

/-- Mixing two rows by the identity matrix leaves the matrix unchanged. -/
theorem rowMix_one {m n : ℕ} (i j : Fin m) (A : Matrix (Fin m) (Fin n) ℤ) :
    rowMix i j 1 A = A := by
  ext r c
  by_cases hi : r = i
  · subst r; simp [rowMix]
  · by_cases hj : r = j
    · subst r; simp [rowMix, hi]
    · simp [rowMix, hi, hj]

/-- For distinct row indices, successive row mixes by `D` and `C` equal a single row mix by `C *
D`. -/
theorem rowMix_compose {m n : ℕ} (i j : Fin m) (hij : i ≠ j)
    (C D : Matrix (Fin 2) (Fin 2) ℤ) (A : Matrix (Fin m) (Fin n) ℤ) :
    rowMix i j C (rowMix i j D A) = rowMix i j (C*D) A := by
  ext r c
  by_cases hi : r = i
  · subst r
    simp [rowMix, Ne.symm hij, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  · by_cases hj : r = j
    · subst r
      simp [rowMix, Ne.symm hij, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    · simp [rowMix, hi, hj]

/-- Mixing rows of the left factor commutes with multiplication on the right. -/
theorem rowMix_mul {m n q : ℕ} (i j : Fin m)
    (C : Matrix (Fin 2) (Fin 2) ℤ) (A : Matrix (Fin m) (Fin n) ℤ)
    (B : Matrix (Fin n) (Fin q) ℤ) :
    rowMix i j C A * B = rowMix i j C (A*B) := by
  ext r c
  by_cases hi : r = i
  · subst r
    simp [rowMix, Matrix.mul_apply, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  · by_cases hj : r = j
    · subst r
      simp [rowMix, hi, Matrix.mul_apply, add_mul,
        Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
    · simp [rowMix, hi, hj, Matrix.mul_apply]

/-- A row mix is left multiplication by the same mix applied to the identity matrix. -/
theorem rowMix_as_left_mul {m n : ℕ} (i j : Fin m)
    (C : Matrix (Fin 2) (Fin 2) ℤ) (A : Matrix (Fin m) (Fin n) ℤ) :
    rowMix i j C A = rowMix i j C (1 : Matrix (Fin m) (Fin m) ℤ) * A := by
  rw [rowMix_mul i j, Matrix.one_mul]

/-- For distinct row indices, row mixing by the Euclidean pair matrix and its inverse undo each
other in either order. -/
theorem rowMix_euclid_inverse {m n : ℕ} (i j : Fin m) (hij : i ≠ j)
    (a b : ℤ) (A : Matrix (Fin m) (Fin n) ℤ) :
    rowMix i j (euclidPairInverse a b) (rowMix i j (euclidPair a b) A) = A ∧
      rowMix i j (euclidPair a b) (rowMix i j (euclidPairInverse a b) A) = A := by
  obtain ⟨hCI,hIC,_⟩ := euclidPair_correct a b
  constructor
  · rw [rowMix_compose i j hij, hIC, rowMix_one]
  · rw [rowMix_compose i j hij, hCI, rowMix_one]

/-- A column elimination step preserves the state's encoding of the original matrix. -/
theorem columnStep_encodes {m n : ℕ} (p : Fin n)
    (A : Matrix (Fin (m+1)) (Fin n) ℤ) (s : ColumnEliminationState (m+1) n)
    (hs : s.Encodes A) (k : Fin m) : (columnStep p s k).Encodes A := by
  let C := euclidPair (s.value 0 p) (s.value k.succ p)
  let CI := euclidPairInverse (s.value 0 p) (s.value k.succ p)
  let E := rowMix 0 k.succ C (1 : Matrix (Fin (m+1)) (Fin (m+1)) ℤ)
  let EI := rowMix 0 k.succ CI (1 : Matrix (Fin (m+1)) (Fin (m+1)) ℤ)
  have hdistinct : (0 : Fin (m+1)) ≠ k.succ := (Fin.succ_ne_zero k).symm
  obtain ⟨hCCI,hCIC,_⟩ := euclidPair_correct (s.value 0 p) (s.value k.succ p)
  have he : E * EI = 1 := by
    change rowMix 0 k.succ C 1 * rowMix 0 k.succ CI 1 = 1
    rw [← rowMix_as_left_mul, rowMix_compose _ _ hdistinct, hCCI, rowMix_one]
  have hei : EI * E = 1 := by
    change rowMix 0 k.succ CI 1 * rowMix 0 k.succ C 1 = 1
    rw [← rowMix_as_left_mul, rowMix_compose _ _ hdistinct, hCIC, rowMix_one]
  refine ⟨?_,?_,?_⟩
  · change rowMix 0 k.succ C s.value = rowMix 0 k.succ C s.left * A
    rw [rowMix_mul, ← hs.1]
  · change rowMix 0 k.succ C s.left * (s.inverse * EI) = 1
    rw [rowMix_as_left_mul]
    change (E * s.left) * (s.inverse * EI) = 1
    calc
      _ = E * (s.left * s.inverse) * EI := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hs.2.1, Matrix.mul_one, he]
  · change (s.inverse * EI) * rowMix 0 k.succ C s.left = 1
    rw [rowMix_as_left_mul]
    change (s.inverse * EI) * (E * s.left) = 1
    calc
      _ = s.inverse * (EI * E) * s.left := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hei, Matrix.mul_one, hs.2.2]

/-- A column elimination step replaces the pivot by the gcd of the pivot and selected entry and
clears that selected entry. -/
theorem columnStep_pivot {m n : ℕ} (p : Fin n) (s : ColumnEliminationState (m+1) n)
    (k : Fin m) :
    (columnStep p s k).value 0 p = (Int.gcd (s.value 0 p) (s.value k.succ p) : ℤ) ∧
      (columnStep p s k).value k.succ p = 0 := by
  have h := (euclidPair_correct (s.value 0 p) (s.value k.succ p)).2.2
  constructor
  · simpa [columnStep, rowMix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using! congrFun h 0
  · simpa [columnStep, rowMix, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using! congrFun h 1

/-- A column elimination step preserves any already-zero entry below the pivot in the selected
column. -/
theorem columnStep_preserves_zero {m n : ℕ} (p : Fin n)
    (s : ColumnEliminationState (m+1) n) (k r : Fin m) (hr : s.value r.succ p = 0) :
    (columnStep p s k).value r.succ p = 0 := by
  by_cases h : r = k
  · subst r
    exact (columnStep_pivot p s k).2
  · simpa [columnStep, rowMix, h] using! hr

/-- Folding column elimination steps over any index list preserves the encoding of the original
matrix. -/
theorem columnFold_encodes {m n : ℕ} (p : Fin n)
    (A : Matrix (Fin (m+1)) (Fin n) ℤ) (s : ColumnEliminationState (m+1) n)
    (hs : s.Encodes A) (ks : List (Fin m)) : (ks.foldl (columnStep p) s).Encodes A := by
  induction ks generalizing s with
  | nil => exact hs
  | cons k ks ih => exact ih _ (columnStep_encodes p A s hs k)

/-- Folding column elimination steps preserves an already-zero entry below the pivot in the
selected column. -/
theorem columnFold_preserves_zero {m n : ℕ} (p : Fin n)
    (s : ColumnEliminationState (m+1) n) (r : Fin m) (hr : s.value r.succ p = 0)
    (ks : List (Fin m)) : (ks.foldl (columnStep p) s).value r.succ p = 0 := by
  induction ks generalizing s with
  | nil => exact hr
  | cons k ks ih => exact ih _ (columnStep_preserves_zero p s k r hr)

/-- Folding column elimination steps clears every below-pivot entry whose index occurs in the
list. -/
theorem columnFold_clears_member {m n : ℕ} (p : Fin n)
    (s : ColumnEliminationState (m+1) n) (ks : List (Fin m)) (r : Fin m) (hr : r ∈ ks) :
    (ks.foldl (columnStep p) s).value r.succ p = 0 := by
  induction ks generalizing s with
  | nil => simp at hr
  | cons k ks ih =>
    rcases List.mem_cons.mp hr with h | h
    · subst r
      exact columnFold_preserves_zero p _ k (columnStep_pivot p s k).2 ks
    · exact ih _ h

/-- Column reduction encodes the original matrix and clears all entries below its pivot in the
selected column. -/
theorem columnReduce_correct {m n : ℕ} (p : Fin n) (A : Matrix (Fin (m+1)) (Fin n) ℤ) :
    (columnReduce p A).Encodes A ∧ ∀ r : Fin m, (columnReduce p A).value r.succ p = 0 := by
  constructor
  · apply columnFold_encodes
    simp [ColumnEliminationState.Encodes]
  · intro r
    exact columnFold_clears_member p _ _ r (List.mem_finRange r)

/-- Left multiplication of the column-reduced value by its recorded inverse reconstructs the
original matrix. -/
theorem columnReduce_reconstruct {m n : ℕ} (p : Fin n)
    (A : Matrix (Fin (m+1)) (Fin n) ℤ) :
    (columnReduce p A).inverse * (columnReduce p A).value = A := by
  have hs := (columnReduce_correct p A).1
  rw [hs.1, ← Matrix.mul_assoc, hs.2.2, Matrix.one_mul]

/-- Each original entry in the selected column is the reduced pivot times the corresponding
entry of the recorded inverse's first column. -/
theorem columnReduce_entry {m n : ℕ} (p : Fin n)
    (A : Matrix (Fin (m+1)) (Fin n) ℤ) (r : Fin (m+1)) :
    A r p = (columnReduce p A).inverse r 0 * (columnReduce p A).value 0 p := by
  calc
    A r p = ((columnReduce p A).inverse * (columnReduce p A).value) r p :=
      congrArg (fun B => B r p) (columnReduce_reconstruct p A).symm
    _ = _ := by
      simp [Matrix.mul_apply, Fin.sum_univ_succ, (columnReduce_correct p A).2]

/-- An integer divides every entry of a column if and only if it divides that column's reduced
pivot. -/
theorem columnReduce_dvd_iff {m n : ℕ} (p : Fin n)
    (A : Matrix (Fin (m+1)) (Fin n) ℤ) (d : ℤ) :
    (∀ r, d ∣ A r p) ↔ d ∣ (columnReduce p A).value 0 p := by
  constructor
  · intro hd
    rw [(columnReduce_correct p A).1.1, Matrix.mul_apply]
    exact Finset.dvd_sum fun r _ => dvd_mul_of_dvd_right (hd r) _
  · intro hd r
    rw [columnReduce_entry p A r]
    exact dvd_mul_of_dvd_right hd _

/-- If a nonzero column pivot fails to divide some entry in its column, column reduction
strictly decreases its absolute value. -/
theorem columnReduce_pivot_strict {m n : ℕ} (p : Fin n)
    (A : Matrix (Fin (m+1)) (Fin n) ℤ) (h0 : A 0 p ≠ 0)
    (hbad : ∃ r, ¬ A 0 p ∣ A r p) :
    ((columnReduce p A).value 0 p).natAbs < (A 0 p).natAbs := by
  have hdiv : ∀ r, (columnReduce p A).value 0 p ∣ A r p :=
    (columnReduce_dvd_iff p A _).mpr (dvd_refl _)
  apply lt_of_le_of_ne (Int.natAbs_le_of_dvd_ne_zero (hdiv 0) h0)
  intro heq
  have hd : A 0 p ∣ (columnReduce p A).value 0 p := by
    apply Int.natAbs_dvd_natAbs.mp
    rw [heq]
  obtain ⟨r, hr⟩ := hbad
  exact hr (hd.trans (hdiv r))

/-- The integer-linear equivalence between the presentation modules of a matrix and its
column-reduced value. -/
def columnReduceQuotientEquiv {m n : ℕ} (p : Fin n)
    (A : Matrix (Fin (m+1)) (Fin n) ℤ) :
    PresentationModule A ≃ₗ[ℤ] PresentationModule (columnReduce p A).value := by
  let s := columnReduce p A
  have hs := (columnReduce_correct p A).1
  let e : (Fin (m+1) → ℤ) ≃ₗ[ℤ] (Fin (m+1) → ℤ) :=
    Matrix.toLin'OfInv (M := s.inverse) (M' := s.left) hs.2.2 hs.2.1
  apply Submodule.Quotient.equiv (LinearMap.range A.mulVecLin) (LinearMap.range s.value.mulVecLin) e
  change (LinearMap.range A.mulVecLin).map s.left.mulVecLin = LinearMap.range s.value.mulVecLin
  rw [← LinearMap.range_comp, ← Matrix.mulVecLin_mul, ← hs.1]

/-- On quotient representatives, `columnReduceQuotientEquiv` applies the recorded left
transformation. -/
theorem columnReduceQuotientEquiv_mk {m n : ℕ} (p : Fin n)
    (A : Matrix (Fin (m+1)) (Fin n) ℤ) (v : Fin (m+1) → ℤ) :
    columnReduceQuotientEquiv p A (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ((columnReduce p A).left *ᵥ v) := rfl

/-- On quotient representatives, the inverse column-reduction equivalence applies the recorded
inverse transformation. -/
theorem columnReduceQuotientEquiv_symm_mk {m n : ℕ} (p : Fin n)
    (A : Matrix (Fin (m+1)) (Fin n) ℤ) (v : Fin (m+1) → ℤ) :
    (columnReduceQuotientEquiv p A).symm (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk ((columnReduce p A).inverse *ᵥ v) := rfl

/-- Row reduction encodes the original matrix and clears all entries to the right of its pivot
in the selected row. -/
theorem rowReduce_correct {m n : ℕ} (p : Fin m)
    (A : Matrix (Fin m) (Fin (n+1)) ℤ) :
    (rowReduce p A).Encodes A ∧ ∀ c : Fin n, (rowReduce p A).value p c.succ = 0 := by
  have hs := columnReduce_correct p A.transpose
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simpa [rowReduce, Matrix.transpose_mul] using! congrArg Matrix.transpose hs.1.1
  · simpa [rowReduce, Matrix.transpose_mul] using! congrArg Matrix.transpose hs.1.2.2
  · simpa [rowReduce, Matrix.transpose_mul] using! congrArg Matrix.transpose hs.1.2.1
  · intro c
    exact hs.2 c

/-- Right multiplication of the row-reduced value by its recorded inverse reconstructs the
original matrix. -/
theorem rowReduce_reconstruct {m n : ℕ} (p : Fin m)
    (A : Matrix (Fin m) (Fin (n+1)) ℤ) :
    (rowReduce p A).value * (rowReduce p A).inverse = A := by
  have hs := (rowReduce_correct p A).1
  rw [hs.1, Matrix.mul_assoc, hs.2.1, Matrix.mul_one]

/-- An integer divides every entry of a row if and only if it divides that row's reduced pivot. -/
theorem rowReduce_dvd_iff {m n : ℕ} (p : Fin m)
    (A : Matrix (Fin m) (Fin (n+1)) ℤ) (d : ℤ) :
    (∀ c, d ∣ A p c) ↔ d ∣ (rowReduce p A).value p 0 :=
  columnReduce_dvd_iff p A.transpose d

/-- If a nonzero row pivot fails to divide some entry in its row, row reduction strictly
decreases its absolute value. -/
theorem rowReduce_pivot_strict {m n : ℕ} (p : Fin m)
    (A : Matrix (Fin m) (Fin (n+1)) ℤ) (h0 : A p 0 ≠ 0)
    (hbad : ∃ c, ¬ A p 0 ∣ A p c) :
    ((rowReduce p A).value p 0).natAbs < (A p 0).natAbs :=
  columnReduce_pivot_strict p A.transpose h0 hbad

/-- Row reduction preserves the range of the integer-linear map defined by matrix-vector
multiplication. -/
theorem rowReduce_range {m n : ℕ} (p : Fin m)
    (A : Matrix (Fin m) (Fin (n+1)) ℤ) :
    LinearMap.range (rowReduce p A).value.mulVecLin = LinearMap.range A.mulVecLin := by
  apply le_antisymm
  · rw [(rowReduce_correct p A).1.1, Matrix.mulVecLin_mul, LinearMap.range_comp]
    exact LinearMap.map_le_range
  · calc
      LinearMap.range A.mulVecLin =
          LinearMap.range ((rowReduce p A).value * (rowReduce p A).inverse).mulVecLin :=
        congrArg (fun B => LinearMap.range B.mulVecLin) (rowReduce_reconstruct p A).symm
      _ ≤ _ := by
        rw [Matrix.mulVecLin_mul]
        exact LinearMap.range_comp_le_range _ _

/-- Multiplication by `firstRowShear v` adds `v r` times the original first row to each row `r`. -/
theorem firstRowShear_mul {m n : ℕ} (v : Fin (m+1) → ℤ)
    (A : Matrix (Fin (m+1)) (Fin n) ℤ) (r : Fin (m+1)) (c : Fin n) :
    (firstRowShear v * A) r c = A r c + v r * A 0 c := by
  simp [firstRowShear, Matrix.mul_apply, add_mul, Finset.sum_add_distrib,
    ite_mul]

/-- If `w 0 = 0`, composing first-row shears with coefficients `v` and `w` gives the shear with
coefficients `v + w`. -/
theorem firstRowShear_compose {m : ℕ} (v w : Fin (m+1) → ℤ) (hw : w 0 = 0) :
    firstRowShear v * firstRowShear w = firstRowShear (v+w) := by
  ext r c
  rw [firstRowShear_mul]
  simp only [firstRowShear, Pi.add_apply]
  by_cases hc : c = 0
  · subst c
    simp [hw]
    ring
  · simp [hc, Ne.symm hc]

/-- If the first coefficient is zero, first-row shears with coefficients `v` and `-v` are mutual
inverses. -/
theorem firstRowShear_inverse {m : ℕ} (v : Fin (m+1) → ℤ) (hv : v 0 = 0) :
    firstRowShear v * firstRowShear (-v) = 1 ∧
      firstRowShear (-v) * firstRowShear v = 1 := by
  constructor
  · rw [firstRowShear_compose _ _ (by simpa using! hv), add_neg_cancel]
    ext r c
    simp [firstRowShear, Matrix.one_apply]
  · rw [firstRowShear_compose _ _ hv, neg_add_cancel]
    ext r c
    simp [firstRowShear, Matrix.one_apply]

/-- When the pivot divides every entry of its column, column clearing encodes the original
matrix, preserves the first row, and clears all entries below the pivot. -/
theorem columnClear_correct {m n : ℕ} (p : Fin n)
    (A : Matrix (Fin (m+1)) (Fin n) ℤ) (hd : ∀ r, A 0 p ∣ A r p) :
    (columnClear p A).Encodes A ∧
      (∀ c, (columnClear p A).value 0 c = A 0 c) ∧
      ∀ r : Fin m, (columnClear p A).value r.succ p = 0 := by
  have hv : columnClearCoefficients p A 0 = 0 := by simp [columnClearCoefficients]
  have hi := firstRowShear_inverse (columnClearCoefficients p A) hv
  refine ⟨⟨rfl, hi.1, hi.2⟩, ?_, ?_⟩
  · intro c
    change (firstRowShear (columnClearCoefficients p A) * A) 0 c = A 0 c
    rw [firstRowShear_mul, hv, zero_mul, add_zero]
  · intro r
    change (firstRowShear (columnClearCoefficients p A) * A) r.succ p = 0
    rw [firstRowShear_mul]
    simp only [columnClearCoefficients, Fin.succ_ne_zero, ↓reduceIte, neg_mul]
    rw [Int.ediv_mul_cancel (hd r.succ), add_neg_cancel]

/-- When the pivot divides every entry of its row, row clearing encodes the original matrix,
preserves the first column, and clears all entries to the right of the pivot. -/
theorem rowClear_correct {m n : ℕ} (p : Fin m)
    (A : Matrix (Fin m) (Fin (n+1)) ℤ) (hd : ∀ c, A p 0 ∣ A p c) :
    (rowClear p A).Encodes A ∧
      (∀ r, (rowClear p A).value r 0 = A r 0) ∧
      ∀ c : Fin n, (rowClear p A).value p c.succ = 0 := by
  have hs := columnClear_correct p A.transpose hd
  refine ⟨⟨?_, ?_, ?_⟩, hs.2.1, hs.2.2⟩
  · simpa [rowClear, Matrix.transpose_mul] using! congrArg Matrix.transpose hs.1.1
  · simpa [rowClear, Matrix.transpose_mul] using! congrArg Matrix.transpose hs.1.2.2
  · simpa [rowClear, Matrix.transpose_mul] using! congrArg Matrix.transpose hs.1.2.1

/-- The identity presentation reduction encodes its input matrix. -/
theorem PresentationReduction.identity_encodes {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    (PresentationReduction.identity A).Encodes A := by
  simp [PresentationReduction.Encodes, PresentationReduction.identity]

/-- Converting a column elimination state to a presentation reduction preserves its encoding of
the original matrix. -/
theorem ColumnEliminationState.toReduction_encodes {m n : ℕ}
    (s : ColumnEliminationState m n) (A : Matrix (Fin m) (Fin n) ℤ) (hs : s.Encodes A) :
    s.toReduction.Encodes A := by
  simpa [ColumnEliminationState.toReduction, PresentationReduction.Encodes] using! hs

/-- Converting a row elimination state to a presentation reduction preserves its encoding of the
original matrix. -/
theorem RowEliminationState.toReduction_encodes {m n : ℕ}
    (s : RowEliminationState m n) (A : Matrix (Fin m) (Fin n) ℤ) (hs : s.Encodes A) :
    s.toReduction.Encodes A := by
  simpa [RowEliminationState.toReduction, PresentationReduction.Encodes] using! hs

/-- Composing two presentation reductions preserves the encoding of the original matrix when the
second encodes the first reduced value. -/
theorem PresentationReduction.then_encodes {m n : ℕ} (s t : PresentationReduction m n)
    (A : Matrix (Fin m) (Fin n) ℤ) (hs : s.Encodes A) (ht : t.Encodes s.value) :
    (s.then t).Encodes A := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change t.value = (t.left * s.left) * A * (s.right * t.right)
    rw [ht.1, hs.1]
    simp only [Matrix.mul_assoc]
  · change (t.left * s.left) * (s.leftInverse * t.leftInverse) = 1
    calc
      _ = t.left * (s.left * s.leftInverse) * t.leftInverse := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hs.2.1, Matrix.mul_one, ht.2.1]
  · change (s.leftInverse * t.leftInverse) * (t.left * s.left) = 1
    calc
      _ = s.leftInverse * (t.leftInverse * t.left) * s.left := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ht.2.2.1, Matrix.mul_one, hs.2.2.1]
  · change (s.right * t.right) * (t.rightInverse * s.rightInverse) = 1
    calc
      _ = s.right * (t.right * t.rightInverse) * s.rightInverse := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ht.2.2.2.1, Matrix.mul_one, hs.2.2.2.1]
  · change (t.rightInverse * s.rightInverse) * (s.right * t.right) = 1
    calc
      _ = t.rightInverse * (s.rightInverse * s.right) * t.right := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hs.2.2.2.2, Matrix.mul_one, ht.2.2.2.2]

/-- The recorded left and right inverses reconstruct the original matrix from an encoding
presentation reduction. -/
theorem PresentationReduction.reconstruct {m n : ℕ} (s : PresentationReduction m n)
    (A : Matrix (Fin m) (Fin n) ℤ) (hs : s.Encodes A) :
    s.leftInverse * s.value * s.rightInverse = A := by
  calc
    _ = (s.leftInverse * s.left) * A * (s.right * s.rightInverse) := by
      rw [hs.1]
      simp only [Matrix.mul_assoc]
    _ = A := by rw [hs.2.2.1, hs.2.2.2.1, Matrix.one_mul, Matrix.mul_one]

/-- Each entry after column clearing is the original entry plus its row's clearing coefficient
times the corresponding first-row entry. -/
theorem columnClear_apply {m n : ℕ} (p : Fin n)
    (A : Matrix (Fin (m+1)) (Fin n) ℤ) (r : Fin (m+1)) (c : Fin n) :
    (columnClear p A).value r c = A r c + columnClearCoefficients p A r * A 0 c :=
  firstRowShear_mul _ _ _ _

/-- Each entry after row clearing is the original entry plus its column's clearing coefficient
times the corresponding first-column entry. -/
theorem rowClear_apply {m n : ℕ} (p : Fin m)
    (A : Matrix (Fin m) (Fin (n+1)) ℤ) (r : Fin m) (c : Fin (n+1)) :
    (rowClear p A).value r c = A r c + columnClearCoefficients p A.transpose c * A r 0 :=
  firstRowShear_mul _ _ _ _

/-- If the leading pivot divides its row and column, pivot clearing encodes the original matrix,
preserves the pivot, and clears the rest of its row and column. -/
theorem clearPivot_correct {m n : ℕ} (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ)
    (hc : ∀ r, A 0 0 ∣ A r 0) (hr : ∀ c, A 0 0 ∣ A 0 c) :
    (clearPivot A).Encodes A ∧ (clearPivot A).value 0 0 = A 0 0 ∧
      (∀ r : Fin m, (clearPivot A).value r.succ 0 = 0) ∧
      ∀ c : Fin n, (clearPivot A).value 0 c.succ = 0 := by
  have hcol := columnClear_correct (0 : Fin (n+1)) A hc
  have hrowdiv : ∀ c, (columnClear 0 A).value 0 0 ∣ (columnClear 0 A).value 0 c := by
    intro c
    rw [hcol.2.1 0, hcol.2.1 c]
    exact hr c
  have hrow := rowClear_correct (0 : Fin (m+1)) (columnClear 0 A).value hrowdiv
  refine ⟨?_, ?_, ?_, hrow.2.2⟩
  · exact PresentationReduction.then_encodes _ _ A
      (ColumnEliminationState.toReduction_encodes _ A hcol.1)
      (RowEliminationState.toReduction_encodes _ _ hrow.1)
  · change (rowClear 0 (columnClear 0 A).value).value 0 0 = A 0 0
    rw [hrow.2.1, hcol.2.1]
  · intro r
    change (rowClear 0 (columnClear 0 A).value).value r.succ 0 = 0
    rw [hrow.2.1, hcol.2.2]

/-- When the leading pivot divides its column, the residual block after pivot clearing has
entries `A r.succ c.succ - (A r.succ 0 / A 0 0) * A 0 c.succ`. -/
theorem clearPivot_residual {m n : ℕ} (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ)
    (hc : ∀ r, A 0 0 ∣ A r 0) (r : Fin m) (c : Fin n) :
    (clearPivot A).value r.succ c.succ =
      A r.succ c.succ - (A r.succ 0 / A 0 0) * A 0 c.succ := by
  change (rowClear 0 (columnClear 0 A).value).value r.succ c.succ = _
  rw [rowClear_apply, (columnClear_correct 0 A hc).2.2, mul_zero, add_zero,
    columnClear_apply]
  simp [columnClearCoefficients, sub_eq_add_neg]

/-- Exposing a row preserves the presentation reduction's encoding of the original matrix. -/
theorem exposeRow_encodes {m n : ℕ} (r : Fin (m+1))
    (A : Matrix (Fin (m+1)) (Fin n) ℤ) : (exposeRow r A).Encodes A := by
  by_cases hr : r = 0
  · simp [exposeRow, hr, ColumnEliminationState.Encodes]
  · have h01 : (0 : Fin (m+1)) ≠ r := Ne.symm hr
    have hCI : (!![1,1;0,1] : Matrix (Fin 2) (Fin 2) ℤ) * !![1,-1;0,1] = 1 := by decide
    have hIC : (!![1,-1;0,1] : Matrix (Fin 2) (Fin 2) ℤ) * !![1,1;0,1] = 1 := by decide
    simp only [exposeRow, hr, ↓reduceIte, ColumnEliminationState.Encodes]
    refine ⟨rowMix_as_left_mul _ _ _ _, ?_, ?_⟩
    · rw [← rowMix_as_left_mul, rowMix_compose _ _ h01, hCI, rowMix_one]
    · rw [← rowMix_as_left_mul, rowMix_compose _ _ h01, hIC, rowMix_one]

/-- The search for a bad pivot entry returns `none` exactly when the leading pivot divides every
matrix entry. -/
theorem badPivotEntry_none_iff {m n : ℕ} (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) :
    badPivotEntry A = none ↔ ∀ r c, A 0 0 ∣ A r c := by
  simp [badPivotEntry, List.find?_eq_none, Prod.forall]

/-- An entry returned by the bad-pivot search is not divisible by the leading pivot. -/
theorem badPivotEntry_some {m n : ℕ} (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ)
    (rc : Fin (m+1) × Fin (n+1)) (h : badPivotEntry A = some rc) :
    ¬ A 0 0 ∣ A rc.1 rc.2 := by
  have ht : decide (¬ A 0 0 ∣ A rc.1 rc.2) = true :=
    List.find?_some (p := fun rc : Fin (m+1) × Fin (n+1) => decide (¬ A 0 0 ∣ A rc.1 rc.2)) h
  exact of_decide_eq_true ht

/-- Column reduction preserves nonzeroness of the selected pivot. -/
theorem columnReduce_pivot_ne_zero {m n : ℕ} (p : Fin n)
    (A : Matrix (Fin (m+1)) (Fin n) ℤ) (h0 : A 0 p ≠ 0) :
    (columnReduce p A).value 0 p ≠ 0 := by
  intro hz
  have he := columnReduce_entry p A 0
  rw [hz, mul_zero] at he
  exact h0 he

/-- Row reduction preserves nonzeroness of the selected pivot. -/
theorem rowReduce_pivot_ne_zero {m n : ℕ} (p : Fin m)
    (A : Matrix (Fin m) (Fin (n+1)) ℤ) (h0 : A p 0 ≠ 0) :
    (rowReduce p A).value p 0 ≠ 0 := columnReduce_pivot_ne_zero p A.transpose h0

/-- If the leading pivot is isolated in its row and column, exposing a row containing a
nondivisible entry preserves the pivot and produces a nondivisible entry in its row. -/
theorem exposeRow_bad {m n : ℕ} (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ)
    (hcol : ∀ r : Fin m, A r.succ 0 = 0) (hrow : ∀ c : Fin n, A 0 c.succ = 0)
    (rc : Fin (m+1) × Fin (n+1)) (hbad : ¬ A 0 0 ∣ A rc.1 rc.2) :
    (exposeRow rc.1 A).value 0 0 = A 0 0 ∧
      ∃ c, ¬ (exposeRow rc.1 A).value 0 0 ∣ (exposeRow rc.1 A).value 0 c := by
  have htop : ∀ c, A 0 0 ∣ A 0 c := by
    intro c
    refine Fin.cases (dvd_refl _) (fun k => ?_) c
    rw [hrow k]
    exact dvd_zero _
  have hleft : ∀ r, A 0 0 ∣ A r 0 := by
    intro r
    refine Fin.cases (dvd_refl _) (fun k => ?_) r
    rw [hcol k]
    exact dvd_zero _
  have hr : rc.1 ≠ 0 := by intro h; apply hbad; rw [h]; exact htop _
  have hc : rc.2 ≠ 0 := by intro h; apply hbad; rw [h]; exact hleft _
  have hzcol : A rc.1 0 = 0 := by
    generalize hr' : rc.1 = r at hr ⊢
    refine Fin.cases (fun h => (h rfl).elim) (fun k _ => hcol k) r hr
  have hzrow : A 0 rc.2 = 0 := by
    generalize hc' : rc.2 = c at hc ⊢
    refine Fin.cases (fun h => (h rfl).elim) (fun k _ => hrow k) c hc
  have hp : (exposeRow rc.1 A).value 0 0 = A 0 0 := by
    simp [exposeRow, hr, rowMix, hzcol]
  refine ⟨hp, rc.2, ?_⟩
  rw [hp]
  simpa [exposeRow, hr, rowMix, hzrow] using! hbad

/-- The pivot-isolation loop encodes its input matrix for every fuel value. -/
theorem isolatePivotLoop_encodes {m n : ℕ} (fuel : ℕ)
    (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) : (isolatePivotLoop fuel A).Encodes A := by
  induction fuel generalizing A with
  | zero => exact PresentationReduction.identity_encodes A
  | succ fuel ih =>
    simp only [isolatePivotLoop, tableMatrix_matrixTable]
    split_ifs with hc hr
    · have hs := (clearPivot_correct A hc hr).1
      split
      · exact hs
      · exact PresentationReduction.then_encodes _ _ A hs
          (PresentationReduction.then_encodes _ _ _
            (ColumnEliminationState.toReduction_encodes _ _ (exposeRow_encodes _ _))
            (PresentationReduction.then_encodes _ _ _
              (RowEliminationState.toReduction_encodes _ _ (rowReduce_correct _ _).1) (ih _)))
    · exact PresentationReduction.then_encodes _ _ A
        (RowEliminationState.toReduction_encodes _ _ (rowReduce_correct _ _).1) (ih _)
    · exact PresentationReduction.then_encodes _ _ A
        (ColumnEliminationState.toReduction_encodes _ _ (columnReduce_correct _ _).1) (ih _)

/-- For a nonzero leading pivot and fuel exceeding its absolute value, the pivot-isolation loop
yields a nonzero isolated pivot. -/
theorem isolatePivotLoop_correct {m n : ℕ} (fuel : ℕ)
    (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) (h0 : A 0 0 ≠ 0)
    (hf : (A 0 0).natAbs < fuel) :
    (isolatePivotLoop fuel A).value 0 0 ≠ 0 ∧ PivotIsolated (isolatePivotLoop fuel A).value := by
  classical
  induction fuel generalizing A with
  | zero => exact (Nat.not_lt_zero _ hf).elim
  | succ fuel ih =>
    rw [isolatePivotLoop, tableMatrix_matrixTable]
    by_cases hc : ∀ r, A 0 0 ∣ A r 0
    · by_cases hr : ∀ c, A 0 0 ∣ A 0 c
      · have hs := clearPivot_correct A hc hr
        cases hsearch : badPivotEntry (clearPivot A).value with
        | none =>
          rw [if_pos hc, if_pos hr]
          dsimp only []
          rw [hsearch]
          refine ⟨?_, hs.2.2.1, hs.2.2.2, (badPivotEntry_none_iff _).mp hsearch⟩
          rw [hs.2.1]
          exact h0
        | some rc =>
          have he := exposeRow_bad (clearPivot A).value hs.2.2.1 hs.2.2.2 rc
            (badPivotEntry_some _ rc hsearch)
          have he0 : (exposeRow rc.1 (clearPivot A).value).value 0 0 ≠ 0 := by
            rw [he.1, hs.2.1]
            exact h0
          have hdec := rowReduce_pivot_strict 0 _ he0 he.2
          have hnext : ((rowReduce 0 (exposeRow rc.1 (clearPivot A).value).value).value 0 0).natAbs
              < fuel := by
            rw [he.1, hs.2.1] at hdec
            omega
          rw [if_pos hc, if_pos hr]
          dsimp only []
          rw [hsearch]
          dsimp only [ColumnEliminationState.toReduction, RowEliminationState.toReduction,
            PresentationReduction.then]
          exact ih _ (rowReduce_pivot_ne_zero 0 _ he0) hnext
      · have hdec := rowReduce_pivot_strict 0 A h0 (not_forall.mp hr)
        have hnext : ((rowReduce 0 A).value 0 0).natAbs < fuel := by omega
        rw [if_pos hc, if_neg hr]
        dsimp only [RowEliminationState.toReduction, PresentationReduction.then]
        exact ih _ (rowReduce_pivot_ne_zero 0 A h0) hnext
    · have hdec := columnReduce_pivot_strict 0 A h0 (not_forall.mp hc)
      have hnext : ((columnReduce 0 A).value 0 0).natAbs < fuel := by omega
      rw [if_neg hc]
      dsimp only [ColumnEliminationState.toReduction, PresentationReduction.then]
      exact ih _ (columnReduce_pivot_ne_zero 0 A h0) hnext

/-- Pivot isolation encodes the original matrix and yields a nonzero isolated pivot whenever the
initial leading pivot is nonzero. -/
theorem isolatePivot_correct {m n : ℕ} (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ)
    (h0 : A 0 0 ≠ 0) : (isolatePivot A).Encodes A ∧
      (isolatePivot A).value 0 0 ≠ 0 ∧ PivotIsolated (isolatePivot A).value :=
  ⟨isolatePivotLoop_encodes _ _, isolatePivotLoop_correct _ _ h0 (Nat.lt_succ_self _)⟩

/-- Swapping the specified row into the first position preserves the encoding of the original
matrix. -/
theorem swapRows_encodes {m n : ℕ} (r : Fin (m+1))
    (A : Matrix (Fin (m+1)) (Fin n) ℤ) : (swapRows r A).Encodes A := by
  have hmul {k : ℕ} (B : Matrix (Fin (m+1)) (Fin k) ℤ) :
      ((1 : Matrix (Fin (m+1)) (Fin (m+1)) ℤ).submatrix (Equiv.swap 0 r) id) * B =
        B.submatrix (Equiv.swap 0 r) id := by
    simpa using! Matrix.one_submatrix_mul (Equiv.swap 0 r) (Equiv.refl _) B
  have hi : (1 : Matrix (Fin (m+1)) (Fin (m+1)) ℤ).submatrix (Equiv.swap 0 r) id *
      (1 : Matrix (Fin (m+1)) (Fin (m+1)) ℤ).submatrix (Equiv.swap 0 r) id = 1 := by
    rw [hmul]
    ext i j
    change (1 : Matrix (Fin (m+1)) (Fin (m+1)) ℤ)
      (Equiv.swap 0 r (Equiv.swap 0 r i)) j = (1 : Matrix (Fin (m+1)) (Fin (m+1)) ℤ) i j
    rw [Equiv.swap_apply_self]
  exact ⟨(hmul A).symm, hi, hi⟩

/-- Swapping the specified column into the first position preserves the encoding of the original
matrix. -/
theorem swapColumns_encodes {m n : ℕ} (c : Fin (n+1))
    (A : Matrix (Fin m) (Fin (n+1)) ℤ) : (swapColumns c A).Encodes A := by
  have hs := swapRows_encodes c A.transpose
  refine ⟨?_, ?_, ?_⟩
  · simpa [swapColumns, Matrix.transpose_mul] using! congrArg Matrix.transpose hs.1
  · simpa [swapColumns, Matrix.transpose_mul] using! congrArg Matrix.transpose hs.2.2
  · simpa [swapColumns, Matrix.transpose_mul] using! congrArg Matrix.transpose hs.2.1

/-- Moving a specified entry to the leading pivot preserves the encoding of the original matrix. -/
theorem movePivot_encodes {m n : ℕ} (rc : Fin (m+1) × Fin (n+1))
    (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) : (movePivot rc A).Encodes A :=
  PresentationReduction.then_encodes _ _ A
    (ColumnEliminationState.toReduction_encodes _ _ (swapRows_encodes _ _))
    (RowEliminationState.toReduction_encodes _ _ (swapColumns_encodes _ _))

/-- After moving a specified entry to the pivot, the leading entry equals that original entry. -/
theorem movePivot_pivot {m n : ℕ} (rc : Fin (m+1) × Fin (n+1))
    (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) : (movePivot rc A).value 0 0 = A rc.1 rc.2 := by
  simp [movePivot, swapRows, swapColumns, ColumnEliminationState.toReduction,
    RowEliminationState.toReduction, PresentationReduction.then]

/-- The nonzero-entry search returns `none` exactly when the matrix is zero. -/
theorem nonzeroEntry_none_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    nonzeroEntry A = none ↔ A = 0 := by
  simp [nonzeroEntry, List.find?_eq_none, Prod.forall, Matrix.ext_iff]
  rfl

/-- An entry returned by the nonzero-entry search is nonzero. -/
theorem nonzeroEntry_some {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (rc : Fin m × Fin n) (h : nonzeroEntry A = some rc) : A rc.1 rc.2 ≠ 0 := by
  have ht : decide (A rc.1 rc.2 ≠ 0) = true :=
    List.find?_some (p := fun rc : Fin m × Fin n => decide (A rc.1 rc.2 ≠ 0)) h
  exact of_decide_eq_true ht

/-- Multiplying two pivot-block matrices multiplies their scalar pivots and their residual
blocks separately. -/
theorem pivotBlock_mul {m n k : ℕ} (a b : ℤ)
    (B : Matrix (Fin m) (Fin n) ℤ) (C : Matrix (Fin n) (Fin k) ℤ) :
    pivotBlock a B * pivotBlock b C = pivotBlock (a*b) (B*C) := by
  ext r c
  refine Fin.cases ?_ (fun i => ?_) r <;>
    refine Fin.cases ?_ (fun j => ?_) c <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, pivotBlock]

/-- The pivot block with scalar pivot one and identity residual block is the identity matrix. -/
theorem pivotBlock_one {m : ℕ} : pivotBlock 1 (1 : Matrix (Fin m) (Fin m) ℤ) = 1 := by
  ext r c
  refine Fin.cases ?_ (fun i => ?_) r <;>
    refine Fin.cases ?_ (fun j => ?_) c <;>
      simp [pivotBlock, Matrix.one_apply, eq_comm]

/-- The square of the integer pivot sign is one. -/
theorem pivotSign_square (a : ℤ) : pivotSign a * pivotSign a = 1 := by
  by_cases h : a < 0 <;> simp [pivotSign, h]

/-- Multiplying an integer by its pivot sign gives its absolute value as an integer. -/
theorem pivotSign_mul (a : ℤ) : pivotSign a * a = (a.natAbs : ℤ) := by
  by_cases h : a < 0
  · simp [pivotSign, h, abs_of_neg h]
  · simp [pivotSign, h, abs_of_nonneg (le_of_not_gt h)]

/-- Lifting a presentation reduction across a scalar pivot preserves its encoding of the
corresponding pivot-block matrix. -/
theorem PresentationReduction.lift_encodes {m n : ℕ} (a : ℤ)
    (s : PresentationReduction m n) (B : Matrix (Fin m) (Fin n) ℤ) (hs : s.Encodes B) :
    (s.lift a).Encodes (pivotBlock a B) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change pivotBlock (a.natAbs : ℤ) s.value =
      pivotBlock (pivotSign a) s.left * pivotBlock a B * pivotBlock 1 s.right
    rw [pivotBlock_mul, pivotBlock_mul, pivotSign_mul, mul_one, hs.1]
  · change pivotBlock (pivotSign a) s.left * pivotBlock (pivotSign a) s.leftInverse = 1
    rw [pivotBlock_mul, pivotSign_square, hs.2.1, pivotBlock_one]
  · change pivotBlock (pivotSign a) s.leftInverse * pivotBlock (pivotSign a) s.left = 1
    rw [pivotBlock_mul, pivotSign_square, hs.2.2.1, pivotBlock_one]
  · change pivotBlock 1 s.right * pivotBlock 1 s.rightInverse = 1
    rw [pivotBlock_mul, one_mul, hs.2.2.2.1, pivotBlock_one]
  · change pivotBlock 1 s.rightInverse * pivotBlock 1 s.right = 1
    rw [pivotBlock_mul, one_mul, hs.2.2.2.2, pivotBlock_one]

/-- A matrix whose leading row and column vanish away from the pivot equals the pivot block of
that entry and its residual submatrix. -/
theorem eq_pivotBlock_of_isolated {m n : ℕ} (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ)
    (hc : ∀ r : Fin m, A r.succ 0 = 0) (hr : ∀ c : Fin n, A 0 c.succ = 0) :
    A = pivotBlock (A 0 0) (A.submatrix Fin.succ Fin.succ) := by
  ext r c
  refine Fin.cases ?_ (fun i => ?_) r <;>
    refine Fin.cases ?_ (fun j => ?_) c <;>
      simp [pivotBlock, hc, hr]

/-- If an integer divides every entry of the left factor, it divides every entry of the matrix
product. -/
private theorem mul_entries_dvd_left {m n k : ℕ} (d : ℤ)
    (A : Matrix (Fin m) (Fin n) ℤ) (B : Matrix (Fin n) (Fin k) ℤ)
    (hd : ∀ r c, d ∣ A r c) : ∀ r c, d ∣ (A*B) r c := by
  intro r c
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left (hd r j) _

/-- If an integer divides every entry of the right factor, it divides every entry of the matrix
product. -/
private theorem mul_entries_dvd_right {m n k : ℕ} (d : ℤ)
    (A : Matrix (Fin m) (Fin n) ℤ) (B : Matrix (Fin n) (Fin k) ℤ)
    (hd : ∀ r c, d ∣ B r c) : ∀ r c, d ∣ (A*B) r c := by
  intro r c
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right (hd j c) _

/-- An encoding presentation reduction preserves the condition that a given integer divides
every matrix entry. -/
theorem PresentationReduction.dvd_entries_iff {m n : ℕ} (s : PresentationReduction m n)
    (A : Matrix (Fin m) (Fin n) ℤ) (hs : s.Encodes A) (d : ℤ) :
    (∀ r c, d ∣ A r c) ↔ ∀ r c, d ∣ s.value r c := by
  constructor
  · intro hd
    rw [hs.1]
    exact mul_entries_dvd_left d _ _ (mul_entries_dvd_right d _ _ hd)
  · intro hd
    have h := mul_entries_dvd_left d _ s.rightInverse
      (mul_entries_dvd_right d s.leftInverse _ hd)
    rwa [s.reconstruct A hs] at h

/-- Rectangular Smith reduction encodes the original integer matrix. -/
theorem rectangularSmith_encodes {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    (rectangularSmith A).Encodes A := by
  induction m generalizing n with
  | zero => exact PresentationReduction.identity_encodes A
  | succ m ih =>
    cases n with
    | zero => exact PresentationReduction.identity_encodes A
    | succ n =>
      rw [rectangularSmith, tableMatrix_matrixTable]
      cases hsearch : nonzeroEntry A with
      | none => exact PresentationReduction.identity_encodes A
      | some rc =>
        have h0 : (movePivot rc A).value 0 0 ≠ 0 := by
          rw [movePivot_pivot]
          exact nonzeroEntry_some A rc hsearch
        have hi := isolatePivot_correct (movePivot rc A).value h0
        refine PresentationReduction.then_encodes _ _ A (movePivot_encodes rc A) ?_
        refine PresentationReduction.then_encodes _ _ _ hi.1 ?_
        rw [eq_pivotBlock_of_isolated _ hi.2.2.1 hi.2.2.2.1]
        exact PresentationReduction.lift_encodes _ _ _ (ih _)

/-- The zero integer matrix is in Smith form. -/
theorem SmithForm_zero {m n : ℕ} : SmithForm (0 : Matrix (Fin m) (Fin n) ℤ) := by
  induction m generalizing n with
  | zero => trivial
  | succ m ih =>
    cases n with
    | zero => trivial
    | succ n =>
      refine ⟨by simp, by simp, by simp, by simp, ?_⟩
      simpa using! (ih (n := n))

/-- A pivot block is in Smith form when its residual block is in Smith form and its nonnegative
scalar pivot divides every residual entry. -/
theorem SmithForm_pivotBlock {m n : ℕ} (a : ℤ) (B : Matrix (Fin m) (Fin n) ℤ)
    (ha : 0 ≤ a) (hd : ∀ r c, a ∣ B r c) (hB : SmithForm B) :
    SmithForm (pivotBlock a B) := by
  refine ⟨?_, ?_, ha, ?_, ?_⟩
  · intro r; simp [pivotBlock]
  · intro c; simp [pivotBlock]
  · intro r c
    refine Fin.cases ?_ (fun i => ?_) r <;>
      refine Fin.cases ?_ (fun j => ?_) c <;> simp [pivotBlock, hd]
  · simpa [Matrix.submatrix, pivotBlock] using! hB

/-- The value produced by rectangular Smith reduction is in Smith form. -/
theorem rectangularSmith_form {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    SmithForm (rectangularSmith A).value := by
  induction m generalizing n with
  | zero => trivial
  | succ m ih =>
    cases n with
    | zero => trivial
    | succ n =>
      rw [rectangularSmith, tableMatrix_matrixTable]
      cases hsearch : nonzeroEntry A with
      | none =>
        change SmithForm A
        rw [(nonzeroEntry_none_iff A).mp hsearch]
        exact SmithForm_zero
      | some rc =>
        have h0 : (movePivot rc A).value 0 0 ≠ 0 := by
          rw [movePivot_pivot]
          exact nonzeroEntry_some A rc hsearch
        have hi := isolatePivot_correct (movePivot rc A).value h0
        let B := (isolatePivot (movePivot rc A).value).value
        let R := B.submatrix Fin.succ Fin.succ
        change SmithForm (pivotBlock ((B 0 0).natAbs : ℤ) (rectangularSmith R).value)
        apply SmithForm_pivotBlock _ _ (Int.natCast_nonneg _)
        · have hd : ∀ r c, B 0 0 ∣ R r c := fun r c => hi.2.2.2.2 r.succ c.succ
          have hnew := (PresentationReduction.dvd_entries_iff _ R
            (rectangularSmith_encodes R) (B 0 0)).mp hd
          exact fun r c => Int.natAbs_dvd.mpr (hnew r c)
        · exact ih R

/-- Right multiplication by a matrix possessing a right inverse preserves the range of the
matrix-vector linear map. -/
theorem mulVecLin_range_right {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (R RI : Matrix (Fin n) (Fin n) ℤ) (hR : R*RI = 1) :
    LinearMap.range (A*R).mulVecLin = LinearMap.range A.mulVecLin := by
  apply le_antisymm
  · rw [Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · have he : (A*R)*RI = A := by rw [Matrix.mul_assoc, hR, Matrix.mul_one]
    calc
      LinearMap.range A.mulVecLin = LinearMap.range ((A*R)*RI).mulVecLin :=
        congrArg (fun B => LinearMap.range B.mulVecLin) he.symm
      _ ≤ _ := by
        rw [Matrix.mulVecLin_mul]
        exact LinearMap.range_comp_le_range _ _

/-- The integer-linear equivalence of presentation modules induced by an encoding presentation
reduction. -/
def PresentationReduction.quotientEquiv {m n : ℕ} (s : PresentationReduction m n)
    (A : Matrix (Fin m) (Fin n) ℤ) (hs : s.Encodes A) :
    PresentationModule A ≃ₗ[ℤ] PresentationModule s.value := by
  let e : (Fin m → ℤ) ≃ₗ[ℤ] (Fin m → ℤ) :=
    Matrix.toLin'OfInv (M := s.leftInverse) (M' := s.left) hs.2.2.1 hs.2.1
  apply Submodule.Quotient.equiv (LinearMap.range A.mulVecLin) (LinearMap.range s.value.mulVecLin) e
  change (LinearMap.range A.mulVecLin).map s.left.mulVecLin = LinearMap.range s.value.mulVecLin
  rw [← LinearMap.range_comp, ← Matrix.mulVecLin_mul, hs.1,
    mulVecLin_range_right _ _ _ hs.2.2.2.1]

/-- On quotient representatives, the equivalence induced by a presentation reduction applies its
recorded left transformation. -/
theorem PresentationReduction.quotientEquiv_mk {m n : ℕ} (s : PresentationReduction m n)
    (A : Matrix (Fin m) (Fin n) ℤ) (hs : s.Encodes A) (v : Fin m → ℤ) :
    s.quotientEquiv A hs (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (s.left *ᵥ v) := rfl

/-- On quotient representatives, the inverse equivalence induced by a presentation reduction
applies its recorded left inverse. -/
theorem PresentationReduction.quotientEquiv_symm_mk {m n : ℕ} (s : PresentationReduction m n)
    (A : Matrix (Fin m) (Fin n) ℤ) (hs : s.Encodes A) (v : Fin m → ℤ) :
    (s.quotientEquiv A hs).symm (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (s.leftInverse *ᵥ v) := rfl

/-- The integer-linear equivalence from the original presentation module to the presentation
module of its computed Smith form. -/
def rectangularSmithQuotientEquiv {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    PresentationModule A ≃ₗ[ℤ] PresentationModule (rectangularSmith A).value :=
  (rectangularSmith A).quotientEquiv A (rectangularSmith_encodes A)

/-- The diagonal list of an `m` by `n` matrix has length `min m n`. -/
theorem diagonalList_length {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    (diagonalList A).length = min m n := by
  induction m generalizing n with
  | zero => simp [diagonalList]
  | succ m ih =>
    cases n with
    | zero => simp [diagonalList]
    | succ n => simp [diagonalList, ih, Nat.succ_min_succ]

/-- An integer dividing every matrix entry divides every member of its diagonal list. -/
theorem diagonalList_dvd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (d : ℤ)
    (hd : ∀ r c, d ∣ A r c) : ∀ a ∈ diagonalList A, d ∣ a := by
  induction m generalizing n with
  | zero => simp [diagonalList]
  | succ m ih =>
    cases n with
    | zero => simp [diagonalList]
    | succ n =>
      simp only [diagonalList, List.mem_cons, forall_eq_or_imp]
      exact ⟨hd 0 0, ih _ (fun r c => hd r.succ c.succ)⟩

/-- Every entry in the diagonal list of a Smith-form matrix is nonnegative. -/
theorem SmithForm_diagonalList_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : SmithForm A) : ∀ a ∈ diagonalList A, 0 ≤ a := by
  induction m generalizing n with
  | zero => simp [diagonalList]
  | succ m ih =>
    cases n with
    | zero => simp [diagonalList]
    | succ n =>
      simp only [diagonalList, List.mem_cons, forall_eq_or_imp]
      exact ⟨hA.2.2.1, ih _ hA.2.2.2.2⟩

/-- The diagonal list of a Smith-form matrix is a divisibility chain. -/
theorem SmithForm_diagonalList_chain {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : SmithForm A) : (diagonalList A).Pairwise (· ∣ ·) := by
  induction m generalizing n with
  | zero => simp [diagonalList]
  | succ m ih =>
    cases n with
    | zero => simp [diagonalList]
    | succ n =>
      rw [diagonalList, List.pairwise_cons]
      exact ⟨diagonalList_dvd _ _ (fun r c => hA.2.2.2.1 r.succ c.succ),
        ih _ hA.2.2.2.2⟩

/-- The list of Smith factors of an `m` by `n` matrix has length `min m n`. -/
theorem smithFactors_length {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    (smithFactors A).length = min m n := by
  simp [smithFactors, diagonalList_length]

/-- The Smith factors form a divisibility chain. -/
theorem smithFactors_chain {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    (smithFactors A).Pairwise (· ∣ ·) := by
  rw [smithFactors, List.pairwise_map]
  exact (SmithForm_diagonalList_chain _ (rectangularSmith_form A)).imp
    fun h => Int.natAbs_dvd_natAbs.mpr h

/-- An entry of a Smith-form matrix vanishes when its row and column have different numeric
indices. -/
theorem SmithForm_offDiagonal {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : SmithForm A) (r : Fin m) (c : Fin n) : r.val ≠ c.val → A r c = 0 := by
  induction m generalizing n with
  | zero => exact Fin.elim0 r
  | succ m ih =>
    cases n with
    | zero => exact Fin.elim0 c
    | succ n =>
      refine Fin.cases ?_ (fun i => ?_) r <;> refine Fin.cases ?_ (fun j => ?_) c
      · intro h; exact (h rfl).elim
      · intro _; exact hA.2.1 _
      · intro _; exact hA.1 _
      · intro h
        exact ih _ hA.2.2.2.2 i j (by simpa using! h)

/-- Matrix-vector multiplication by a Smith-form matrix multiplies matching coordinates by their
diagonal entries and is zero on rows beyond the column range. -/
theorem SmithForm_mulVec_coordinate {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : SmithForm A) (v : Fin n → ℤ) (r : Fin m) :
    (A *ᵥ v) r = if h : r.val < n then A r ⟨r.val,h⟩ * v ⟨r.val,h⟩ else 0 := by
  change (∑ c, A r c * v c) = _
  split_ifs with h
  · apply Finset.sum_eq_single (⟨r.val,h⟩ : Fin n)
    · intro c _ hc
      have hne : r.val ≠ c.val := by
        intro he
        apply hc
        exact Fin.ext he.symm
      rw [SmithForm_offDiagonal A hA r c hne, zero_mul]
    · intro hc
      exact (hc (Finset.mem_univ _)).elim
  · apply Finset.sum_eq_zero
    intro c _
    rw [SmithForm_offDiagonal A hA r c (by omega), zero_mul]

/-- A vector lies in the range of a Smith-form matrix exactly when each coordinate is divisible
by the corresponding diagonal coefficient. -/
theorem SmithForm_mem_range_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : SmithForm A) (v : Fin m → ℤ) :
    v ∈ LinearMap.range A.mulVecLin ↔ ∀ r, diagonalCoefficient A r ∣ v r := by
  constructor
  · rintro ⟨w, rfl⟩ r
    change diagonalCoefficient A r ∣ (A *ᵥ w) r
    rw [SmithForm_mulVec_coordinate A hA]
    split_ifs with h
    · simpa only [diagonalCoefficient, h, ↓reduceDIte] using!
        dvd_mul_right (A r ⟨r.val,h⟩) (w ⟨r.val,h⟩)
    · exact dvd_zero _
  · intro hd
    refine ⟨diagonalRelationCoefficients A v, ?_⟩
    ext r
    change (A *ᵥ diagonalRelationCoefficients A v) r = v r
    rw [SmithForm_mulVec_coordinate A hA]
    split_ifs with h
    · simp only [diagonalRelationCoefficients, r.isLt, ↓reduceDIte]
      exact Int.mul_ediv_cancel_of_dvd (by simpa [diagonalCoefficient, h] using! hd r)
    · have hz : v r = 0 := by simpa [diagonalCoefficient, h] using! hd r
      exact hz.symm

/-- The range of a Smith-form matrix is the product of the principal integer ideals generated by
its diagonal coefficients. -/
theorem SmithForm_range {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : SmithForm A) :
    LinearMap.range A.mulVecLin = Submodule.pi Set.univ
      (fun r => (Ideal.span ({diagonalCoefficient A r} : Set ℤ) : Submodule ℤ ℤ)) := by
  ext v
  rw [SmithForm_mem_range_iff A hA]
  simp [Submodule.mem_pi, Ideal.mem_span_singleton]

/-- The additive equivalence between a Smith-form presentation module and the product of `ZMod`
groups given by the absolute diagonal coefficients. -/
def SmithForm.cyclicEquiv {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : SmithForm A) :
    PresentationModule A ≃+ (∀ r : Fin m, ZMod (diagonalCoefficient A r).natAbs) := by
  let I : Fin m → Submodule ℤ ℤ :=
    fun r => Ideal.span ({diagonalCoefficient A r} : Set ℤ)
  let e : PresentationModule A ≃ₗ[ℤ] (∀ r : Fin m, ℤ ⧸ I r) :=
    (Submodule.quotEquivOfEq _ _ (SmithForm_range A hA)).trans (Submodule.quotientPi I)
  exact e.toAddEquiv.trans
    (AddEquiv.piCongrRight fun r => (Int.quotientSpanEquivZMod (diagonalCoefficient A r)).toAddEquiv)

/-- The cyclic-coordinate equivalence for a Smith-form matrix sends a quotient representative to
its coordinatewise residue classes. -/
theorem SmithForm.cyclicEquiv_mk {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : SmithForm A) (v : Fin m → ℤ) (r : Fin m) :
    SmithForm.cyclicEquiv A hA (Submodule.Quotient.mk v) r =
      (v r : ZMod (diagonalCoefficient A r).natAbs) := rfl

/-- The additive equivalence from an integer presentation module to the product of cyclic groups
specified by its computed Smith coefficients. -/
def rectangularSmithCyclicEquiv {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    PresentationModule A ≃+ (∀ r : Fin m, ZMod (cyclicFactors A r)) :=
  (rectangularSmithQuotientEquiv A).toAddEquiv.trans
    (SmithForm.cyclicEquiv (rectangularSmith A).value (rectangularSmith_form A))

/-- The cyclic coordinates of a quotient representative are the residues of its image under the
Smith reduction's left transformation. -/
theorem rectangularSmithCyclicEquiv_mk {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (v : Fin m → ℤ) (r : Fin m) :
    rectangularSmithCyclicEquiv A (Submodule.Quotient.mk v) r =
      (((rectangularSmith A).left *ᵥ v) r : ZMod (cyclicFactors A r)) := rfl

/-- The inverse cyclic-coordinate equivalence sends an integer vector's residue classes to the
quotient class of its image under the recorded left inverse. -/
theorem rectangularSmithCyclicEquiv_symm_cast {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (v : Fin m → ℤ) :
    (rectangularSmithCyclicEquiv A).symm (fun r => (v r : ZMod (cyclicFactors A r))) =
      Submodule.Quotient.mk ((rectangularSmith A).leftInverse *ᵥ v) := by
  apply (rectangularSmithCyclicEquiv A).injective
  rw [AddEquiv.apply_symm_apply]
  ext r
  rw [rectangularSmithCyclicEquiv_mk, Matrix.mulVec_mulVec,
    (rectangularSmith_encodes A).2.1, Matrix.one_mulVec]

/-- An integer presentation module is finite exactly when all its cyclic factors are nonzero. -/
theorem finite_presentation_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    Finite (PresentationModule A) ↔ ∀ r, cyclicFactors A r ≠ 0 := by
  classical
  constructor
  · intro hA
    letI := hA
    letI : Finite (∀ r : Fin m, ZMod (cyclicFactors A r)) :=
      Finite.of_equiv (PresentationModule A) (rectangularSmithCyclicEquiv A).toEquiv
    intro r hz
    have hp : Function.Surjective (fun v : (∀ i : Fin m, ZMod (cyclicFactors A i)) => v r) := by
      intro x
      exact ⟨Function.update (fun _ => 0) r x, by simp⟩
    have hf : Finite (ZMod (cyclicFactors A r)) := Finite.of_surjective _ hp
    have hf0 : Finite (ZMod 0) := by simpa [hz] using! hf
    exact hf0.false
  · intro h
    letI (r : Fin m) : NeZero (cyclicFactors A r) := ⟨h r⟩
    letI : ∀ r : Fin m, Finite (ZMod (cyclicFactors A r)) := fun _ => inferInstance
    exact Finite.of_equiv (∀ r : Fin m, ZMod (cyclicFactors A r))
      (rectangularSmithCyclicEquiv A).symm.toEquiv

/-- The natural cardinality of an integer presentation module equals the product of its cyclic
factors. -/
theorem presentation_card {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    Nat.card (PresentationModule A) = ∏ r, cyclicFactors A r := by
  rw [Nat.card_congr (rectangularSmithCyclicEquiv A).toEquiv, Nat.card_pi]
  simp [Nat.card_zmod]

/-- The cyclic-coordinate equivalence sends `smithGenerator A r` to the vector with one in
coordinate `r` and zero elsewhere. -/
theorem rectangularSmithCyclicEquiv_generator {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (r : Fin m) : rectangularSmithCyclicEquiv A (smithGenerator A r) = Pi.single r 1 := by
  ext i
  rw [smithGenerator, rectangularSmithCyclicEquiv_mk, Matrix.mulVec_mulVec,
    (rectangularSmith_encodes A).2.1, Matrix.one_mulVec]
  by_cases hi : i = r
  · subst i; simp
  · simp [hi]

/-- The determinant of a matrix product expands as a sum over column selections of the left
factor, weighted by the corresponding entries of the right factor. -/
theorem det_mul_columns {k l : ℕ} (M : Matrix (Fin k) (Fin l) ℤ)
    (N : Matrix (Fin l) (Fin k) ℤ) :
    (M*N).det = ∑ p : Fin k → Fin l, (M.submatrix id p).det * ∏ i, N (p i) i := by
  classical
  simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
    Finset.mul_sum, Fintype.piFinset_univ, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro σ _
  simp [Matrix.submatrix_apply, Finset.prod_mul_distrib, mul_assoc]

/-- Divisibility of all minors of a fixed size is invariant under transposition. -/
theorem MinorsDivisible.transpose_iff {m n : ℕ} (k : ℕ) (d : ℤ)
    (A : Matrix (Fin m) (Fin n) ℤ) : MinorsDivisible k d A.transpose ↔ MinorsDivisible k d A := by
  constructor <;> intro h rows cols
  · simpa only [← Matrix.transpose_submatrix, Matrix.det_transpose] using! h cols rows
  · simpa only [← Matrix.transpose_submatrix, Matrix.det_transpose] using! h cols rows

/-- Divisibility of all minors of a fixed size is preserved by right multiplication. -/
theorem MinorsDivisible.mul_right {m n p : ℕ} (k : ℕ) (d : ℤ)
    (A : Matrix (Fin m) (Fin n) ℤ) (B : Matrix (Fin n) (Fin p) ℤ)
    (hd : MinorsDivisible k d A) : MinorsDivisible k d (A*B) := by
  classical
  intro rows cols
  have he : (A*B).submatrix rows cols = A.submatrix rows id * B.submatrix id cols := by
    simpa using! Matrix.submatrix_mul A B rows (Equiv.refl _) cols (Equiv.refl _).bijective
  rw [he, det_mul_columns]
  exact Finset.dvd_sum fun f _ => dvd_mul_of_dvd_left (hd rows f) _

/-- Divisibility of all minors of a fixed size is preserved by left multiplication. -/
theorem MinorsDivisible.mul_left {m n p : ℕ} (k : ℕ) (d : ℤ)
    (A : Matrix (Fin m) (Fin n) ℤ) (B : Matrix (Fin n) (Fin p) ℤ)
    (hd : MinorsDivisible k d B) : MinorsDivisible k d (A*B) := by
  apply (MinorsDivisible.transpose_iff k d (A*B)).mp
  rw [Matrix.transpose_mul]
  exact MinorsDivisible.mul_right k d B.transpose A.transpose
    ((MinorsDivisible.transpose_iff k d B).mpr hd)

/-- An encoding presentation reduction preserves divisibility of all minors of any fixed size by
a given integer. -/
theorem PresentationReduction.minors_iff {m n : ℕ} (s : PresentationReduction m n)
    (A : Matrix (Fin m) (Fin n) ℤ) (hs : s.Encodes A) (k : ℕ) (d : ℤ) :
    MinorsDivisible k d A ↔ MinorsDivisible k d s.value := by
  constructor
  · intro hd
    rw [hs.1]
    exact MinorsDivisible.mul_right k d _ s.right (MinorsDivisible.mul_left k d s.left A hd)
  · intro hd
    have h := MinorsDivisible.mul_right k d _ s.rightInverse
      (MinorsDivisible.mul_left k d s.leftInverse s.value hd)
    rwa [s.reconstruct A hs] at h

/-- A successor-index diagonal coefficient equals the corresponding coefficient of the residual
submatrix. -/
theorem diagonalCoefficient_succ {m n : ℕ} (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ)
    (r : Fin m) :
    diagonalCoefficient A r.succ = diagonalCoefficient (A.submatrix Fin.succ Fin.succ) r := by
  simp only [diagonalCoefficient, Fin.val_succ, Nat.add_lt_add_iff_right]
  split_ifs <;> rfl

/-- Every diagonal coefficient of a Smith-form matrix is nonnegative. -/
theorem SmithForm_coefficient_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : SmithForm A) (r : Fin m) : 0 ≤ diagonalCoefficient A r := by
  induction m generalizing n with
  | zero => exact Fin.elim0 r
  | succ m ih =>
    cases n with
    | zero => simp [diagonalCoefficient]
    | succ n =>
      refine Fin.cases ?_ (fun i => ?_) r
      · simpa [diagonalCoefficient] using! hA.2.2.1
      · rw [diagonalCoefficient_succ]
        exact ih _ hA.2.2.2.2 _

/-- The diagonal coefficients of a Smith-form matrix form a divisibility chain in their index
order. -/
theorem SmithForm_coefficient_chain {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : SmithForm A) (r s : Fin m) : r ≤ s → diagonalCoefficient A r ∣ diagonalCoefficient A s := by
  induction m generalizing n with
  | zero => exact Fin.elim0 r
  | succ m ih =>
    cases n with
    | zero => simp [diagonalCoefficient]
    | succ n =>
      refine Fin.cases ?_ (fun i => ?_) r <;> refine Fin.cases ?_ (fun j => ?_) s
      · intro _; exact dvd_refl _
      · intro _
        simp only [diagonalCoefficient, Fin.val_zero, Nat.zero_lt_succ, ↓reduceDIte]
        split_ifs with h
        · exact hA.2.2.2.1 _ _
        · exact dvd_zero _
      · intro h
        have hval : i.val + 1 ≤ 0 := by
          simpa only [Fin.le_def, Fin.val_succ, Fin.val_zero] using! h
        omega
      · intro h
        rw [diagonalCoefficient_succ, diagonalCoefficient_succ]
        exact ih _ hA.2.2.2.2 i j (by simpa using! h)

/-- Every diagonal prefix product of a Smith-form matrix is nonnegative. -/
theorem diagonalPrefix_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : SmithForm A) (k : ℕ) (h : k ≤ m) : 0 ≤ diagonalPrefix A k h := by
  exact Finset.prod_nonneg fun _ _ => SmithForm_coefficient_nonneg A hA _

/-- A strictly increasing map between finite index types sends each index to an index with at
least its numeric value. -/
private theorem strictMono_fin_index_le {k m : ℕ} (f : Fin k → Fin m)
    (hf : StrictMono f) (i : Fin k) : i.val ≤ (f i).val := by
  have h : ∀ a, ∀ ha : a < k, a ≤ (f ⟨a,ha⟩).val := by
    intro a
    induction a with
    | zero => intro _; exact Nat.zero_le _
    | succ a ih =>
      intro ha
      have ha0 : a < k := by omega
      have hprev := ih ha0
      have hstep : (f ⟨a,ha0⟩).val < (f ⟨a+1,ha⟩).val := hf (by simp)
      omega
  exact h i.val i.isLt

/-- In a divisibility chain, the product of the first `k` terms divides the product along any
injective selection of `k` indices. -/
theorem chain_prefix_dvd_selection {m k : ℕ} (d : Fin m → ℤ)
    (hd : ∀ i j, i ≤ j → d i ∣ d j) (hk : k ≤ m)
    (f : Fin k → Fin m) (hf : Function.Injective f) :
    (∏ i : Fin k, d (initialIndex hk i)) ∣ ∏ i, d (f i) := by
  classical
  let S := Finset.univ.image f
  have hcard : S.card = k := by simp [S, Finset.card_image_of_injective _ hf]
  let g := S.orderEmbOfFin hcard
  have hgprod : (∏ i : Fin k, d (g i)) = ∏ i, d (f i) := by
    calc
      _ = ∏ j ∈ Finset.univ.image g, d j := (Finset.prod_image g.injective.injOn).symm
      _ = ∏ j ∈ S, d j := by rw [S.image_orderEmbOfFin_univ hcard]
      _ = _ := Finset.prod_image hf.injOn
  rw [← hgprod]
  exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ =>
    hd _ _ (strictMono_fin_index_le g g.strictMono i)

/-- Each diagonal coefficient of a Smith-form matrix divides every entry in its row. -/
theorem SmithForm_coefficient_dvd_entry {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : SmithForm A) (r : Fin m) (c : Fin n) : diagonalCoefficient A r ∣ A r c := by
  by_cases he : r.val = c.val
  · have hr : r.val < n := he ▸ c.isLt
    have hc : (⟨r.val,hr⟩ : Fin n) = c := Fin.ext he
    simp [diagonalCoefficient, hr, hc]
  · rw [SmithForm_offDiagonal A hA r c he]
    exact dvd_zero _

/-- The product of the first `k` diagonal coefficients of a Smith-form matrix divides every `k`
by `k` submatrix determinant. -/
theorem SmithForm_prefix_dvd_minor {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : SmithForm A) (hk : k ≤ m) (rows : Fin k → Fin m) (cols : Fin k → Fin n) :
    diagonalPrefix A k hk ∣ (A.submatrix rows cols).det := by
  classical
  by_cases hr : Function.Injective rows
  · have hp := chain_prefix_dvd_selection (diagonalCoefficient A)
      (SmithForm_coefficient_chain A hA) hk rows hr
    rw [Matrix.det_apply']
    apply Finset.dvd_sum
    intro σ _
    have hterms : (∏ i, diagonalCoefficient A (rows (σ i))) ∣
        ∏ i, A (rows (σ i)) (cols i) :=
      Finset.prod_dvd_prod_of_dvd _ _ fun i _ => SmithForm_coefficient_dvd_entry A hA _ _
    rw [Equiv.prod_comp (σ : Fin k ≃ Fin k) (fun i => diagonalCoefficient A (rows i))] at hterms
    exact dvd_mul_of_dvd_right (hp.trans hterms) _
  · simp only [Function.Injective] at hr
    push Not at hr
    obtain ⟨i,j,he,hne⟩ := hr
    rw [Matrix.det_zero_of_row_eq (M := A.submatrix rows cols) hne (by
      funext c
      exact congrArg (fun r => A r (cols c)) he)]
    exact dvd_zero _

/-- The determinant of the leading `k` by `k` submatrix of a Smith-form matrix is its `k`th
diagonal prefix product. -/
theorem SmithForm_principal_det {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : SmithForm A) (hm : k ≤ m) (hn : k ≤ n) :
    (A.submatrix (initialIndex hm) (initialIndex hn)).det = diagonalPrefix A k hm := by
  have he : A.submatrix (initialIndex hm) (initialIndex hn) =
      Matrix.diagonal (fun i => diagonalCoefficient A (initialIndex hm i)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [diagonalCoefficient, initialIndex, lt_of_lt_of_le i.isLt hn]
    · simp only [Matrix.diagonal_apply, if_neg hij, Matrix.submatrix_apply]
      exact SmithForm_offDiagonal A hA _ _ (by intro h; exact hij (Fin.ext h))
  rw [he, Matrix.det_diagonal]
  rfl

/-- For an available minor size, an integer divides all minors of a Smith-form matrix exactly
when it divides the corresponding diagonal prefix product. -/
theorem SmithForm_minors_iff {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : SmithForm A) (hm : k ≤ m) (hn : k ≤ n) (d : ℤ) :
    MinorsDivisible k d A ↔ d ∣ diagonalPrefix A k hm := by
  constructor
  · intro hd
    simpa only [SmithForm_principal_det A hA hm hn] using! hd (initialIndex hm) (initialIndex hn)
  · intro hd rows cols
    exact hd.trans (SmithForm_prefix_dvd_minor A hA hm rows cols)

/-- The next diagonal prefix product is the previous prefix product times the next diagonal
coefficient. -/
theorem diagonalPrefix_succ {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (k : ℕ) (hk : k+1 ≤ m) :
    diagonalPrefix A (k+1) hk = diagonalPrefix A k (by omega) *
      diagonalCoefficient A ⟨k, by omega⟩ := by
  exact Fin.prod_univ_castSucc (fun i => diagonalCoefficient A (initialIndex hk i))

/-- If a diagonal prefix product of a Smith-form matrix vanishes, every diagonal coefficient at
or beyond that prefix length is zero. -/
theorem SmithForm_prefix_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : SmithForm A) (k : ℕ) (hk : k ≤ m) (r : Fin m) (hr : k ≤ r.val)
    (hz : diagonalPrefix A k hk = 0) : diagonalCoefficient A r = 0 := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hz
  have hd := SmithForm_coefficient_chain A hA (initialIndex hk i) r
    (show (initialIndex hk i).val ≤ r.val from (Nat.le_of_lt i.isLt).trans hr)
  simpa only [hi, zero_dvd_iff] using! hd

/-- Two encoding reductions of the same matrix into Smith form have equal diagonal prefix
products for every available minor size. -/
theorem smith_prefix_unique {m n k : ℕ} (s t : PresentationReduction m n)
    (A : Matrix (Fin m) (Fin n) ℤ) (hs : s.Encodes A) (ht : t.Encodes A)
    (hS : SmithForm s.value) (hT : SmithForm t.value) (hm : k ≤ m) (hn : k ≤ n) :
    diagonalPrefix s.value k hm = diagonalPrefix t.value k hm := by
  have he (d : ℤ) : d ∣ diagonalPrefix s.value k hm ↔ d ∣ diagonalPrefix t.value k hm :=
    (SmithForm_minors_iff s.value hS hm hn d).symm.trans
      ((s.minors_iff A hs k d).symm.trans
        ((t.minors_iff A ht k d).trans (SmithForm_minors_iff t.value hT hm hn d)))
  exact Int.dvd_antisymm (diagonalPrefix_nonneg s.value hS k hm)
    (diagonalPrefix_nonneg t.value hT k hm)
    ((he _).mp (dvd_refl _)) ((he _).mpr (dvd_refl _))

/-- Two encoding reductions of the same matrix into Smith form have identical reduced matrices. -/
theorem smith_value_unique {m n : ℕ} (s t : PresentationReduction m n)
    (A : Matrix (Fin m) (Fin n) ℤ) (hs : s.Encodes A) (ht : t.Encodes A)
    (hS : SmithForm s.value) (hT : SmithForm t.value) : s.value = t.value := by
  ext r c
  by_cases he : r.val = c.val
  · have hrn : r.val < n := he ▸ c.isLt
    have hm : r.val ≤ m := Nat.le_of_lt r.isLt
    have hn : r.val ≤ n := Nat.le_of_lt hrn
    have hm1 : r.val+1 ≤ m := Nat.succ_le_of_lt r.isLt
    have hn1 : r.val+1 ≤ n := Nat.succ_le_of_lt hrn
    have hp := smith_prefix_unique s t A hs ht hS hT hm hn
    have hp1 := smith_prefix_unique s t A hs ht hS hT hm1 hn1
    have hcoeff : diagonalCoefficient s.value r = diagonalCoefficient t.value r := by
      by_cases hz : diagonalPrefix s.value r.val hm = 0
      · have hzt : diagonalPrefix t.value r.val hm = 0 := by rw [← hp]; exact hz
        rw [SmithForm_prefix_zero s.value hS _ hm r le_rfl hz,
          SmithForm_prefix_zero t.value hT _ hm r le_rfl hzt]
      · have hps : diagonalPrefix s.value (r.val+1) hm1 =
            diagonalPrefix s.value r.val hm * diagonalCoefficient s.value r :=
          diagonalPrefix_succ s.value r.val hm1
        have hpt : diagonalPrefix t.value (r.val+1) hm1 =
            diagonalPrefix t.value r.val hm * diagonalCoefficient t.value r :=
          diagonalPrefix_succ t.value r.val hm1
        rw [hps, hpt, ← hp] at hp1
        exact mul_left_cancel₀ hz hp1
    have hc : (⟨r.val,hrn⟩ : Fin n) = c := Fin.ext he
    simpa [diagonalCoefficient, hrn, hc] using! hcoeff
  · rw [SmithForm_offDiagonal s.value hS r c he, SmithForm_offDiagonal t.value hT r c he]

/-- Any encoding reduction into Smith form has the same value as `rectangularSmith`. -/
theorem rectangularSmith_unique {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (s : PresentationReduction m n) (hs : s.Encodes A) (hS : SmithForm s.value) :
    s.value = (rectangularSmith A).value :=
  smith_value_unique s (rectangularSmith A) A hs (rectangularSmith_encodes A)
    hS (rectangularSmith_form A)

/-- The absolute diagonal entries of any encoding Smith-form reduction equal the computed Smith
factors. -/
theorem smithFactors_unique {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (s : PresentationReduction m n) (hs : s.Encodes A) (hS : SmithForm s.value) :
    (diagonalList s.value).map Int.natAbs = smithFactors A := by
  rw [rectangularSmith_unique A s hs hS]
  rfl

/-- The cyclic-coordinate equivalence applied to a quotient representative agrees with
`smithEncode`. -/
theorem smithEncode_sound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (v : Fin m → ℤ) :
    rectangularSmithCyclicEquiv A (Submodule.Quotient.mk v) = smithEncode A v := rfl

/-- Encoding a decoded cyclic-coordinate vector returns that vector. -/
theorem smithEncode_decode {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (z : ∀ r : Fin m, ZMod (cyclicFactors A r)) : smithEncode A (smithDecode A z) = z := by
  ext r
  change (((rectangularSmith A).left *ᵥ
    ((rectangularSmith A).leftInverse *ᵥ (fun i => (ZMod.cast (z i) : ℤ)))) r :
      ZMod (cyclicFactors A r)) = z r
  rw [Matrix.mulVec_mulVec, (rectangularSmith_encodes A).2.1, Matrix.one_mulVec]
  exact ZMod.intCast_zmod_cast (z r)

/-- The quotient class of a decoded cyclic-coordinate vector is its image under the inverse
cyclic-coordinate equivalence. -/
theorem smithDecode_sound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (z : ∀ r : Fin m, ZMod (cyclicFactors A r)) :
    Submodule.Quotient.mk (smithDecode A z) = (rectangularSmithCyclicEquiv A).symm z := by
  apply (rectangularSmithCyclicEquiv A).injective
  rw [smithEncode_sound, smithEncode_decode, AddEquiv.apply_symm_apply]

/-- Decoding an encoded integer vector preserves its class in the presentation module. -/
theorem smithDecode_encode {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (v : Fin m → ℤ) :
    Submodule.Quotient.mk (smithDecode A (smithEncode A v)) =
      (Submodule.Quotient.mk v : PresentationModule A) := by
  rw [smithDecode_sound, ← smithEncode_sound, AddEquiv.symm_apply_apply]

/-- Smith coordinate encoding preserves addition of integer vectors. -/
theorem smithEncode_add {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (u v : Fin m → ℤ) :
    smithEncode A (u+v) = smithEncode A u + smithEncode A v := by
  ext r
  simp [smithEncode, Matrix.mulVec_add]

/-- Two integer vectors have the same Smith encoding exactly when their difference lies in the
relation matrix's range. -/
theorem smithEncode_eq_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (u v : Fin m → ℤ) :
    smithEncode A u = smithEncode A v ↔ u-v ∈ LinearMap.range A.mulVecLin := by
  have he : smithEncode A u = smithEncode A v ↔
      (Submodule.Quotient.mk u : PresentationModule A) = Submodule.Quotient.mk v := by
    rw [← smithEncode_sound A u, ← smithEncode_sound A v]
    exact (rectangularSmithCyclicEquiv A).injective.eq_iff
  exact he.trans (Submodule.Quotient.eq _)

/-- The Smith word-equality test returns `true` exactly when the difference of its inputs lies
in the relation matrix's range. -/
theorem smithWordEq_true_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (u v : Fin m → ℤ) :
    smithWordEq A u v = true ↔ u-v ∈ LinearMap.range A.mulVecLin := by
  constructor
  · intro h
    have hc : ∀ r, smithEncode A u r = smithEncode A v r := of_decide_eq_true h
    exact (smithEncode_eq_iff A u v).mp (funext hc)
  · intro h
    have hc : ∀ r, smithEncode A u r = smithEncode A v r :=
      congrFun ((smithEncode_eq_iff A u v).mpr h)
    simpa only [smithWordEq, decide_eq_true_eq] using! hc

/-- The normalized Smith coefficient at each index equals the corresponding cyclic factor of the
table matrix. -/
@[simp] theorem normalizedSmith_coeff {m n : ℕ} (rows : Vector (Vector ℤ n) m) (r : Fin m) :
    (normalizedSmith rows).coeff r = cyclicFactors (tableMatrix rows) r := by
  simp [normalizedSmith, NormalizedSmithData.coeff, cyclicFactors]

/-- The reduction stored in normalized Smith data is the rectangular Smith reduction of the
input table matrix. -/
@[simp] theorem normalizedSmith_reduction {m n : ℕ} (rows : Vector (Vector ℤ n) m) :
    (normalizedSmith rows).reduction = rectangularSmith (tableMatrix rows) := rfl

/-- An index is retained in normalized Smith data exactly when its coefficient is not one. -/
@[simp] theorem mem_normalizedSmith_retained {m n : ℕ} (rows : Vector (Vector ℤ n) m)
    (r : Fin m) : r ∈ (normalizedSmith rows).retained ↔ (normalizedSmith rows).coeff r ≠ 1 := by
  simp [normalizedSmith, NormalizedSmithData.coeff]

/-- The additive equivalence obtained by dropping the trivial `ZMod 1` coordinates from a full
Smith-coordinate product. -/
def normalizedRestrictionEquiv {m n : ℕ} (p : NormalizedSmithData m n) :
    (∀ r : Fin m, ZMod (p.coeff r)) ≃+ NormalizedCoordinates p where
  toFun z r := z r
  invFun := inflateNormalized p
  left_inv z := by
    funext r
    by_cases h : p.coeff r ≠ 1
    · simp [inflateNormalized, h]
    · haveI : Subsingleton (ZMod (p.coeff r)) := by
        rw [not_ne_iff.mp h]
        infer_instance
      exact Subsingleton.elim _ _
  right_inv z := by
    funext r
    simp [inflateNormalized, r.property]
  map_add' _ _ := rfl

/-- The additive equivalence from a table's presentation module to its normalized cyclic
coordinates. -/
def normalizedCyclicEquiv {m n : ℕ} (rows : Vector (Vector ℤ n) m) :
    PresentationModule (tableMatrix rows) ≃+ NormalizedCoordinates (normalizedSmith rows) :=
  ((rectangularSmithCyclicEquiv (tableMatrix rows)).trans
    (AddEquiv.piCongrRight fun r =>
      (ZMod.ringEquivCongr (normalizedSmith_coeff rows r).symm).toAddEquiv)).trans
    (normalizedRestrictionEquiv (normalizedSmith rows))

/-- The normalized cyclic equivalence on a quotient representative agrees with normalized
coordinate encoding. -/
theorem normalizedCyclicEquiv_mk {m n : ℕ} (rows : Vector (Vector ℤ n) m)
    (v : Fin m → ℤ) :
    normalizedCyclicEquiv rows (Submodule.Quotient.mk v) = normalizedEncode (normalizedSmith rows) v := by
  funext r
  change ZMod.ringEquivCongr (normalizedSmith_coeff rows r).symm
    (((rectangularSmith (tableMatrix rows)).left *ᵥ v) r : _) = _
  rw [ZMod.ringEquivCongr_intCast]
  rfl

/-- Normalized encoding of a decoded normalized-coordinate vector returns the original vector. -/
theorem normalizedEncode_decode {m n : ℕ} (rows : Vector (Vector ℤ n) m)
    (z : NormalizedCoordinates (normalizedSmith rows)) :
    normalizedEncode (normalizedSmith rows) (normalizedDecode (normalizedSmith rows) z) = z := by
  funext r
  change (((rectangularSmith (tableMatrix rows)).left *ᵥ
    ((rectangularSmith (tableMatrix rows)).leftInverse *ᵥ
      (fun i => (ZMod.cast (inflateNormalized (normalizedSmith rows) z i) : ℤ)))) r : _) = z r
  rw [Matrix.mulVec_mulVec, (rectangularSmith_encodes (tableMatrix rows)).2.1, Matrix.one_mulVec]
  rw [ZMod.intCast_zmod_cast]
  simp only [inflateNormalized, dif_pos r.property]

/-- Decoding the normalized encoding of an integer vector preserves its quotient class in the
presentation module. -/
theorem normalizedDecode_encode {m n : ℕ} (rows : Vector (Vector ℤ n) m) (v : Fin m → ℤ) :
    (Submodule.Quotient.mk (normalizedDecode (normalizedSmith rows)
      (normalizedEncode (normalizedSmith rows) v)) : PresentationModule (tableMatrix rows)) =
      Submodule.Quotient.mk v := by
  apply (normalizedCyclicEquiv rows).injective
  rw [normalizedCyclicEquiv_mk, normalizedEncode_decode, normalizedCyclicEquiv_mk]

/-- Two integer vectors have the same normalized encoding exactly when their difference lies in
the relation matrix's range. -/
theorem normalizedEncode_eq_iff {m n : ℕ} (rows : Vector (Vector ℤ n) m) (u v : Fin m → ℤ) :
    normalizedEncode (normalizedSmith rows) u = normalizedEncode (normalizedSmith rows) v ↔
      u-v ∈ LinearMap.range (tableMatrix rows).mulVecLin := by
  rw [← normalizedCyclicEquiv_mk, ← normalizedCyclicEquiv_mk]
  exact (normalizedCyclicEquiv rows).injective.eq_iff.trans (Submodule.Quotient.eq _)

/-- The normalized word-equality test returns `true` exactly when the difference of its inputs
lies in the relation matrix's range. -/
theorem normalizedWordEq_true_iff {m n : ℕ} (rows : Vector (Vector ℤ n) m) (u v : Fin m → ℤ) :
    normalizedWordEq (normalizedSmith rows) u v = true ↔
      u-v ∈ LinearMap.range (tableMatrix rows).mulVecLin := by
  simp only [normalizedWordEq, decide_eq_true_eq, ← funext_iff]
  exact normalizedEncode_eq_iff rows u v

/-- The normalized Smith finiteness flag is `true` exactly when the presented module is finite. -/
@[simp] theorem normalizedSmith_isFinite {m n : ℕ} (rows : Vector (Vector ℤ n) m) :
    (normalizedSmith rows).isFinite = true ↔ Finite (PresentationModule (tableMatrix rows)) := by
  simp only [NormalizedSmithData.isFinite, decide_eq_true_eq, normalizedSmith_coeff]
  exact (finite_presentation_iff _).symm

/-- The retained indices in normalized Smith data contain no duplicates. -/
theorem normalizedSmith_retained_nodup {m n : ℕ} (rows : Vector (Vector ℤ n) m) :
    (normalizedSmith rows).retained.Nodup := by
  exact (List.nodup_finRange m).filter _

/-- The retained indices in normalized Smith data are strictly increasing. -/
theorem normalizedSmith_retained_increasing {m n : ℕ} (rows : Vector (Vector ℤ n) m) :
    (normalizedSmith rows).retained.Pairwise (fun r s => r < s) := by
  have h : (List.finRange m).Pairwise (fun r s => r < s) := by
    rw [← List.ofFn_id]
    exact List.pairwise_ofFn.mpr (fun _ _ h => h)
  exact h.filter _

/-- Normalized Smith coefficients form a divisibility chain in their index order. -/
theorem normalizedSmith_coefficient_chain {m n : ℕ} (rows : Vector (Vector ℤ n) m)
    (r s : Fin m) (h : r ≤ s) : (normalizedSmith rows).coeff r ∣ (normalizedSmith rows).coeff s := by
  simp only [normalizedSmith_coeff, cyclicFactors]
  exact Int.natAbs_dvd_natAbs.mpr
    (SmithForm_coefficient_chain _ (rectangularSmith_form _) r s h)

/-- The retained normalized Smith factors form a divisibility chain. -/
theorem normalizedSmith_factors_chain {m n : ℕ} (rows : Vector (Vector ℤ n) m) :
    (normalizedSmith rows).factors.Pairwise Dvd.dvd := by
  rw [NormalizedSmithData.factors, List.pairwise_map]
  exact (normalizedSmith_retained_increasing rows).imp
    (fun h => normalizedSmith_coefficient_chain rows _ _ (le_of_lt h))

/-- No retained normalized Smith factor equals one. -/
theorem normalizedSmith_factors_ne_one {m n : ℕ} (rows : Vector (Vector ℤ n) m)
    (d : ℕ) (hd : d ∈ (normalizedSmith rows).factors) : d ≠ 1 := by
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hd
  exact (mem_normalizedSmith_retained rows r).mp hr

/-- When the normalized Smith finiteness flag is `true`, every retained factor is strictly
greater than one. -/
theorem normalizedSmith_finite_factors {m n : ℕ} (rows : Vector (Vector ℤ n) m)
    (hf : (normalizedSmith rows).isFinite = true) (d : ℕ)
    (hd : d ∈ (normalizedSmith rows).factors) : 1 < d := by
  have hn := normalizedSmith_factors_ne_one rows d hd
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hd
  have hzero : (normalizedSmith rows).coeff r ≠ 0 :=
    (of_decide_eq_true hf : ∀ r : Fin m, (normalizedSmith rows).coeff r ≠ 0) r
  omega

/-- Normalized Smith data has at most `m` retained factors, with exactly one generator word for
each factor. -/
theorem normalizedSmith_output_size {m n : ℕ} (rows : Vector (Vector ℤ n) m) :
    (normalizedSmith rows).factors.length ≤ m ∧
      (normalizedSmith rows).generatorWords.length = (normalizedSmith rows).factors.length := by
  constructor
  · simp only [NormalizedSmithData.factors, List.length_map]
    change ((List.finRange m).filter _).length ≤ m
    simpa using! List.length_filter_le
      (fun r : Fin m => (normalizedSmith rows).coeff r != 1) (List.finRange m)
  · simp [NormalizedSmithData.generatorWords, NormalizedSmithData.factors]

/-- The quotient class of the generator word taken from a column of the recorded left inverse is
the corresponding Smith generator. -/
theorem normalizedSmith_generatorWord {m n : ℕ} (rows : Vector (Vector ℤ n) m)
    (r : Fin m) :
    (Submodule.Quotient.mk (fun i : Fin m =>
      (Vector.ofFn (fun j => (normalizedSmith rows).reduction.leftInverse j r))[i.val]) :
        PresentationModule (tableMatrix rows)) = smithGenerator (tableMatrix rows) r := by
  unfold smithGenerator
  congr 1
  funext i
  simp [Matrix.col_apply]

/-- Removing the trivial factors preserves the product of all cyclic factors of the
presentation. -/
theorem normalizedSmith_factors_product {m n : ℕ} (rows : Vector (Vector ℤ n) m) :
    (normalizedSmith rows).factors.prod = ∏ r : Fin m, cyclicFactors (tableMatrix rows) r := by
  let p := normalizedSmith rows
  have he : p.factors = ((List.finRange m).map p.coeff).filter (fun d => d != 1) := by
    rw [List.filter_map]
    rfl
  rw [he, List.prod_filter_bne_one, ← List.ofFn_eq_map, List.prod_ofFn]
  simp only [p, normalizedSmith_coeff]

/-- The natural cardinality of the presented module equals the product of its retained
normalized Smith factors. -/
theorem normalizedSmith_card {m n : ℕ} (rows : Vector (Vector ℤ n) m) :
    Nat.card (PresentationModule (tableMatrix rows)) = (normalizedSmith rows).factors.prod := by
  rw [normalizedSmith_factors_product, presentation_card]

/-- An additive equivalence restricts to an equivalence between the elements killed by
multiplication by `k`. -/
def torsionKernelEquiv {G H : Type*} [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H) (k : ℕ) :
    {x : G // k • x = 0} ≃ {y : H // k • y = 0} where
  toFun x := ⟨e x, by rw [← map_nsmul, x.property, map_zero]⟩
  invFun y := ⟨e.symm y, by rw [← map_nsmul, y.property, map_zero]⟩
  left_inv _ := Subtype.ext (e.symm_apply_apply _)
  right_inv _ := Subtype.ext (e.apply_symm_apply _)

/-- The elements killed by `k` in a product of `ZMod` groups correspond to the products of the
coordinatewise kernels. -/
def piTorsionKernelEquiv {ι : Type*} (d : ι → ℕ) (k : ℕ) :
    {x : (∀ i, ZMod (d i)) // k • x = 0} ≃ (∀ i, {x : ZMod (d i) // k • x = 0}) where
  toFun x i := ⟨x.val i, congrFun x.property i⟩
  invFun y := ⟨fun i => (y i).val, funext fun i => (y i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- For nonzero modulus `d`, the number of elements of `ZMod d` killed by `k` is `Nat.gcd d k`. -/
theorem card_zmod_torsion (d k : ℕ) (hd : d ≠ 0) :
    Nat.card {x : ZMod d // k • x = 0} = Nat.gcd d k := by
  letI : NeZero d := ⟨hd⟩
  change Nat.card (nsmulAddMonoidHom k : ZMod d →+ ZMod d).ker = _
  simpa only [Nat.card_zmod] using! IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod d) k

/-- For a finite presentation module, the number of elements killed by `k` is the product of the
gcds of its cyclic factors with `k`. -/
theorem card_presentation_torsion {m n : ℕ} (rows : Vector (Vector ℤ n) m)
    (hf : Finite (PresentationModule (tableMatrix rows))) (k : ℕ) :
    Nat.card {x : PresentationModule (tableMatrix rows) // k • x = 0} =
      ∏ r : Fin m, Nat.gcd (cyclicFactors (tableMatrix rows) r) k := by
  rw [Nat.card_congr (torsionKernelEquiv (rectangularSmithCyclicEquiv (tableMatrix rows)) k),
    Nat.card_congr (piTorsionKernelEquiv (cyclicFactors (tableMatrix rows)) k), Nat.card_pi]
  exact Finset.prod_congr rfl
      (fun r _ => card_zmod_torsion _ k ((finite_presentation_iff _).mp hf r))

/-- Filtering out entries equal to one preserves the product of their images under any
natural-valued function sending one to one. -/
private theorem prod_filter_units (l : List ℕ) (f : ℕ → ℕ) (hf : f 1 = 1) :
    ((l.filter (fun d => d != 1)).map f).prod = (l.map f).prod := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
    by_cases h : d = 1
    · subst d; simpa [hf] using! ih
    · simp [h, ih]

/-- The normalized Smith torsion profile at `k` is the product of the gcds of all cyclic factors
with `k`. -/
theorem normalizedSmith_torsionProfile_product {m n : ℕ} (rows : Vector (Vector ℤ n) m) (k : ℕ) :
    (normalizedSmith rows).torsionProfile k = ∏ r : Fin m, Nat.gcd (cyclicFactors (tableMatrix rows) r) k := by
  let p := normalizedSmith rows
  have he : p.factors = ((List.finRange m).map p.coeff).filter (fun d => d != 1) := by
    rw [List.filter_map]
    rfl
  change (p.factors.map _).prod = _
  rw [he, prod_filter_units _ _ (Nat.gcd_one_left k), List.map_map,
    ← List.ofFn_eq_map, List.prod_ofFn]
  simp only [Function.comp_def, p, normalizedSmith_coeff]

/-- When the normalized Smith finiteness flag is `true`, its torsion profile at `k` counts the
presented elements killed by `k`. -/
theorem normalizedSmith_torsionProfile_correct {m n : ℕ} (rows : Vector (Vector ℤ n) m)
    (hf : (normalizedSmith rows).isFinite = true) (k : ℕ) :
    (normalizedSmith rows).torsionProfile k =
      Nat.card {x : PresentationModule (tableMatrix rows) // k • x = 0} := by
  rw [normalizedSmith_torsionProfile_product,
    card_presentation_torsion rows ((normalizedSmith_isFinite rows).mp hf)]

/-- For isomorphic presented groups, with the first flagged finite, the normalized Smith torsion
profiles agree at every `k`. -/
theorem normalizedSmith_torsionProfile_invariant {m n m' n' : ℕ}
    (rows : Vector (Vector ℤ n) m) (rows' : Vector (Vector ℤ n') m')
    (hf : (normalizedSmith rows).isFinite = true)
    (e : PresentationModule (tableMatrix rows) ≃+ PresentationModule (tableMatrix rows'))
    (k : ℕ) : (normalizedSmith rows).torsionProfile k = (normalizedSmith rows').torsionProfile k := by
  have hf' : (normalizedSmith rows').isFinite = true := by
    apply (normalizedSmith_isFinite rows').mpr
    letI := (normalizedSmith_isFinite rows).mp hf
    exact Finite.of_equiv _ e.toEquiv
  rw [normalizedSmith_torsionProfile_correct rows hf,
    normalizedSmith_torsionProfile_correct rows' hf']
  exact Nat.card_congr (torsionKernelEquiv e k)

/-- For prime `p`, the product of the gcds of the list entries with `p` is `p` raised to the
number of entries divisible by `p`. -/
theorem list_prime_gcd_product (l : List ℕ) (p : ℕ) (hp : p.Prime) :
    (l.map (fun d => Nat.gcd d p)).prod = p ^ (l.filter (fun d => decide (p ∣ d))).length := by
  induction l with
  | nil => simp
  | cons d ds ih =>
    by_cases h : p ∣ d
    · have hg : Nat.gcd d p = p := Nat.gcd_eq_right h
      simp [h, hg, ih, pow_succ, mul_comm]
    · have hg : Nat.gcd d p = 1 := (hp.coprime_iff_not_dvd.mpr h).symm.gcd_eq_one
      simp [h, hg, ih]

/-- Isomorphic presentations of a finite group have the same number of normalized Smith factors
divisible by each prime. -/
theorem normalizedSmith_primeMultiplicity_invariant {m n m' n' : ℕ}
    (rows : Vector (Vector ℤ n) m) (rows' : Vector (Vector ℤ n') m')
    (hf : (normalizedSmith rows).isFinite = true)
    (e : PresentationModule (tableMatrix rows) ≃+ PresentationModule (tableMatrix rows'))
    (p : ℕ) (hp : p.Prime) :
    ((normalizedSmith rows).factors.filter (fun d => decide (p ∣ d))).length =
      ((normalizedSmith rows').factors.filter (fun d => decide (p ∣ d))).length := by
  apply pow_right_injective₀ hp.pos hp.ne_one
  have he := normalizedSmith_torsionProfile_invariant rows rows' hf e p
  simpa only [NormalizedSmithData.torsionProfile, list_prime_gcd_product _ p hp] using! he

/-- A divisibility chain with no entries equal to one has length at most that of any list having
the same counts of entries divisible by each prime. -/
private theorem divisorChain_length_le (l l' : List ℕ) (hl : l.Pairwise Dvd.dvd)
    (hne : ∀ d ∈ l, d ≠ 1)
    (hc : ∀ p : ℕ, p.Prime →
      (l.filter (fun d => decide (p ∣ d))).length = (l'.filter (fun d => decide (p ∣ d))).length) :
    l.length ≤ l'.length := by
  cases l with
  | nil => simp
  | cons d ds =>
    obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd (hne d (by simp))
    have hall : ∀ a ∈ d :: ds, p ∣ a := by
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hpd
      · exact hpd.trans (List.rel_of_pairwise_cons hl ha)
    have he : ((d :: ds).filter (fun a => decide (p ∣ a))) = d :: ds := by
      apply List.filter_eq_self.mpr
      intro a ha
      exact decide_eq_true (hall a ha)
    calc
      (d :: ds).length = ((d :: ds).filter (fun a => decide (p ∣ a))).length := by rw [he]
      _ = (l'.filter (fun a => decide (p ∣ a))).length := hc p hp
      _ ≤ l'.length := List.length_filter_le _ _

/-- Isomorphic presentations of a finite group have the same number of retained normalized Smith
factors. -/
theorem normalizedSmith_factorCount_invariant {m n m' n' : ℕ}
    (rows : Vector (Vector ℤ n) m) (rows' : Vector (Vector ℤ n') m')
    (hf : (normalizedSmith rows).isFinite = true)
    (e : PresentationModule (tableMatrix rows) ≃+ PresentationModule (tableMatrix rows')) :
    (normalizedSmith rows).factors.length = (normalizedSmith rows').factors.length := by
  have hf' : (normalizedSmith rows').isFinite = true := by
    apply (normalizedSmith_isFinite rows').mpr
    letI := (normalizedSmith_isFinite rows).mp hf
    exact Finite.of_equiv _ e.toEquiv
  apply Nat.le_antisymm
  · exact divisorChain_length_le _ _ (normalizedSmith_factors_chain rows)
      (normalizedSmith_factors_ne_one rows)
      (normalizedSmith_primeMultiplicity_invariant rows rows' hf e)
  · exact divisorChain_length_le _ _ (normalizedSmith_factors_chain rows')
      (normalizedSmith_factors_ne_one rows')
      (normalizedSmith_primeMultiplicity_invariant rows' rows hf' e.symm)

/-- Equality of all gcd-product profiles implies equal counts of entries divisible by each
prime. -/
private theorem prime_count_congr (l r : List ℕ)
    (he : ∀ k : ℕ, (l.map (fun d => Nat.gcd d k)).prod = (r.map (fun d => Nat.gcd d k)).prod)
    (p : ℕ) (hp : p.Prime) :
    (l.filter (fun d => decide (p ∣ d))).length = (r.filter (fun d => decide (p ∣ d))).length := by
  apply pow_right_injective₀ hp.pos hp.ne_one
  simpa only [list_prime_gcd_product _ p hp] using! he p

/-- For equal-length lists with equal gcd-product profiles, a prime dividing every entry of the
first list divides every entry of the second. -/
private theorem all_prime_divides_congr (l r : List ℕ) (hlen : l.length = r.length)
    (he : ∀ k : ℕ, (l.map (fun d => Nat.gcd d k)).prod = (r.map (fun d => Nat.gcd d k)).prod)
    (p : ℕ) (hp : p.Prime) (hl : ∀ d ∈ l, p ∣ d) : ∀ d ∈ r, p ∣ d := by
  have hc := prime_count_congr l r he p hp
  have hfl : l.filter (fun d => decide (p ∣ d)) = l :=
    List.filter_eq_self.mpr (fun d hd => decide_eq_true (hl d hd))
  rw [hfl, hlen] at hc
  have hr := List.length_filter_eq_length_iff.mp hc.symm
  intro d hd
  exact of_decide_eq_true (hr d hd)

/-- If `p` divides every list entry, the gcd product at `p*k` is `p^l.length` times the gcd
product at `k` after dividing the entries by `p`. -/
private theorem gcd_profile_div (l : List ℕ) (p k : ℕ) (hd : ∀ d ∈ l, p ∣ d) :
    (l.map (fun d => Nat.gcd d (p*k))).prod =
      p ^ l.length * (l.map (fun d => Nat.gcd (d/p) k)).prod := by
  induction l with
  | nil => simp
  | cons d ds ih =>
    have hp : p ∣ d := hd d (by simp)
    have hg : Nat.gcd d (p*k) = p * Nat.gcd (d/p) k := by
      calc
        _ = Nat.gcd (p*(d/p)) (p*k) := by rw [Nat.mul_div_cancel' hp]
        _ = _ := Nat.gcd_mul_left _ _ _
    simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.pow_succ]
    rw [hg, ih (fun a ha => hd a (by simp [ha]))]
    ac_rfl

/-- Dividing every entry of a natural-number list by `p` does not increase its sum. -/
private theorem sum_div_le (l : List ℕ) (p : ℕ) : (l.map (fun d => d/p)).sum ≤ l.sum := by
  induction l with
  | nil => simp
  | cons d ds ih => simpa using! Nat.add_le_add (Nat.div_le_self d p) ih

/-- Positive divisibility chains with equal lengths and equal gcd-product profiles are equal. -/
theorem divisorChain_eq_of_gcd_profiles (l r : List ℕ)
    (hl : l.Pairwise Dvd.dvd) (hr : r.Pairwise Dvd.dvd)
    (hposl : ∀ d ∈ l, 0 < d) (hposr : ∀ d ∈ r, 0 < d)
    (hlen : l.length = r.length)
    (he : ∀ k : ℕ, (l.map (fun d => Nat.gcd d k)).prod = (r.map (fun d => Nat.gcd d k)).prod) :
    l = r := by
  generalize hs : l.sum = s
  induction s using Nat.strong_induction_on generalizing l r with
  | h s ih =>
    cases l with
    | nil => exact (List.length_eq_zero_iff.mp hlen.symm).symm
    | cons a as =>
      cases r with
      | nil => simp at hlen
      | cons b bs =>
        have htail : as.length = bs.length := by simpa using! hlen
        by_cases ha : a = 1
        · have hb : b = 1 := by
            by_contra hb
            obtain ⟨p,hp,hpb⟩ := Nat.exists_prime_and_dvd hb
            have hbr : ∀ d ∈ b :: bs, p ∣ d := by
              intro d hd
              rcases List.mem_cons.mp hd with rfl | hd
              · exact hpb
              · exact hpb.trans (List.rel_of_pairwise_cons hr hd)
            have hal := all_prime_divides_congr (b::bs) (a::as) hlen.symm
              (fun k => (he k).symm) p hp hbr
            have hpa : p ∣ 1 := ha ▸ hal a (by simp)
            exact hp.ne_one (Nat.dvd_one.mp hpa)
          subst a; subst b
          have hsmall : as.sum < s := by simp only [List.sum_cons] at hs; omega
          have ht : as = bs := ih as.sum hsmall as bs hl.of_cons hr.of_cons
            (fun d hd => hposl d (by simp [hd]))
            (fun d hd => hposr d (by simp [hd])) htail
            (fun k => by simpa using! he k) rfl
          rw [ht]
        · obtain ⟨p,hp,hpa⟩ := Nat.exists_prime_and_dvd ha
          have hdivl : ∀ d ∈ a :: as, p ∣ d := by
            intro d hd
            rcases List.mem_cons.mp hd with rfl | hd
            · exact hpa
            · exact hpa.trans (List.rel_of_pairwise_cons hl hd)
          have hdivr := all_prime_divides_congr (a::as) (b::bs) hlen he p hp hdivl
          have hsmall : ((a::as).map (fun d => d/p)).sum < s := by
            have hlt := Nat.div_lt_self (hposl a (by simp)) hp.one_lt
            have hle := sum_div_le as p
            simp only [List.map_cons, List.sum_cons] at hs ⊢
            omega
          have hl' : ((a::as).map (fun d => d/p)).Pairwise Dvd.dvd := by
            rw [List.pairwise_map]
            exact hl.imp_of_mem (fun hx _ h => Nat.div_dvd_div (hdivl _ hx) h)
          have hr' : ((b::bs).map (fun d => d/p)).Pairwise Dvd.dvd := by
            rw [List.pairwise_map]
            exact hr.imp_of_mem (fun hx _ h => Nat.div_dvd_div (hdivr _ hx) h)
          have he' (k : ℕ) :
              (((a::as).map (fun d => d/p)).map (fun d => Nat.gcd d k)).prod =
              (((b::bs).map (fun d => d/p)).map (fun d => Nat.gcd d k)).prod := by
            have h := he (p*k)
            rw [gcd_profile_div _ p k hdivl, gcd_profile_div _ p k hdivr, hlen] at h
            simpa only [List.map_map, Function.comp_def] using!
              (Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) h)
          have hq := ih _ hsmall _ _ hl' hr'
            (by
              intro d hd
              obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hd
              exact Nat.div_pos (Nat.le_of_dvd (hposl x hx) (hdivl x hx)) hp.pos)
            (by
              intro d hd
              obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hd
              exact Nat.div_pos (Nat.le_of_dvd (hposr x hx) (hdivr x hx)) hp.pos)
            (by simpa only [List.length_map] using! hlen) he' rfl
          have hlrec : ((a::as).map (fun d => d/p)).map (fun d => p*d) = a::as := by
            rw [List.map_map]
            calc
              _ = (a::as).map (fun d => d) := List.map_congr_left (fun d hd => Nat.mul_div_cancel' (hdivl d hd))
              _ = _ := List.map_id' _
          have hrrec : ((b::bs).map (fun d => d/p)).map (fun d => p*d) = b::bs := by
            rw [List.map_map]
            calc
              _ = (b::bs).map (fun d => d) := List.map_congr_left (fun d hd => Nat.mul_div_cancel' (hdivr d hd))
              _ = _ := List.map_id' _
          rw [← hlrec, ← hrrec, hq]

/-- Isomorphic presentations of a finite group yield identical retained normalized Smith factor
lists. -/
theorem normalizedSmith_factors_invariant {m n m' n' : ℕ}
    (rows : Vector (Vector ℤ n) m) (rows' : Vector (Vector ℤ n') m')
    (hf : (normalizedSmith rows).isFinite = true)
    (e : PresentationModule (tableMatrix rows) ≃+ PresentationModule (tableMatrix rows')) :
    (normalizedSmith rows).factors = (normalizedSmith rows').factors := by
  have hf' : (normalizedSmith rows').isFinite = true := by
    apply (normalizedSmith_isFinite rows').mpr
    letI := (normalizedSmith_isFinite rows).mp hf
    exact Finite.of_equiv _ e.toEquiv
  exact divisorChain_eq_of_gcd_profiles _ _
    (normalizedSmith_factors_chain rows) (normalizedSmith_factors_chain rows')
    (fun d hd => Nat.zero_lt_of_lt (normalizedSmith_finite_factors rows hf d hd))
    (fun d hd => Nat.zero_lt_of_lt (normalizedSmith_finite_factors rows' hf' d hd))
    (normalizedSmith_factorCount_invariant rows rows' hf e)
    (normalizedSmith_torsionProfile_invariant rows rows' hf e)

/-- The generator word map evaluates an integer vector as the sum of its integer multiples of
the specified generators. -/
@[simp] theorem generatorWordMap_apply {C : Type*} [AddCommGroup C] {m : ℕ}
    (g : Vector C m) (v : Fin m → ℤ) : generatorWordMap g v = ∑ r : Fin m, v r • g[r.val] := by
  simp [generatorWordMap]

/-- The additive equivalence from the quotient by the relation matrix of a valid compact abelian
presentation to the presented group. -/
noncomputable def compactPresentationEquiv {C : Type*} [AddCommGroup C] {m n : ℕ}
    (p : CompactAbelianPresentation C m n) (hp : p.Valid) :
    PresentationModule (tableMatrix p.relations) ≃+ C :=
  ((Submodule.quotEquivOfEq _ _ hp.relations_complete.symm).trans
    ((generatorWordMap p.generators).quotKerEquivOfSurjective hp.generates)).toAddEquiv

/-- The compact-presentation equivalence sends an integer vector's quotient class to the group
element represented by that generator word. -/
@[simp] theorem compactPresentationEquiv_mk {C : Type*} [AddCommGroup C] {m n : ℕ}
    (p : CompactAbelianPresentation C m n) (hp : p.Valid) (v : Fin m → ℤ) :
    compactPresentationEquiv p hp (Submodule.Quotient.mk v) = generatorWordMap p.generators v := by
  simp [compactPresentationEquiv, LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The additive equivalence from a group with a valid compact abelian presentation to its
recovered normalized Smith coordinates. -/
noncomputable def compactRecoveryEquiv {C : Type*} [AddCommGroup C] {m n : ℕ}
    (p : CompactAbelianPresentation C m n) (hp : p.Valid) :
    C ≃+ NormalizedCoordinates p.run :=
  (compactPresentationEquiv p hp).symm.trans (normalizedCyclicEquiv p.relations)

/-- The recovered coordinates of a generator word are its normalized Smith encoding. -/
theorem compactRecoveryEquiv_word {C : Type*} [AddCommGroup C] {m n : ℕ}
    (p : CompactAbelianPresentation C m n) (hp : p.Valid) (v : Fin m → ℤ) :
    compactRecoveryEquiv p hp (generatorWordMap p.generators v) = normalizedEncode p.run v := by
  rw [← compactPresentationEquiv_mk p hp v]
  change normalizedCyclicEquiv p.relations ((compactPresentationEquiv p hp).symm
    (compactPresentationEquiv p hp (Submodule.Quotient.mk v))) = _
  rw [AddEquiv.symm_apply_apply, normalizedCyclicEquiv_mk]
  rfl

/-- For a valid compact presentation, the normalized word test returns `true` exactly when the
two words represent the same group element. -/
@[simp] theorem compactRecovery_wordEq {C : Type*} [AddCommGroup C] {m n : ℕ}
    (p : CompactAbelianPresentation C m n) (hp : p.Valid) (u v : Fin m → ℤ) :
    normalizedWordEq p.run u v = true ↔ generatorWordMap p.generators u = generatorWordMap p.generators v := by
  simp only [normalizedWordEq, decide_eq_true_eq, ← funext_iff]
  rw [← compactRecoveryEquiv_word p hp u, ← compactRecoveryEquiv_word p hp v]
  exact (compactRecoveryEquiv p hp).injective.eq_iff

/-- For a valid compact presentation, the recovered finiteness flag is `true` exactly when the
presented group is finite. -/
@[simp] theorem compactRecovery_finite_iff {C : Type*} [AddCommGroup C] {m n : ℕ}
    (p : CompactAbelianPresentation C m n) (hp : p.Valid) :
    p.run.isFinite = true ↔ Finite C := by
  change (normalizedSmith p.relations).isFinite = true ↔ _
  rw [normalizedSmith_isFinite]
  constructor
  · intro hf
    letI := hf
    exact Finite.of_equiv _ (compactPresentationEquiv p hp).toEquiv
  · intro hf
    letI := hf
    exact Finite.of_equiv _ (compactPresentationEquiv p hp).symm.toEquiv

/-- Two valid compact presentations of the same finite abelian group produce identical
normalized factor lists [Cheung and Mosca, Theorem 7][CheungMosca2001]. -/
theorem compactRecovery_factors_canonical {C : Type*} [AddCommGroup C] {m n m' n' : ℕ}
    (p : CompactAbelianPresentation C m n) (q : CompactAbelianPresentation C m' n')
    (hp : p.Valid) (hq : q.Valid) (hf : Finite C) : p.run.factors = q.run.factors := by
  exact normalizedSmith_factors_invariant p.relations q.relations
    ((compactRecovery_finite_iff p hp).mpr hf)
    ((compactPresentationEquiv p hp).trans (compactPresentationEquiv q hq).symm)

/-- The normalized cyclic equivalence sends a Smith generator to the vector with one at its
retained index and zero at every other retained index. -/
theorem normalizedCyclicEquiv_generator {m n : ℕ} (rows : Vector (Vector ℤ n) m) (r : Fin m) :
    normalizedCyclicEquiv rows (smithGenerator (tableMatrix rows) r) =
      fun s : {i : Fin m // (normalizedSmith rows).coeff i ≠ 1} =>
        if (s : Fin m) = r then (1 : ZMod ((normalizedSmith rows).coeff s)) else 0 := by
  funext s
  change ZMod.ringEquivCongr (normalizedSmith_coeff rows s).symm
    (rectangularSmithCyclicEquiv (tableMatrix rows) (smithGenerator (tableMatrix rows) r) s) = _
  rw [rectangularSmithCyclicEquiv_generator]
  by_cases h : (s : Fin m) = r
  · subst r
    simp
  · simp [h]

/-- The group element represented by column `r` of the recovered left inverse has coordinate one
at retained index `r` and zero elsewhere under `compactRecoveryEquiv` [Cheung and Mosca,
Theorem 7][CheungMosca2001]. -/
theorem compactRecovery_generator {C : Type*} [AddCommGroup C] {m n : ℕ}
    (p : CompactAbelianPresentation C m n) (hp : p.Valid) (r : Fin m) :
    compactRecoveryEquiv p hp
      (generatorWordMap p.generators (fun i => p.run.reduction.leftInverse i r)) =
      fun s : {i : Fin m // p.run.coeff i ≠ 1} =>
        if (s : Fin m) = r then (1 : ZMod (p.run.coeff s)) else 0 := by
  rw [compactRecoveryEquiv_word]
  change normalizedEncode (normalizedSmith p.relations) _ = _
  rw [← normalizedCyclicEquiv_mk]
  have hg : (Submodule.Quotient.mk (fun i => p.run.reduction.leftInverse i r) :
      PresentationModule (tableMatrix p.relations)) = smithGenerator (tableMatrix p.relations) r := by
    simpa only [Vector.getElem_ofFn] using! normalizedSmith_generatorWord p.relations r
  rw [hg, normalizedCyclicEquiv_generator]
  rfl

/-- Decoding the binary digits of a natural number returns that number. -/
@[simp] theorem smithDecodeNat_bits (n : ℕ) : smithDecodeNat n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [smithDecodeNat]
  | bit b n h ih => simp [Nat.bits_append_bit n b h, smithDecodeNat] at ih ⊢; exact congrArg (Nat.bit b) ih

/-- Decoding an encoded integer returns the original integer. -/
@[simp] theorem smithDecodeInteger_encode (z : ℤ) : smithDecodeInteger (smithEncodeInteger z) = z := by
  by_cases h : z < 0
  · simp [smithDecodeInteger, smithEncodeInteger, h, abs_of_neg h]
  · simp [smithDecodeInteger, smithEncodeInteger, h, abs_of_nonneg (le_of_not_gt h)]

/-- Decoding an encoded integer relation table returns the original table. -/
@[simp] theorem smithDecodeRelations_encode {m n : ℕ} (rows : Vector (Vector ℤ n) m) :
    smithDecodeRelations (smithEncodeRelations rows) = rows := by
  ext i hi j hj
  simp [smithDecodeRelations, smithEncodeRelations]

/-- Running the binary Smith procedure on an encoded integer relation table returns its
normalized Smith data. -/
@[simp] theorem smithRunBinary_encode {m n : ℕ} (rows : Vector (Vector ℤ n) m) :
    smithRunBinary (smithEncodeRelations rows) = normalizedSmith rows := by
  simp [smithRunBinary]

/-- The encoded relation-table bit count is the sum, over all entries, of one sign bit plus the
binary size of the absolute value. -/
theorem smithRelationBits_encode {m n : ℕ} (rows : Vector (Vector ℤ n) m) :
    smithRelationBits (smithEncodeRelations rows) =
      ∑ i : Fin m, ∑ j : Fin n, (1 + (rows[i.val][j.val]).natAbs.size) := by
  simp [smithRelationBits, smithEncodeRelations, smithEncodeInteger, Nat.size_eq_bits_len]

/-- The recorded bit count of a binary relation table is at least its number of cells `m*n`. -/
theorem smithRelationBits_cells_le {m n : ℕ} (rows : Vector (Vector SmithIntegerCode n) m) :
    m*n ≤ smithRelationBits rows := by
  calc
    m*n = ∑ i : Fin m, ∑ j : Fin n, (1 : ℕ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => Nat.le_add_right _ _

/-- Decoding the binary factors of normalized Smith data returns its factor list. -/
@[simp] theorem binaryFactors_decode {m n : ℕ} (p : NormalizedSmithData m n) :
    p.binaryFactors.map smithDecodeNat = p.factors := by
  simp [NormalizedSmithData.binaryFactors, List.map_map, Function.comp_def]

/-- Decoding the binary generator words of normalized Smith data returns its integer generator
words. -/
@[simp] theorem binaryGeneratorWords_decode {m n : ℕ} (p : NormalizedSmithData m n) :
    p.binaryGeneratorWords.map (fun w => w.map smithDecodeInteger) = p.generatorWords := by
  simp only [NormalizedSmithData.binaryGeneratorWords, List.map_map]
  calc
    _ = p.generatorWords.map id := by
      apply List.map_congr_left
      intro w _
      ext i hi
      simp
    _ = _ := List.map_id _

/-- The value returned by counted search is the ordinary list search result. -/
@[simp] theorem smithFindCounted_value {α : Type*} (p : α → Bool) (l : List α) :
    (smithFindCounted p l).1 = l.find? p := by
  induction l with
  | nil => rfl
  | cons a as ih => cases h : p a <;> simp [smithFindCounted, List.find?, h, ih]

/-- The number of tests recorded by counted search is at most the list length. -/
theorem smithFindCounted_bound {α : Type*} (p : α → Bool) (l : List α) :
    (smithFindCounted p l).2 ≤ l.length := by
  induction l with
  | nil => simp [smithFindCounted]
  | cons a as ih =>
    simp only [smithFindCounted]
    split
    · simp
    · simpa using! Nat.add_le_add_right ih 1

/-- The counted finite universal check returns `true` exactly when the predicate holds at every
index. -/
@[simp] theorem smithCheckAllFin_true {m : ℕ} (P : Fin m → Prop) [DecidablePred P] :
    (smithCheckAllFin P).1 = true ↔ ∀ i, P i := by
  simp [smithCheckAllFin, List.find?_eq_none]

/-- The counted universal check on `Fin m` records at most `m` tests. -/
theorem smithCheckAllFin_bound {m : ℕ} (P : Fin m → Prop) [DecidablePred P] :
    (smithCheckAllFin P).2 ≤ m := by
  simpa [smithCheckAllFin] using!
    smithFindCounted_bound (fun i => decide (¬ P i)) (List.finRange m)

/-- The value component of the counted pivot-isolation loop equals the uncounted loop result. -/
@[simp] theorem countedIsolatePivotLoop_value {m n : ℕ} (fuel : ℕ)
    (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) :
    (countedIsolatePivotLoop fuel A).1 = isolatePivotLoop fuel A := by
  induction fuel generalizing A with
  | zero => rfl
  | succ fuel ih =>
    simp only [countedIsolatePivotLoop, isolatePivotLoop, tableMatrix_matrixTable]
    by_cases hc : ∀ r, A 0 0 ∣ A r 0
    · have hcb := (smithCheckAllFin_true _).mpr hc
      simp only [hcb, ↓reduceIte, if_pos hc]
      by_cases hr : ∀ c, A 0 0 ∣ A 0 c
      · have hrb := (smithCheckAllFin_true _).mpr hr
        simp only [hrb, ↓reduceIte, if_pos hr, smithFindCounted_value]
        cases h : badPivotEntry (clearPivot A).value
        · have hfind := h
          unfold badPivotEntry at hfind
          simp only [hfind]
        · have hfind := h
          unfold badPivotEntry at hfind
          simp only [hfind, ih]
      · have hrb : (smithCheckAllFin (fun c => A 0 0 ∣ A 0 c)).1 = false :=
          Bool.eq_false_iff.mpr (fun h => hr ((smithCheckAllFin_true _).mp h))
        simp [hrb, hr, ih]
    · have hcb : (smithCheckAllFin (fun r => A 0 0 ∣ A r 0)).1 = false :=
        Bool.eq_false_iff.mpr (fun h => hc ((smithCheckAllFin_true _).mp h))
      simp [hcb, hc, ih]

/-- The value component of counted pivot isolation equals the uncounted result. -/
@[simp] theorem countedIsolatePivot_value {m n : ℕ} (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) :
    (countedIsolatePivot A).1 = isolatePivot A := by
  simp [countedIsolatePivot, isolatePivot]

/-- The value component of counted rectangular Smith reduction equals the uncounted reduction. -/
@[simp] theorem countedRectangularSmith_value {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    (countedRectangularSmith A).1 = rectangularSmith A := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [countedRectangularSmith, rectangularSmith, tableMatrix_matrixTable,
        smithFindCounted_value]
      cases h : nonzeroEntry A
      · have hfind := h
        unfold nonzeroEntry at hfind
        simp only [hfind]
      · have hfind := h
        unfold nonzeroEntry at hfind
        simp only [hfind, countedIsolatePivot_value, ih]

/-- Each operation count of the pivot-isolation loop is bounded by the fuel times the
corresponding per-round budget. -/
theorem countedIsolatePivotLoop_bound {m n : ℕ} (fuel : ℕ)
    (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) (op : SmithKernelOp) :
    (countedIsolatePivotLoop fuel A).2 op ≤ fuel * smithPivotRoundBudget (m+1) (n+1) op := by
  induction fuel generalizing A with
  | zero => simp [countedIsolatePivotLoop]
  | succ fuel ih =>
    have hc := smithCheckAllFin_bound (fun r => A 0 0 ∣ A r 0)
    have hr := smithCheckAllFin_bound (fun c => A 0 0 ∣ A 0 c)
    have hb : (smithFindCounted (fun rc => decide (¬ (clearPivot A).value 0 0 ∣
        (clearPivot A).value rc.1 rc.2))
        ((List.finRange (m+1)).product (List.finRange (n+1)))).2 ≤ (m+1)*(n+1) := by
      calc
        _ ≤ ((List.finRange (m+1)).product (List.finRange (n+1))).length :=
          smithFindCounted_bound _ _
        _ = _ := by simpa only [List.length_finRange] using!
          List.length_product (List.finRange (m+1)) (List.finRange (n+1))
    simp only [countedIsolatePivotLoop, tableMatrix_matrixTable]
    split
    · split
      · split
        · cases op <;> simp [smithCharge, smithPivotRoundBudget, Pi.add_apply,
            Nat.succ_mul] at * <;> omega
        · rename_i rc he
          have hi := ih (rowReduce 0 (exposeRow rc.1 (clearPivot A).value).value).value
          cases op <;> simp [smithCharge, smithPivotRoundBudget, Pi.add_apply, Nat.succ_mul,
            RowEliminationState.toReduction, ColumnEliminationState.toReduction] at * <;> omega
      · have hi := ih (rowReduce 0 A).value
        cases op <;> simp [smithCharge, smithPivotRoundBudget, Pi.add_apply, Nat.succ_mul,
            RowEliminationState.toReduction] at * <;> omega
    · have hi := ih (columnReduce 0 A).value
      cases op <;> simp [smithCharge, smithPivotRoundBudget, Pi.add_apply, Nat.succ_mul,
            ColumnEliminationState.toReduction] at * <;> omega

/-- An operation with zero per-round budget has zero count in the pivot-isolation loop. -/
@[simp] theorem countedIsolatePivotLoop_zero_charge {m n : ℕ} (fuel : ℕ)
    (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) (op : SmithKernelOp)
    (h : smithPivotRoundBudget (m+1) (n+1) op = 0) :
    (countedIsolatePivotLoop fuel A).2 op = 0 := by
  have hb := countedIsolatePivotLoop_bound fuel A op
  rw [h, mul_zero] at hb
  exact Nat.eq_zero_of_le_zero hb

/-- Counted pivot isolation allocates fuel equal to the initial pivot's absolute value plus one. -/
@[simp] theorem countedIsolatePivot_allocated {m n : ℕ}
    (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) :
    (countedIsolatePivot A).2 .pivotFuelAllocated = (A 0 0).natAbs+1 := by
  simp [countedIsolatePivot, smithCharge, Pi.add_apply,
    countedIsolatePivotLoop_zero_charge ((A 0 0).natAbs+1) A .pivotFuelAllocated (by rfl)]

/-- Each operation count of pivot isolation is bounded by the allocated fuel times its per-round
budget, plus the fuel-allocation charge. -/
theorem countedIsolatePivot_bound {m n : ℕ} (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ)
    (op : SmithKernelOp) :
    (countedIsolatePivot A).2 op ≤ ((A 0 0).natAbs+1) * smithPivotRoundBudget (m+1) (n+1) op +
      smithCharge .pivotFuelAllocated ((A 0 0).natAbs+1) op := by
  simp only [countedIsolatePivot, Pi.add_apply]
  exact Nat.add_le_add_right (countedIsolatePivotLoop_bound _ _ _) _

/-- Pivot isolation records no rectangular-frame operations. -/
@[simp] theorem countedIsolatePivot_frame_zero {m n : ℕ}
    (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) :
    (countedIsolatePivot A).2 .rectangularFrame = 0 := by
  simp [countedIsolatePivot, smithCharge, Pi.add_apply,
    countedIsolatePivotLoop_zero_charge ((A 0 0).natAbs+1) A .rectangularFrame (by rfl)]

/-- Pivot isolation records no pivot-move operations. -/
@[simp] theorem countedIsolatePivot_move_zero {m n : ℕ}
    (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) :
    (countedIsolatePivot A).2 .movePivot = 0 := by
  simp [countedIsolatePivot, smithCharge, Pi.add_apply,
    countedIsolatePivotLoop_zero_charge ((A 0 0).natAbs+1) A .movePivot (by rfl)]

/-- Pivot isolation records no residual-lift operations. -/
@[simp] theorem countedIsolatePivot_lift_zero {m n : ℕ}
    (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) :
    (countedIsolatePivot A).2 .liftResidual = 0 := by
  simp [countedIsolatePivot, smithCharge, Pi.add_apply,
    countedIsolatePivotLoop_zero_charge ((A 0 0).natAbs+1) A .liftResidual (by rfl)]

/-- Rectangular Smith reduction records at most `min m n + 1` rectangular-frame operations. -/
theorem countedRectangularSmith_frames {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    (countedRectangularSmith A).2 .rectangularFrame ≤ min m n + 1 := by
  induction m generalizing n with
  | zero => simp [countedRectangularSmith, smithCharge]
  | succ m ih =>
    cases n with
    | zero => simp [countedRectangularSmith, smithCharge]
    | succ n =>
      simp only [countedRectangularSmith, tableMatrix_matrixTable]
      split
      · simp [smithCharge]
      · rename_i rc he
        have hi :=
            ih ((countedIsolatePivot (movePivot rc A).value).1.value.submatrix Fin.succ Fin.succ)
        simp [smithCharge, Pi.add_apply] at *
        omega

/-- Rectangular Smith reduction records at most `min m n` pivot moves. -/
theorem countedRectangularSmith_moves {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    (countedRectangularSmith A).2 .movePivot ≤ min m n := by
  induction m generalizing n with
  | zero => simp [countedRectangularSmith, smithCharge]
  | succ m ih =>
    cases n with
    | zero => simp [countedRectangularSmith, smithCharge]
    | succ n =>
      simp only [countedRectangularSmith, tableMatrix_matrixTable]
      split
      · simp [smithCharge]
      · rename_i rc he
        have hi :=
            ih ((countedIsolatePivot (movePivot rc A).value).1.value.submatrix Fin.succ Fin.succ)
        simp [smithCharge, Pi.add_apply] at *
        omega

/-- The residual-lift count of rectangular Smith reduction equals its pivot-move count. -/
theorem countedRectangularSmith_lifts {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    (countedRectangularSmith A).2 .liftResidual = (countedRectangularSmith A).2 .movePivot := by
  induction m generalizing n with
  | zero => simp [countedRectangularSmith, smithCharge]
  | succ m ih =>
    cases n with
    | zero => simp [countedRectangularSmith, smithCharge]
    | succ n =>
      simp only [countedRectangularSmith, tableMatrix_matrixTable]
      split
      · simp [smithCharge]
      · simp [smithCharge, Pi.add_apply, ih]

/-- The terminal rectangular-frame, cell-tabulation, and nonzero-test charges are bounded by the
rectangular Smith budget with zero pivot fuel. -/
private theorem smithRectangularBudget_terminal (m n : ℕ) (op : SmithKernelOp) :
    smithCharge .rectangularFrame 1 op + smithCharge .tabulateCell ((m+1)*(n+1)) op +
      smithCharge .nonzeroTest ((m+1)*(n+1)) op ≤ smithRectangularBudget (m+1) (n+1) 0 op := by
  cases op <;> simp [smithCharge, smithRectangularBudget]

/-- The charges for one rectangular reduction step, its allocated pivot fuel, and the residual
budget fit within the larger rectangular budget with the combined fuel. -/
private theorem smithRectangularBudget_step (m n f g : ℕ) (op : SmithKernelOp) :
    smithCharge .rectangularFrame 1 op + smithCharge .tabulateCell ((m+1)*(n+1)) op +
      smithCharge .nonzeroTest ((m+1)*(n+1)) op + smithCharge .movePivot 1 op +
      smithCharge .basisCompose 3 op + smithCharge .liftResidual 1 op +
      (f * smithPivotRoundBudget (m+1) (n+1) op + smithCharge .pivotFuelAllocated f op) +
      smithRectangularBudget m n g op ≤ smithRectangularBudget (m+1) (n+1) (f+g) op := by
  cases op <;> simp [smithCharge, smithRectangularBudget,
      smithPivotRoundBudget] <;> ring_nf <;> omega

/-- Increasing the amount charged to an operation does not decrease any component of its charge
vector. -/
theorem smithCharge_mono (op : SmithKernelOp) (a b : ℕ) (h : a ≤ b) (k : SmithKernelOp) :
    smithCharge op a k ≤ smithCharge op b k := by
  by_cases hk : k = op
  · simpa only [smithCharge, if_pos hk] using! h
  · simp [smithCharge, hk]

/-- Each recorded operation count of rectangular Smith reduction is bounded by the rectangular
budget evaluated at its total allocated pivot fuel. -/
theorem countedRectangularSmith_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (op : SmithKernelOp) :
    (countedRectangularSmith A).2 op ≤
      smithRectangularBudget m n ((countedRectangularSmith A).2 .pivotFuelAllocated) op := by
  induction m generalizing n with
  | zero => cases op <;> simp [countedRectangularSmith, smithRectangularBudget, smithCharge]
  | succ m ih =>
    cases n with
    | zero => cases op <;> simp [countedRectangularSmith, smithRectangularBudget, smithCharge]
    | succ n =>
      have hs : (smithFindCounted (fun rc => decide (A rc.1 rc.2 ≠ 0))
          ((List.finRange (m+1)).product (List.finRange (n+1)))).2 ≤ (m+1)*(n+1) := by
        calc
          _ ≤ ((List.finRange (m+1)).product (List.finRange (n+1))).length := smithFindCounted_bound _ _
          _ = _ := by simpa only [List.length_finRange] using!
            List.length_product (List.finRange (m+1)) (List.finRange (n+1))
      let base : SmithKernelCounts := smithCharge .rectangularFrame 1 +
        smithCharge .tabulateCell ((m+1)*(n+1)) + smithCharge .nonzeroTest
          (smithFindCounted (fun rc => decide (A rc.1 rc.2 ≠ 0))
            ((List.finRange (m+1)).product (List.finRange (n+1)))).2
      have hsc := smithCharge_mono .nonzeroTest _ _ hs op
      simp only [countedRectangularSmith, tableMatrix_matrixTable]
      split
      · change base op ≤ smithRectangularBudget (m+1) (n+1) (base .pivotFuelAllocated) op
        have hf : base .pivotFuelAllocated = 0 := by simp [base, smithCharge, Pi.add_apply]
        rw [hf]
        exact (Nat.add_le_add_left hsc _).trans (smithRectangularBudget_terminal m n op)
      · rename_i rc he
        let B := (movePivot rc A).value
        let U := (countedIsolatePivot B).1.value.submatrix Fin.succ Fin.succ
        let total := base + smithCharge .movePivot 1 + smithCharge .basisCompose 3 +
          smithCharge .liftResidual 1 + (countedIsolatePivot B).2 + (countedRectangularSmith U).2
        have ht := countedIsolatePivot_bound B op
        have hu := ih U
        have hstep := smithRectangularBudget_step m n ((B 0 0).natAbs+1)
          ((countedRectangularSmith U).2 .pivotFuelAllocated) op
        change total op ≤ smithRectangularBudget (m+1) (n+1) (total .pivotFuelAllocated) op
        have hf : total .pivotFuelAllocated =
            ((B 0 0).natAbs+1) + (countedRectangularSmith U).2 .pivotFuelAllocated := by
          simp [total, base, smithCharge, Pi.add_apply]
        rw [hf]
        dsimp only [total, base]
        simp only [Pi.add_apply]
        omega

/-- The value component of counted normalized Smith computation is the ordinary normalized Smith
data. -/
@[simp] theorem countedNormalizedSmith_value {m n : ℕ} (rows : Vector (Vector ℤ n) m) :
    (countedNormalizedSmith rows).1 = normalizedSmith rows := by
  simp only [countedNormalizedSmith, countedRectangularSmith_value]
  rfl

/-- The value component of the counted binary Smith procedure equals the ordinary binary
procedure's output. -/
@[simp] theorem countedSmithRunBinary_value {m n : ℕ} (rows : Vector (Vector SmithIntegerCode n) m) :
    (countedSmithRunBinary rows).1 = smithRunBinary rows := by
  simp only [countedSmithRunBinary, countedNormalizedSmith_value]
  rfl

/-- The counted binary Smith procedure on encoded integer relations returns their normalized
Smith data as its value component. -/
@[simp] theorem countedSmithRunBinary_encode {m n : ℕ} (rows : Vector (Vector ℤ n) m) :
    (countedSmithRunBinary (smithEncodeRelations rows)).1 = normalizedSmith rows := by
  simp

/-- Each recorded operation count of the binary Smith procedure is bounded by the rectangular
budget evaluated at its total allocated pivot fuel. -/
theorem countedSmithRunBinary_bound {m n : ℕ} (rows : Vector (Vector SmithIntegerCode n) m)
    (op : SmithKernelOp) :
    (countedSmithRunBinary rows).2 op ≤
      smithRectangularBudget m n ((countedSmithRunBinary rows).2 .pivotFuelAllocated) op :=
  countedRectangularSmith_bound (tableMatrix (smithDecodeRelations rows)) op

/-- The factor lists returned by counted normalized Smith computation agree for isomorphic
finite presented groups. -/
theorem countedNormalizedSmith_factors_invariant {m n m' n' : ℕ}
    (rows : Vector (Vector ℤ n) m) (rows' : Vector (Vector ℤ n') m')
    (hf : (countedNormalizedSmith rows).1.isFinite = true)
    (e : PresentationModule (tableMatrix rows) ≃+ PresentationModule (tableMatrix rows')) :
    (countedNormalizedSmith rows).1.factors = (countedNormalizedSmith rows').1.factors := by
  simp only [countedNormalizedSmith_value] at hf ⊢
  exact normalizedSmith_factors_invariant rows rows' hf e

/-- An unsuccessful counted list search records exactly the full list length in tests. -/
theorem smithFindCounted_none {α : Type*} (p : α → Bool) (l : List α)
    (h : (smithFindCounted p l).1 = none) : (smithFindCounted p l).2 = l.length := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    by_cases hp : p a = true
    · simp [smithFindCounted, hp] at h
    · simp only [smithFindCounted, if_neg hp] at h ⊢
      simpa only [List.length_cons] using! congrArg (fun n => n+1) (ih h)

/-- Counted list search records zero tests exactly when the input list is empty. -/
theorem smithFindCounted_zero_iff {α : Type*} (p : α → Bool) (l : List α) :
    (smithFindCounted p l).2 = 0 ↔ l = [] := by
  cases l with
  | nil => simp [smithFindCounted]
  | cons a as =>
    by_cases hp : p a = true <;> simp [smithFindCounted, hp]

/-- When the predicate holds at every finite index, the counted universal check records exactly
`m` tests. -/
theorem smithCheckAllFin_full_count {m : ℕ} (P : Fin m → Prop) [DecidablePred P]
    (h : ∀ i, P i) : (smithCheckAllFin P).2 = m := by
  have he : (smithFindCounted (fun i => decide (¬ P i)) (List.finRange m)).1 = none := by
    simp [List.find?_eq_none, h]
  simpa only [smithCheckAllFin, List.length_finRange] using! smithFindCounted_none _ _ he

/-- The value returned by counted Euclidean pair computation is the ordinary Euclidean pair
matrix together with its specified inverse. -/
theorem smithEuclidPairCounted_value (a b : ℤ) :
    (smithEuclidPairCounted a b).1 = (euclidPair a b,euclidPairInverse a b) := by
  simp only [smithEuclidPairCounted, Qatlib.Concepts.HspRecovery.CfOrder.cyclicDlogEuclid_value, Nat.xgcdAux_val, Nat.xgcd_val,
    euclidPair, euclidPairInverse, Int.gcd_def]
  have ha : (if a < 0 then -Nat.gcdA a.natAbs b.natAbs else Nat.gcdA a.natAbs b.natAbs) = Int.gcdA a b := by
    cases a <;> simp [Int.gcdA]
  have hb : (if b < 0 then -Nat.gcdB a.natAbs b.natAbs else Nat.gcdB a.natAbs b.natAbs) = Int.gcdB a b := by
    cases b <;> simp [Int.gcdB]
  rw [ha,hb]
  split <;> rfl

/-- The recorded Euclidean step count is at most `2*(Nat.log 2 (max a.natAbs b.natAbs) + 1) +
2`. -/
theorem smithEuclidPairCounted_work (a b : ℤ) :
    (smithEuclidPairCounted a b).2 ≤ 2*(Nat.log 2 (max a.natAbs b.natAbs)+1)+2 := by
  have he : (smithEuclidPairCounted a b).2 =
      (Qatlib.Concepts.HspRecovery.CfOrder.cyclicDlogEuclid a.natAbs 1 0 b.natAbs 0 1).2 := by
    simp only [smithEuclidPairCounted]
    split <;> rfl
  rw [he]
  by_cases hz : max a.natAbs b.natAbs = 0
  · have ha : a.natAbs = 0 := Nat.eq_zero_of_le_zero (hz ▸ le_max_left _ _)
    simp [ha, Qatlib.Concepts.HspRecovery.CfOrder.cyclicDlogEuclid]
  · exact Qatlib.Concepts.HspRecovery.JointDlog.joint_dlog_logarithmic_euclid _ _ _ _ _ _ _
      (Nat.pos_of_ne_zero hz) (le_max_left _ _) (le_max_right _ _)

/-- The counted Euclidean pair procedure records exactly the step count of `cyclicDlogEuclid` on
the absolute input values with the standard initial coefficients. -/
theorem smithEuclidPairCounted_steps (a b : ℤ) :
    (smithEuclidPairCounted a b).2 = (Qatlib.Concepts.HspRecovery.CfOrder.cyclicDlogEuclid a.natAbs 1 0 b.natAbs 0 1).2 := by
  simp only [smithEuclidPairCounted]
  split <;> rfl

/-- The recorded Euclidean step count is at most twice the binary size of the larger absolute
input plus two. -/
theorem smithEuclidPairCounted_bit_work (a b : ℤ) :
    (smithEuclidPairCounted a b).2 ≤ 2*(max a.natAbs b.natAbs).size+2 := by
  by_cases hz : max a.natAbs b.natAbs = 0
  · have ha : a.natAbs = 0 := Nat.eq_zero_of_le_zero (hz ▸ le_max_left _ _)
    rw [smithEuclidPairCounted_steps]
    simp [ha, Qatlib.Concepts.HspRecovery.CfOrder.cyclicDlogEuclid]
  · have hw := smithEuclidPairCounted_work a b
    have hl := Nat.log_lt_of_lt_pow hz (Nat.lt_size_self (max a.natAbs b.natAbs))
    omega

/-- The zero Euclidean work record is valid. -/
theorem SmithEuclidWork.valid_zero : SmithEuclidWork.zero.Valid := by
  simp [SmithEuclidWork.Valid, SmithEuclidWork.zero]

/-- Appending two valid Euclidean work records produces a valid work record. -/
theorem SmithEuclidWork.valid_append (a b : SmithEuclidWork) (ha : a.Valid) (hb : b.Valid) :
    (a.append b).Valid := by
  have ham := Nat.mul_le_mul_left a.calls (show 2*a.peakPairInputBits+2 ≤
      2*(max a.peakPairInputBits b.peakPairInputBits)+2 by omega)
  have hbm := Nat.mul_le_mul_left b.calls (show 2*b.peakPairInputBits+2 ≤
      2*(max a.peakPairInputBits b.peakPairInputBits)+2 by omega)
  change a.quotRemPairs+b.quotRemPairs ≤
      (a.calls+b.calls)*(2*(max a.peakPairInputBits b.peakPairInputBits)+2)
  rw [Nat.add_mul]
  exact Nat.add_le_add (ha.trans ham) (hb.trans hbm)

/-- The value returned by a counted column elimination step equals the ordinary column step. -/
@[simp] theorem smithColumnStepCounted_value {m n : ℕ} (p : Fin n)
    (s : ColumnEliminationState (m+1) n) (k : Fin m) :
    (smithColumnStepCounted p s k).1 = columnStep p s k := by
  simp only [smithColumnStepCounted, smithEuclidPairCounted_value, columnStep]

/-- The Euclidean work record produced by a counted column elimination step is valid. -/
theorem smithColumnStepCounted_work {m n : ℕ} (p : Fin n)
    (s : ColumnEliminationState (m+1) n) (k : Fin m) :
    (smithColumnStepCounted p s k).2.Valid := by
  simpa only [smithColumnStepCounted, SmithEuclidWork.Valid, one_mul] using!
    smithEuclidPairCounted_bit_work (s.value 0 p) (s.value k.succ p)

/-- The value returned by a counted column fold equals the ordinary fold of column elimination
steps. -/
@[simp] theorem smithColumnFoldCounted_value {m n : ℕ} (p : Fin n) (ks : List (Fin m))
    (s : ColumnEliminationState (m+1) n) (w : SmithEuclidWork) :
    (smithColumnFoldCounted p ks s w).1 = ks.foldl (columnStep p) s := by
  induction ks generalizing s w with
  | nil => rfl
  | cons k ks ih =>
    simp only [smithColumnFoldCounted, List.foldl_cons]
    change (smithColumnFoldCounted p ks _ _).1 = _
    rw [ih, smithColumnStepCounted_value]

/-- A counted column fold preserves validity of its accumulated Euclidean work record. -/
theorem smithColumnFoldCounted_work {m n : ℕ} (p : Fin n) (ks : List (Fin m))
    (s : ColumnEliminationState (m+1) n) (w : SmithEuclidWork) (hw : w.Valid) :
    (smithColumnFoldCounted p ks s w).2.Valid := by
  induction ks generalizing s w with
  | nil => exact hw
  | cons k ks ih =>
    simp only [smithColumnFoldCounted, List.foldl_cons]
    exact ih _ _ (SmithEuclidWork.valid_append w _ hw (smithColumnStepCounted_work p s k))

/-- A counted column fold adds exactly one Euclidean call per listed index to its initial call
count. -/
theorem smithColumnFoldCounted_calls {m n : ℕ} (p : Fin n) (ks : List (Fin m))
    (s : ColumnEliminationState (m+1) n) (w : SmithEuclidWork) :
    (smithColumnFoldCounted p ks s w).2.calls = w.calls + ks.length := by
  induction ks generalizing s w with
  | nil => simp [smithColumnFoldCounted]
  | cons k ks ih =>
    simp only [smithColumnFoldCounted, List.foldl_cons]
    change (smithColumnFoldCounted p ks _ _).2.calls = _
    rw [ih]
    simp only [SmithEuclidWork.append, smithColumnStepCounted, List.length_cons]
    omega

/-- The value returned by counted column reduction equals ordinary column reduction. -/
@[simp] theorem smithColumnReduceCounted_value {m n : ℕ} (p : Fin n)
    (A : Matrix (Fin (m+1)) (Fin n) ℤ) :
    (smithColumnReduceCounted p A).1 = columnReduce p A := by
  simp [smithColumnReduceCounted, columnReduce]

/-- The Euclidean work record returned by counted column reduction is valid. -/
theorem smithColumnReduceCounted_work {m n : ℕ} (p : Fin n)
    (A : Matrix (Fin (m+1)) (Fin n) ℤ) :
    (smithColumnReduceCounted p A).2.Valid :=
  smithColumnFoldCounted_work p _ _ _ SmithEuclidWork.valid_zero

/-- Column reduction of a matrix with `m+1` rows records exactly `m` Euclidean calls. -/
@[simp] theorem smithColumnReduceCounted_calls {m n : ℕ} (p : Fin n)
    (A : Matrix (Fin (m+1)) (Fin n) ℤ) :
    (smithColumnReduceCounted p A).2.calls = m := by
  simp [smithColumnReduceCounted, smithColumnFoldCounted_calls, SmithEuclidWork.zero]

/-- The value returned by counted row reduction equals ordinary row reduction. -/
@[simp] theorem smithRowReduceCounted_value {m n : ℕ} (p : Fin m)
    (A : Matrix (Fin m) (Fin (n+1)) ℤ) :
    (smithRowReduceCounted p A).1 = rowReduce p A := by
  simp [smithRowReduceCounted, rowReduce]

/-- The Euclidean work record returned by counted row reduction is valid. -/
theorem smithRowReduceCounted_work {m n : ℕ} (p : Fin m)
    (A : Matrix (Fin m) (Fin (n+1)) ℤ) :
    (smithRowReduceCounted p A).2.Valid := smithColumnReduceCounted_work _ _

/-- Row reduction of a matrix with `n+1` columns records exactly `n` Euclidean calls. -/
@[simp] theorem smithRowReduceCounted_calls {m n : ℕ} (p : Fin m)
    (A : Matrix (Fin m) (Fin (n+1)) ℤ) :
    (smithRowReduceCounted p A).2.calls = n := by simp [smithRowReduceCounted]

/-- The quotient-remainder pair count of a column fold equals its initial count plus the sum of
the Euclidean step counts on the input pairs encountered by that fold. -/
theorem smithColumnFoldCounted_exact_quotRem {m n : ℕ} (p : Fin n) (ks : List (Fin m))
    (s : ColumnEliminationState (m+1) n) (w : SmithEuclidWork) :
    (smithColumnFoldCounted p ks s w).2.quotRemPairs = w.quotRemPairs +
      ((smithColumnEuclidInputs p ks s).map
        (fun ab => (Qatlib.Concepts.HspRecovery.CfOrder.cyclicDlogEuclid ab.1.natAbs 1 0 ab.2.natAbs 0 1).2)).sum := by
  induction ks generalizing s w with
  | nil => simp [smithColumnFoldCounted, smithColumnEuclidInputs]
  | cons k ks ih =>
    simp only [smithColumnFoldCounted, List.foldl_cons]
    change (smithColumnFoldCounted p ks _ _).2.quotRemPairs = _
    rw [ih, smithColumnStepCounted_value]
    simp only [SmithEuclidWork.append, smithColumnStepCounted, smithColumnEuclidInputs,
      List.map_cons, List.sum_cons, smithEuclidPairCounted_steps, Nat.add_assoc]

/-- The peak input size recorded by a column fold is the maximum of its initial peak and the
binary input sizes of all Euclidean pairs encountered by the fold. -/
theorem smithColumnFoldCounted_exact_peak {m n : ℕ} (p : Fin n) (ks : List (Fin m))
    (s : ColumnEliminationState (m+1) n) (w : SmithEuclidWork) :
    (smithColumnFoldCounted p ks s w).2.peakPairInputBits = max w.peakPairInputBits
      (((smithColumnEuclidInputs p ks s).map smithPairInputBits).foldr max 0) := by
  induction ks generalizing s w with
  | nil => simp [smithColumnFoldCounted, smithColumnEuclidInputs]
  | cons k ks ih =>
    simp only [smithColumnFoldCounted, List.foldl_cons]
    change (smithColumnFoldCounted p ks _ _).2.peakPairInputBits = _
    rw [ih, smithColumnStepCounted_value]
    simp only [SmithEuclidWork.append, smithColumnStepCounted, smithColumnEuclidInputs,
      smithPairInputBits, List.map_cons, List.foldr_cons, max_assoc]

/-- The quotient-remainder pair count of column reduction is at most `m * (2*B + 2)`, where `B`
is its recorded peak input bit size. -/
theorem smithColumnReduceCounted_division_bound {m n : ℕ} (p : Fin n)
    (A : Matrix (Fin (m+1)) (Fin n) ℤ) :
    (smithColumnReduceCounted p A).2.quotRemPairs ≤
      m*(2*(smithColumnReduceCounted p A).2.peakPairInputBits+2) := by
  have h := smithColumnReduceCounted_work p A
  simpa only [SmithEuclidWork.Valid, smithColumnReduceCounted_calls] using! h

/-- The quotient-remainder pair count of row reduction is at most `n * (2*B + 2)`, where `B` is
its recorded peak input bit size. -/
theorem smithRowReduceCounted_division_bound {m n : ℕ} (p : Fin m)
    (A : Matrix (Fin m) (Fin (n+1)) ℤ) :
    (smithRowReduceCounted p A).2.quotRemPairs ≤
      n*(2*(smithRowReduceCounted p A).2.peakPairInputBits+2) := by
  have h := smithRowReduceCounted_work p A
  simpa only [SmithEuclidWork.Valid, smithRowReduceCounted_calls] using! h

/-- Discarding the Euclidean work record from the instrumented pivot-isolation loop yields the
ordinary counted loop. -/
@[simp] theorem smithIsolatePivotEuclidLoop_projection {m n : ℕ} (fuel : ℕ)
    (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) :
    (smithIsolatePivotEuclidLoop fuel A).1 = countedIsolatePivotLoop fuel A := by
  induction fuel generalizing A with
  | zero => rfl
  | succ fuel ih =>
    simp only [smithIsolatePivotEuclidLoop, countedIsolatePivotLoop, tableMatrix_matrixTable]
    split
    · split
      · split
        · simp_all only []
        · simp_all only [smithRowReduceCounted_value, RowEliminationState.toReduction]
      · simp_all only [smithRowReduceCounted_value, RowEliminationState.toReduction]
    · simp_all only [smithColumnReduceCounted_value, ColumnEliminationState.toReduction]

/-- Discarding the Euclidean work record from instrumented pivot isolation yields ordinary
counted pivot isolation. -/
@[simp] theorem smithIsolatePivotEuclid_projection {m n : ℕ}
    (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) :
    (smithIsolatePivotEuclid A).1 = countedIsolatePivot A := by
  simp [smithIsolatePivotEuclid, countedIsolatePivot]

/-- Discarding the Euclidean work record from instrumented rectangular Smith reduction yields
ordinary counted rectangular Smith reduction. -/
@[simp] theorem smithRectangularEuclid_projection {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    (smithRectangularEuclid A).1 = countedRectangularSmith A := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [smithRectangularEuclid, countedRectangularSmith, tableMatrix_matrixTable]
      split
      · simp_all only []
      · simp_all only [smithIsolatePivotEuclid_projection]

/-- The Euclidean work record of the instrumented pivot-isolation loop is valid for every fuel
value. -/
theorem smithIsolatePivotEuclidLoop_valid {m n : ℕ} (fuel : ℕ)
    (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) : (smithIsolatePivotEuclidLoop fuel A).2.Valid := by
  induction fuel generalizing A with
  | zero => exact SmithEuclidWork.valid_zero
  | succ fuel ih =>
    simp only [smithIsolatePivotEuclidLoop, tableMatrix_matrixTable]
    split
    · split
      · split
        · exact SmithEuclidWork.valid_zero
        · exact SmithEuclidWork.valid_append _ _ (smithRowReduceCounted_work _ _) (ih _)
      · exact SmithEuclidWork.valid_append _ _ (smithRowReduceCounted_work _ _) (ih _)
    · exact SmithEuclidWork.valid_append _ _ (smithColumnReduceCounted_work _ _) (ih _)

/-- The Euclidean work record of instrumented pivot isolation is valid. -/
theorem smithIsolatePivotEuclid_valid {m n : ℕ} (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) :
    (smithIsolatePivotEuclid A).2.Valid := smithIsolatePivotEuclidLoop_valid _ _

/-- The Euclidean work record of instrumented rectangular Smith reduction is valid. -/
theorem smithRectangularEuclid_valid {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    (smithRectangularEuclid A).2.Valid := by
  induction m generalizing n with
  | zero => exact SmithEuclidWork.valid_zero
  | succ m ih =>
    cases n with
    | zero => exact SmithEuclidWork.valid_zero
    | succ n =>
      simp only [smithRectangularEuclid, tableMatrix_matrixTable]
      split
      · exact SmithEuclidWork.valid_zero
      · exact SmithEuclidWork.valid_append _ _ (smithIsolatePivotEuclid_valid _) (ih _)

/-- The pivot-isolation loop's Euclidean call count is `m` times its column-sweep count plus `n`
times its row-sweep count. -/
theorem smithIsolatePivotEuclidLoop_calls {m n : ℕ} (fuel : ℕ)
    (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) :
    (smithIsolatePivotEuclidLoop fuel A).2.calls =
      m*(smithIsolatePivotEuclidLoop fuel A).1.2 .columnSweep +
      n*(smithIsolatePivotEuclidLoop fuel A).1.2 .rowSweep := by
  induction fuel generalizing A with
  | zero => simp [smithIsolatePivotEuclidLoop, SmithEuclidWork.zero]
  | succ fuel ih =>
    simp only [smithIsolatePivotEuclidLoop, tableMatrix_matrixTable]
    split
    · split
      · split
        · simp [SmithEuclidWork.zero, smithCharge, Pi.add_apply]
        · rename_i rc he
          have hi :=
              ih (smithRowReduceCounted 0 (exposeRow rc.1 (clearPivot A).value).value).1.value
          simp [SmithEuclidWork.append, smithCharge, Pi.add_apply, Nat.mul_add,
            ColumnEliminationState.toReduction] at *
          omega
      · have hi := ih (smithRowReduceCounted 0 A).1.value
        simp [SmithEuclidWork.append, smithCharge, Pi.add_apply, Nat.mul_add] at *
        omega
    · have hi := ih (smithColumnReduceCounted 0 A).1.value
      simp [SmithEuclidWork.append, smithCharge, Pi.add_apply, Nat.mul_add] at *
      omega

/-- The Euclidean call count of the pivot-isolation loop is at most `(m+n)*fuel`. -/
theorem smithIsolatePivotEuclidLoop_calls_bound {m n : ℕ} (fuel : ℕ)
    (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) :
    (smithIsolatePivotEuclidLoop fuel A).2.calls ≤ (m+n)*fuel := by
  have hc : (countedIsolatePivotLoop fuel A).2 .columnSweep ≤ fuel := by
    simpa only [smithPivotRoundBudget, mul_one] using!
        countedIsolatePivotLoop_bound fuel A .columnSweep
  have hr : (countedIsolatePivotLoop fuel A).2 .rowSweep ≤ fuel := by
    simpa only [smithPivotRoundBudget, mul_one] using!
        countedIsolatePivotLoop_bound fuel A .rowSweep
  rw [smithIsolatePivotEuclidLoop_calls, smithIsolatePivotEuclidLoop_projection]
  calc
    _ ≤ m*fuel+n*fuel := Nat.add_le_add (Nat.mul_le_mul_left m hc) (Nat.mul_le_mul_left n hr)
    _ = _ := (Nat.add_mul _ _ _).symm

/-- The Euclidean call count of pivot isolation is at most `(m+n)*((A 0 0).natAbs + 1)`. -/
theorem smithIsolatePivotEuclid_calls_bound {m n : ℕ}
    (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) :
    (smithIsolatePivotEuclid A).2.calls ≤ (m+n)*((A 0 0).natAbs+1) :=
  smithIsolatePivotEuclidLoop_calls_bound _ _

/-- The Euclidean call count of rectangular Smith reduction is at most `m+n` times its total
allocated pivot fuel. -/
theorem smithRectangularEuclid_calls_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    (smithRectangularEuclid A).2.calls ≤
      (m+n)*(smithRectangularEuclid A).1.2 .pivotFuelAllocated := by
  induction m generalizing n with
  | zero => simp [smithRectangularEuclid, SmithEuclidWork.zero]
  | succ m ih =>
    cases n with
    | zero => simp [smithRectangularEuclid, SmithEuclidWork.zero]
    | succ n =>
      simp only [smithRectangularEuclid, tableMatrix_matrixTable]
      split
      · simp [SmithEuclidWork.zero]
      · rename_i rc he
        let B := (movePivot rc A).value
        let U := (smithIsolatePivotEuclid B).1.1.value.submatrix Fin.succ Fin.succ
        let total := smithCharge .rectangularFrame 1 + smithCharge .tabulateCell ((m+1)*(n+1)) +
          smithCharge .nonzeroTest
            (smithFindCounted (fun rc => decide (A rc.1 rc.2 ≠ 0))
              ((List.finRange (m+1)).product (List.finRange (n+1)))).2 +
          smithCharge .movePivot 1 + smithCharge .basisCompose 3 + smithCharge .liftResidual 1 +
          (smithIsolatePivotEuclid B).1.2 + (smithRectangularEuclid U).1.2
        have ht := smithIsolatePivotEuclid_calls_bound B
        have hu := ih U
        change (smithIsolatePivotEuclid B).2.calls+(smithRectangularEuclid U).2.calls ≤
          ((m+1)+(n+1))*total .pivotFuelAllocated
        have hf : total .pivotFuelAllocated = ((B 0 0).natAbs+1) +
            (smithRectangularEuclid U).1.2 .pivotFuelAllocated := by
          simp only [total, Pi.add_apply, smithIsolatePivotEuclid_projection]
          simp [smithCharge]
        rw [hf]
        calc
          _ ≤ (m+n)*(((B 0 0).natAbs+1)+(smithRectangularEuclid U).1.2 .pivotFuelAllocated) := by
            rw [Nat.mul_add]
            exact Nat.add_le_add ht hu
          _ ≤ _ := Nat.mul_le_mul_right _ (by omega : m+n ≤ (m+1)+(n+1))

/-- The quotient-remainder pair count of rectangular Smith reduction is at most `(m+n)*F*(2*B +
2)`, where `F` is its allocated pivot fuel and `B` its recorded peak input bit size. -/
theorem smithRectangularEuclid_division_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    (smithRectangularEuclid A).2.quotRemPairs ≤
      (m+n)*(smithRectangularEuclid A).1.2 .pivotFuelAllocated *
        (2*(smithRectangularEuclid A).2.peakPairInputBits+2) := by
  have hw := smithRectangularEuclid_valid A
  have hc := smithRectangularEuclid_calls_bound A
  exact hw.trans (Nat.mul_le_mul_right _ hc)

/-- Discarding the Euclidean work record from the instrumented binary Smith procedure yields the
ordinary counted binary procedure. -/
@[simp] theorem smithRunBinaryEuclid_projection {m n : ℕ}
    (rows : Vector (Vector SmithIntegerCode n) m) :
    (smithRunBinaryEuclid rows).1 = countedSmithRunBinary rows := by
  simp only [smithRunBinaryEuclid, countedSmithRunBinary, countedNormalizedSmith,
    smithRectangularEuclid_projection]

/-- The value component of the instrumented binary Smith procedure equals the ordinary binary
procedure's output. -/
@[simp] theorem smithRunBinaryEuclid_value {m n : ℕ} (rows : Vector (Vector SmithIntegerCode n) m) :
    (smithRunBinaryEuclid rows).1.1 = smithRunBinary rows := by simp

/-- The instrumented binary Smith procedure on encoded integer relations returns their
normalized Smith data as its value component. -/
@[simp] theorem smithRunBinaryEuclid_encode {m n : ℕ} (rows : Vector (Vector ℤ n) m) :
    (smithRunBinaryEuclid (smithEncodeRelations rows)).1.1 = normalizedSmith rows := by simp

/-- Each control-operation count of the instrumented binary Smith procedure is bounded by the
rectangular budget evaluated at its total allocated pivot fuel. -/
theorem smithRunBinaryEuclid_control_bound {m n : ℕ}
    (rows : Vector (Vector SmithIntegerCode n) m) (op : SmithKernelOp) :
    (smithRunBinaryEuclid rows).1.2 op ≤
      smithRectangularBudget m n ((smithRunBinaryEuclid rows).1.2 .pivotFuelAllocated) op := by
  simpa only [smithRunBinaryEuclid_projection] using! countedSmithRunBinary_bound rows op

/-- The binary Smith procedure's quotient-remainder pair count is at most `(m+n)*F*(2*B + 2)`,
where `F` is its allocated pivot fuel and `B` its recorded peak input bit size. -/
theorem smithRunBinaryEuclid_division_bound {m n : ℕ}
    (rows : Vector (Vector SmithIntegerCode n) m) :
    (smithRunBinaryEuclid rows).2.quotRemPairs ≤
      (m+n)*(smithRunBinaryEuclid rows).1.2 .pivotFuelAllocated *
        (2*(smithRunBinaryEuclid rows).2.peakPairInputBits+2) :=
  smithRectangularEuclid_division_bound _

/-- The instrumented binary Smith procedure returns equal factor lists for binary presentations
of isomorphic finite groups. -/
theorem smithRunBinaryEuclid_factors_invariant {m n m' n' : ℕ}
    (rows : Vector (Vector SmithIntegerCode n) m) (rows' : Vector (Vector SmithIntegerCode n') m')
    (hf : (smithRunBinaryEuclid rows).1.1.isFinite = true)
    (e : PresentationModule (tableMatrix (smithDecodeRelations rows)) ≃+
      PresentationModule (tableMatrix (smithDecodeRelations rows'))) :
    (smithRunBinaryEuclid rows).1.1.factors = (smithRunBinaryEuclid rows').1.1.factors := by
  simp only [smithRunBinaryEuclid_value, smithRunBinary] at hf ⊢
  exact normalizedSmith_factors_invariant _ _ hf e

/-- A positive proper divisor of a natural number has strictly smaller binary size. -/
theorem smith_size_strict_of_proper_dvd (a b : ℕ) (ha : 0 < a) (hab : a ∣ b) (hlt : a < b) :
    a.size < b.size := by
  obtain ⟨k,hk⟩ := hab
  have hk2 : 2 ≤ k := by
    cases k with
    | zero => simp at hk; omega
    | succ k =>
      cases k with
      | zero => simp at hk; omega
      | succ k => omega
  have htwo : a*2 ≤ b := (Nat.mul_le_mul_left a hk2).trans_eq hk.symm
  have hsize : (a*2).size = a.size+1 := by
    simpa only [Nat.shiftLeft_eq_mul_pow, pow_one] using! Nat.size_shiftLeft (Nat.ne_of_gt ha) 1
  have h := Nat.size_le_size htwo
  rw [hsize] at h
  omega

/-- If a nonzero column pivot fails to divide some entry in its column, column reduction
strictly decreases the binary size of its absolute value. -/
theorem columnReduce_pivot_size_strict {m n : ℕ} (p : Fin n)
    (A : Matrix (Fin (m+1)) (Fin n) ℤ) (h0 : A 0 p ≠ 0) (hbad : ∃ r, ¬ A 0 p ∣ A r p) :
    ((columnReduce p A).value 0 p).natAbs.size < (A 0 p).natAbs.size := by
  have hd : (columnReduce p A).value 0 p ∣ A 0 p :=
    ((columnReduce_dvd_iff p A _).mpr (dvd_refl _)) 0
  exact smith_size_strict_of_proper_dvd _ _
    (Int.natAbs_pos.mpr (columnReduce_pivot_ne_zero p A h0))
    (Int.natAbs_dvd_natAbs.mpr hd) (columnReduce_pivot_strict p A h0 hbad)

/-- If a nonzero row pivot fails to divide some entry in its row, row reduction strictly
decreases the binary size of its absolute value. -/
theorem rowReduce_pivot_size_strict {m n : ℕ} (p : Fin m)
    (A : Matrix (Fin m) (Fin (n+1)) ℤ) (h0 : A p 0 ≠ 0) (hbad : ∃ c, ¬ A p 0 ∣ A p c) :
    ((rowReduce p A).value p 0).natAbs.size < (A p 0).natAbs.size :=
  columnReduce_pivot_size_strict p A.transpose h0 hbad

/-- For a nonzero leading pivot, the pivot-isolation loop records at most its initial absolute
binary size in pivot rounds. -/
theorem countedIsolatePivotLoop_bit_rounds {m n : ℕ} (fuel : ℕ)
    (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) (h0 : A 0 0 ≠ 0) :
    (countedIsolatePivotLoop fuel A).2 .pivotRound ≤ (A 0 0).natAbs.size := by
  induction fuel generalizing A with
  | zero => simp [countedIsolatePivotLoop]
  | succ fuel ih =>
    have hbits : 0 < (A 0 0).natAbs.size := Nat.size_pos.mpr (Int.natAbs_pos.mpr h0)
    simp only [countedIsolatePivotLoop, tableMatrix_matrixTable]
    by_cases hc : ∀ r, A 0 0 ∣ A r 0
    · have hcb := (smithCheckAllFin_true _).mpr hc
      simp only [hcb]
      by_cases hr : ∀ c, A 0 0 ∣ A 0 c
      · have hrb := (smithCheckAllFin_true _).mpr hr
        simp only [hrb, ↓reduceIte, smithFindCounted_value]
        cases hsearch : badPivotEntry (clearPivot A).value with
        | none =>
          have hfind := hsearch
          unfold badPivotEntry at hfind
          simp only [hfind]
          simpa [smithCharge, Pi.add_apply] using! hbits
        | some rc =>
          have hs := clearPivot_correct A hc hr
          have he := exposeRow_bad (clearPivot A).value hs.2.2.1 hs.2.2.2 rc
            (badPivotEntry_some _ rc hsearch)
          have he0 : (exposeRow rc.1 (clearPivot A).value).value 0 0 ≠ 0 := by
            rw [he.1, hs.2.1]
            exact h0
          have hdec := rowReduce_pivot_size_strict 0 _ he0 he.2
          have hrec := ih _ (rowReduce_pivot_ne_zero 0 _ he0)
          rw [he.1, hs.2.1] at hdec
          have hfind := hsearch
          unfold badPivotEntry at hfind
          simp only [hfind]
          simp [smithCharge, Pi.add_apply, ColumnEliminationState.toReduction,
            RowEliminationState.toReduction] at *
          omega
      · have hrb : (smithCheckAllFin (fun c => A 0 0 ∣ A 0 c)).1 = false :=
          Bool.eq_false_iff.mpr (fun h => hr ((smithCheckAllFin_true _).mp h))
        have hdec := rowReduce_pivot_size_strict 0 A h0 (not_forall.mp hr)
        have hrec := ih _ (rowReduce_pivot_ne_zero 0 A h0)
        simp only [hrb]
        simp [smithCharge, Pi.add_apply, RowEliminationState.toReduction] at *
        omega
    · have hcb : (smithCheckAllFin (fun r => A 0 0 ∣ A r 0)).1 = false :=
        Bool.eq_false_iff.mpr (fun h => hc ((smithCheckAllFin_true _).mp h))
      have hdec := columnReduce_pivot_size_strict 0 A h0 (not_forall.mp hc)
      have hrec := ih _ (columnReduce_pivot_ne_zero 0 A h0)
      simp only [hcb]
      simp [smithCharge, Pi.add_apply, ColumnEliminationState.toReduction] at *
      omega

/-- For a nonzero leading pivot, counted pivot isolation records at most its initial absolute
binary size in pivot rounds. -/
theorem countedIsolatePivot_bit_rounds {m n : ℕ}
    (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) (h0 : A 0 0 ≠ 0) :
    (countedIsolatePivot A).2 .pivotRound ≤ (A 0 0).natAbs.size := by
  simpa [countedIsolatePivot, smithCharge, Pi.add_apply] using!
      countedIsolatePivotLoop_bit_rounds _ A h0

/-- Each operation count of the pivot-isolation loop is bounded by its recorded pivot-round
count times the corresponding per-round budget. -/
theorem countedIsolatePivotLoop_round_bound {m n : ℕ} (fuel : ℕ)
    (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) (op : SmithKernelOp) :
    (countedIsolatePivotLoop fuel A).2 op ≤ (countedIsolatePivotLoop fuel A).2 .pivotRound * smithPivotRoundBudget (m+1) (n+1) op := by
  induction fuel generalizing A with
  | zero => simp [countedIsolatePivotLoop]
  | succ fuel ih =>
    have hc := smithCheckAllFin_bound (fun r => A 0 0 ∣ A r 0)
    have hr := smithCheckAllFin_bound (fun c => A 0 0 ∣ A 0 c)
    have hb : (smithFindCounted (fun rc => decide (¬ (clearPivot A).value 0 0 ∣
        (clearPivot A).value rc.1 rc.2))
        ((List.finRange (m+1)).product (List.finRange (n+1)))).2 ≤ (m+1)*(n+1) := by
      calc
        _ ≤ ((List.finRange (m+1)).product (List.finRange (n+1))).length :=
          smithFindCounted_bound _ _
        _ = _ := by simpa only [List.length_finRange] using!
          List.length_product (List.finRange (m+1)) (List.finRange (n+1))
    simp only [countedIsolatePivotLoop, tableMatrix_matrixTable]
    split
    · split
      · split <;> simp only [*]
        · cases op <;> simp [smithCharge, smithPivotRoundBudget, Pi.add_apply,
            Nat.add_mul] at * <;> omega
        · rename_i rc he
          have hi := ih (rowReduce 0 (exposeRow rc.1 (clearPivot A).value).value).value
          cases op <;> simp [smithCharge, smithPivotRoundBudget, Pi.add_apply, Nat.add_mul,
            RowEliminationState.toReduction, ColumnEliminationState.toReduction] at * <;> omega
      · have hi := ih (rowReduce 0 A).value
        cases op <;> simp [smithCharge, smithPivotRoundBudget, Pi.add_apply, Nat.add_mul,
            RowEliminationState.toReduction] at * <;> omega
    · have hi := ih (columnReduce 0 A).value
      cases op <;> simp [smithCharge, smithPivotRoundBudget, Pi.add_apply, Nat.add_mul,
            ColumnEliminationState.toReduction] at * <;> omega

/-- For a nonzero leading pivot, each loop operation count is bounded by the binary size of its
initial absolute value times the corresponding per-round budget. -/
theorem countedIsolatePivotLoop_bit_bound {m n : ℕ} (fuel : ℕ)
    (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) (h0 : A 0 0 ≠ 0) (op : SmithKernelOp) :
    (countedIsolatePivotLoop fuel A).2 op ≤
      (A 0 0).natAbs.size*smithPivotRoundBudget (m+1) (n+1) op := by
  exact (countedIsolatePivotLoop_round_bound fuel A op).trans
    (Nat.mul_le_mul_right _ (countedIsolatePivotLoop_bit_rounds fuel A h0))

/-- For a nonzero leading pivot, the pivot-isolation loop records at most `m+n` times the binary
size of its initial absolute value in Euclidean calls. -/
theorem smithIsolatePivotEuclidLoop_bit_calls {m n : ℕ} (fuel : ℕ)
    (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) (h0 : A 0 0 ≠ 0) :
    (smithIsolatePivotEuclidLoop fuel A).2.calls ≤ (m+n)*(A 0 0).natAbs.size := by
  have hc : (countedIsolatePivotLoop fuel A).2 .columnSweep ≤ (A 0 0).natAbs.size := by
    simpa only [smithPivotRoundBudget, mul_one] using!
        countedIsolatePivotLoop_bit_bound fuel A h0 .columnSweep
  have hr : (countedIsolatePivotLoop fuel A).2 .rowSweep ≤ (A 0 0).natAbs.size := by
    simpa only [smithPivotRoundBudget, mul_one] using!
        countedIsolatePivotLoop_bit_bound fuel A h0 .rowSweep
  rw [smithIsolatePivotEuclidLoop_calls, smithIsolatePivotEuclidLoop_projection]
  calc
    _ ≤ m*(A 0 0).natAbs.size+n*(A 0 0).natAbs.size :=
      Nat.add_le_add (Nat.mul_le_mul_left m hc) (Nat.mul_le_mul_left n hr)
    _ = _ := (Nat.add_mul _ _ _).symm

end Qatlib.Concepts.IntWordFraming.WordFraming
