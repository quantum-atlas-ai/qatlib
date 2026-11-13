/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BeyondCircuit08.MainResults.HalfSupport.HalfSet

/-!
# Clearing columns with half-support factors

The list type `HalfSupports` records coordinate sets together with matrices, while `AllHalf`
requires each set to have size `m / 2` and each matrix to be unitary and fix its complement. The
elementary operation `twoLevelOp` eliminates a selected entry using two rows.

For `m ≥ 4`, the column-clearing theorems assemble these operations into a finite product,
preserving the chosen column's entries outside the selected list except at row zero. This
supplies column elimination for the half-support development of [Jordan2008].

## Main statements

* `clear_list`: clears a list of distinct nonzero rows in a chosen column.
* `exists_halfSupports_clear_column`: clears every row except row zero in a chosen column using
  half-support factors.

## References

* [Jordan, 2008][Jordan2008]
-/

set_option autoImplicit false
noncomputable section

open scoped Matrix BigOperators

namespace Qatlib.Papers.BeyondCircuit08.MainResults.HalfSupport

variable {m : ℕ}

/-- Lists of pairs consisting of a finite set of coordinate indices and a complex square matrix. -/
abbrev HalfSupports (m : ℕ) : Type :=
  List (Finset (Fin m) × Matrix (Fin m) (Fin m) ℂ)

/-- The ordered product of the matrix components of a list of support-matrix pairs. -/
def halfProd {m : ℕ} (L : HalfSupports m) : Matrix (Fin m) (Fin m) ℂ :=
  (L.map (fun p => p.2)).prod

/-- The property that every listed support has size `m / 2` and its matrix is unitary and fixes
the support's complement. -/
def AllHalf {m : ℕ} (L : HalfSupports m) : Prop :=
  ∀ p ∈ L, p.1.card = m / 2 ∧ FixesComplement p.1 p.2

/-- The two-row matrix operation built from column `k` at rows `i` and `j`, with coefficients
normalized by `twoLevelNorm`. -/
def twoLevelOp (U : Matrix (Fin m) (Fin m) ℂ) (i j k : Fin m) :
    Matrix (Fin m) (Fin m) ℂ :=
  elemOp i j (star (U i k) / twoLevelNorm (U i k) (U j k))
    (star (U j k) / twoLevelNorm (U i k) (U j k))
    (U j k / twoLevelNorm (U i k) (U j k))
    (-(U i k) / twoLevelNorm (U i k) (U j k))

/-- For distinct `i` and `j`, left multiplication by `twoLevelOp U i j k` makes entry `(j, k)`
zero. -/
theorem twoLevelOp_zero (U : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m)
    (hij : i ≠ j) (k : Fin m) : (twoLevelOp U i j k * U) j k = 0 :=
  elemOp_twoLevel_zero U i j hij k

/-- Left multiplication by `twoLevelOp U i j k` leaves entry `(r, k)` unchanged whenever `r`
differs from both selected rows. -/
theorem twoLevelOp_row_other (U : Matrix (Fin m) (Fin m) ℂ) (i j r : Fin m)
    (hij : i ≠ j) (hri : r ≠ i) (hrj : r ≠ j) (k : Fin m) :
    (twoLevelOp U i j k * U) r k = U r k :=
  elemOp_mul_apply_other U i j r hij hri hrj _ _ _ _ k

/-- If the selected rows lie in `S` and their column entries are not both zero, `twoLevelOp U i
j k` is unitary and fixes the complement of `S`. -/
theorem twoLevelOp_fixes (U : Matrix (Fin m) (Fin m) ℂ) {S : Finset (Fin m)}
    {i j : Fin m} (hij : i ≠ j) (hi : i ∈ S) (hj : j ∈ S) {k : Fin m}
    (hne : U i k ≠ 0 ∨ U j k ≠ 0) : FixesComplement S (twoLevelOp U i j k) :=
  elemOp_twoLevel_fixes U hij hi hj hne

/-- For `m ≥ 4`, a list of distinct rows excluding zero can be cleared in a selected column by a
product of half-support unitaries, preserving that column's entries in all other rows except
row zero [Jordan2008]. -/
theorem clear_list [NeZero m] (U : Matrix (Fin m) (Fin m) ℂ) (hm : 4 ≤ m) (k : Fin m)
    (rs : List (Fin m)) (h0 : (0 : Fin m) ∉ rs) (hnd : rs.Nodup) :
    ∃ L : HalfSupports m, AllHalf L ∧
      (∀ r ∈ rs, (halfProd L * U) r k = 0) ∧
      (∀ p, p ∉ rs → p ≠ 0 → (halfProd L * U) p k = U p k) := by
  induction rs with
  | nil =>
      refine ⟨[], ?_, ?_, ?_⟩
      · intro p hp; exact absurd hp (by simp)
      · intro r hr; exact absurd hr (by simp)
      · intro p _ _; simp [halfProd]
  | cons r rs ih =>
      have hr0 : r ≠ 0 := by
        rintro rfl; exact h0 List.mem_cons_self
      have hr_notin : r ∉ rs := (List.nodup_cons.mp hnd).1
      have h0' : (0 : Fin m) ∉ rs := fun h => h0 (List.mem_cons_of_mem _ h)
      have hnd' : rs.Nodup := (List.nodup_cons.mp hnd).2
      obtain ⟨L, hAll, hclear, hpres⟩ := ih h0' hnd'
      set U' := halfProd L * U with hU'
      by_cases hz : U' r k = 0
      · refine ⟨L, hAll, ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with h | h
          · rw [h]; exact hz
          · exact hclear x h
        · intro p hp hp0
          exact hpres p (fun h => hp (List.mem_cons_of_mem _ h)) hp0
      · have h0r : (0 : Fin m) ≠ r := Ne.symm hr0
        obtain ⟨S, hcard, h0S, hrS⟩ := exists_halfSet hm h0r
        refine ⟨(S, twoLevelOp U' 0 r k) :: L, ?_, ?_, ?_⟩
        · intro p hp
          rcases List.mem_cons.mp hp with h | h
          · rw [h]
            exact ⟨hcard, twoLevelOp_fixes U' h0r h0S hrS (Or.inr hz)⟩
          · exact hAll p h
        · intro x hx
          rw [show halfProd ((S, twoLevelOp U' 0 r k) :: L) * U =
              twoLevelOp U' 0 r k * U' by simp [halfProd, hU', Matrix.mul_assoc]]
          rcases List.mem_cons.mp hx with h | h
          · rw [h]; exact twoLevelOp_zero U' 0 r h0r k
          · have hxr : x ≠ r := by rintro rfl; exact hr_notin h
            have hx0 : x ≠ 0 := by rintro rfl; exact h0' h
            rw [twoLevelOp_row_other U' 0 r x h0r hx0 hxr k]
            exact hclear x h
        · intro p hp hp0
          rw [show halfProd ((S, twoLevelOp U' 0 r k) :: L) * U =
              twoLevelOp U' 0 r k * U' by simp [halfProd, hU', Matrix.mul_assoc]]
          have hpr : p ≠ r := by rintro rfl; exact hp List.mem_cons_self
          have hprs : p ∉ rs := fun h => hp (List.mem_cons_of_mem _ h)
          rw [twoLevelOp_row_other U' 0 r p h0r hp0 hpr k, hU']
          exact hpres p hprs hp0

/-- For `m ≥ 4`, a product of half-support unitaries clears every nonzero row index in a
selected column of any complex square matrix [Jordan2008]. -/
theorem exists_halfSupports_clear_column [NeZero m] (U : Matrix (Fin m) (Fin m) ℂ)
    (hm : 4 ≤ m) (k : Fin m) :
    ∃ L : HalfSupports m, AllHalf L ∧
      ∀ r : Fin m, r ≠ 0 → (halfProd L * U) r k = 0 := by
  have hnd : ((Finset.univ.erase (0 : Fin m)).toList).Nodup :=
    Finset.nodup_toList _
  have h0 : (0 : Fin m) ∉ (Finset.univ.erase (0 : Fin m)).toList := by
    simp [Finset.mem_erase]
  obtain ⟨L, hAll, hclear, _⟩ :=
    clear_list U hm k ((Finset.univ.erase (0 : Fin m)).toList) h0 hnd
  refine ⟨L, hAll, fun r hr => ?_⟩
  exact hclear r (by
    rw [Finset.mem_toList, Finset.mem_erase]
    exact ⟨hr, Finset.mem_univ _⟩)

end Qatlib.Papers.BeyondCircuit08.MainResults.HalfSupport
