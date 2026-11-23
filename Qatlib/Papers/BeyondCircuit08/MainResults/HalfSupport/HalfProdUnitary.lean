/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BeyondCircuit08.MainResults.HalfSupport.ColumnClear

@[expose] public section

/-!
# Products of half-support unitaries (Lemma 4)

Paper: Stephen P. Jordan, *Quantum Computation Beyond the Circuit Model*,
arXiv:0809.2307v1 (2008), Lemma 4, p. 85.

Lemma 4 writes an arbitrary unitary as a product of seven half-support
unitaries.  The public library proves the column-clearing engine
(`exists_halfSupports_clear_column`): finitely many half-support factors
clear one column.  Assembling such steps into the proof of Lemma 4 needs
the closure properties proved here: the product of the listed
half-support factors is itself unitary, and it fixes the complement of
any common superset of the listed supports, so the clearing products can
be composed and iterated over columns.

## Main statements

* `halfProd_mem_unitaryGroup`: a product of half-support factors is
  unitary.
* `halfProd_fixes_complement`: such a product fixes the complement of
  any finset containing every listed support.
* `exists_unitary_halfProd_clear_column`: for `m ≥ 4`, a list of
  half-support factors has a unitary product that clears a prescribed column.
-/

set_option autoImplicit false
noncomputable section

open scoped Matrix Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.BeyondCircuit08.MainResults.HalfSupport

open Qatlib.Papers.BeyondCircuit08.MainResults.HalfSupport

/-- The ordered product of a list of half-support factors is unitary:
each factor is unitary by `AllHalf` (through `FixesComplement`), and the
unitary group is closed under multiplication. -/
theorem halfProd_mem_unitaryGroup {m : ℕ} {L : HalfSupports m}
    (hAll : AllHalf L) :
    halfProd L ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  induction L with
  | nil =>
      simp only [halfProd, List.map_nil, List.prod_nil]
      exact one_mem _
  | cons p L ih =>
      have hp : p.2 ∈ Matrix.unitaryGroup (Fin m) ℂ :=
        (hAll p List.mem_cons_self).2.1
      have hL : AllHalf L := fun q hq => hAll q (List.mem_cons_of_mem p hq)
      have hprod : halfProd (p :: L) = p.2 * halfProd L := by
        simp [halfProd]
      rw [hprod]
      exact mul_mem hp (ih hL)

/-- The ordered product of half-support factors fixes the complement of
any finset `S` containing every listed support: in a row outside `S` the
leftmost factor acts as the identity row, and in a column outside `S`
every factor's tail product acts as the identity column, so the product
agrees with the identity matrix whenever either index lies outside `S`. -/
theorem halfProd_fixes_complement {m : ℕ} {L : HalfSupports m}
    (hAll : AllHalf L) {S : Finset (Fin m)}
    (hsub : ∀ p ∈ L, p.1 ⊆ S) :
    FixesComplement S (halfProd L) := by
  refine ⟨halfProd_mem_unitaryGroup hAll, ?_⟩
  induction L with
  | nil =>
      intro i j _
      simp [halfProd, Matrix.one_apply]
  | cons p L ih =>
      intro i j hij
      have hp : FixesComplement p.1 p.2 :=
        (hAll p List.mem_cons_self).2
      have hL : AllHalf L := fun q hq => hAll q (List.mem_cons_of_mem p hq)
      have hsubL : ∀ q ∈ L, q.1 ⊆ S :=
        fun q hq => hsub q (List.mem_cons_of_mem p hq)
      have hpS : p.1 ⊆ S := hsub p List.mem_cons_self
      have hentry : ∀ x y : Fin m, (x ∉ S ∨ y ∉ S) →
          halfProd L x y = if x = y then (1 : ℂ) else 0 :=
        ih hL hsubL
      have hprod : halfProd (p :: L) = p.2 * halfProd L := by
        simp [halfProd]
      rw [hprod, Matrix.mul_apply]
      rcases hij with hi | hj
      · have hi' : i ∉ p.1 := fun h => hi (hpS h)
        have hrow : ∀ k, p.2 i k = if i = k then (1 : ℂ) else 0 :=
          fun k => hp.2 i k (Or.inl hi')
        refine (Finset.sum_eq_single i (fun k _ hk => ?_) (by simp)).trans ?_
        · rw [hrow k, ite_eq_right (Ne.symm hk), zero_mul]
        · rw [hrow i, ite_eq_left rfl, one_mul]
          exact hentry i j (Or.inl hi)
      · have hj' : j ∉ p.1 := fun h => hj (hpS h)
        have hcol : ∀ k, halfProd L k j = if k = j then (1 : ℂ) else 0 :=
          fun k => hentry k j (Or.inr hj)
        refine (Finset.sum_eq_single j (fun k _ hk => ?_) (by simp)).trans ?_
        · rw [hcol k, ite_eq_right hk, mul_zero]
        · rw [hcol j, ite_eq_left rfl, mul_one]
          exact hp.2 i j (Or.inr hj')

/-- For `m ≥ 4`, any matrix has a prescribed column cleared by a single
unitary that is a product of half-support factors: this packages
`exists_halfSupports_clear_column` together with
`halfProd_mem_unitaryGroup`, giving the composable unitary step needed to
iterate column clearing in the proof of Lemma 4 of [Jordan2008]. -/
theorem exists_unitary_halfProd_clear_column {m : ℕ} [NeZero m]
    (U : Matrix (Fin m) (Fin m) ℂ) (hm : 4 ≤ m) (k : Fin m) :
    ∃ L : HalfSupports m, AllHalf L ∧
      halfProd L ∈ Matrix.unitaryGroup (Fin m) ℂ ∧
        ∀ r : Fin m, r ≠ 0 → (halfProd L * U) r k = 0 := by
  obtain ⟨L, hAll, hclear⟩ := exists_halfSupports_clear_column U hm k
  exact ⟨L, hAll, halfProd_mem_unitaryGroup hAll, hclear⟩

end Qatlib.Papers.BeyondCircuit08.MainResults.HalfSupport
