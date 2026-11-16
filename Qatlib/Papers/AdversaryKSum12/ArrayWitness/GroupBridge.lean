/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdversaryKSum12.ArrayWitness.SourceModel

@[expose] public section


set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace Qatlib.Papers.AdversaryKSum12.ArrayWitness
open Qatlib.Papers.AdversaryKSum12.ArrayWitness

/-! ## The group orthogonal arrays of Example 3 -/

/-- The sum over the coordinates of `Fin k` other than `i`, with the dependent
proof of inequality kept as a `dif`. -/
def sumOthers {G : Type} [AddCommMonoid G] {k : ℕ} (i : Fin k)
    (g : {j : Fin k // j ≠ i} → G) : G :=
  ∑ j ∈ Finset.univ.erase i, if h : j ≠ i then g ⟨j, h⟩ else 0

/-- Summing an `extendTuple` splits off the overwritten coordinate. -/
theorem sum_extendTuple {G : Type} [AddCommMonoid G] {k : ℕ} (i : Fin k)
    (g : {j : Fin k // j ≠ i} → G) (a : G) :
    ∑ j : Fin k, extendTuple i g a j = sumOthers i g + a := by
  rw [← Finset.sum_erase_add (s := Finset.univ)
      (f := fun j : Fin k => extendTuple i g a j) (a := i) (Finset.mem_univ i)]
  rw [extendTuple_apply_self]
  simp only [sumOthers]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  simp [extendTuple, hji]

/-- **Example 3 (p.2).**  The array of all `k`-tuples summing to `t`. -/
def sumArray {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (t : G) (k : ℕ) : Finset (Fin k → G) :=
  Finset.univ.filter (fun v => ∑ i, v i = t)

/-- **Example 3 (p.2).**  The sum-to-`t` array is an orthogonal array: for
every `i` and every assignment of the other coordinates there is exactly one
value of coordinate `i` making the tuple sum to `t`, namely
`t −` (sum of the others). -/
theorem sumArray_isOrthogonalArray {G : Type} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (t : G) (k : ℕ) :
    IsOrthogonalArray (sumArray t k) := by
  intro i g
  refine ⟨t - sumOthers i g, ?_, ?_⟩
  · simp only [sumArray, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [sum_extendTuple]
    abel
  · intro a ha
    simp only [sumArray, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [sum_extendTuple] at ha
    exact eq_sub_of_add_eq (by simpa [add_comm] using ha)

/-! ## The k-sum / k-orthogonal-array correspondence -/

/-- The ordered projection `x ↦ x_S` on an arbitrary alphabet (the group
version of `restrictTo`, which is stated for `Fin q`). -/
def restrictToG {α : Type} {n k : ℕ} (S : Finset (Fin n)) (hS : S.card = k)
    (x : Fin n → α) : Fin k → α :=
  fun i => x (S.orderEmbOfFin hS i)

/-- The ordered projection `x ↦ x_S` sums to the same value as the unordered
`Finset` sum over `S`. -/
theorem sum_restrictTo {G : Type} [AddCommMonoid G] {n k : ℕ}
    (S : Finset (Fin n)) (hS : S.card = k) (x : Fin n → G) :
    ∑ i : Fin k, restrictToG S hS x i = ∑ i ∈ S, x i := by
  rw [← Finset.sum_coe_sort S (fun i : Fin n => x i)]
  refine Fintype.sum_equiv (S.orderIsoOfFin hS).toEquiv
    (fun i : Fin k => restrictToG S hS x i) (fun s : ↥S => x ↑s) ?_
  intro i
  simp only [restrictToG]
  exact (congrArg x (Finset.coe_orderIsoOfFin_apply S hS i)).symm

/-- **Theorem 1, reduction step (p.1).**  The `k`-sum instance `x` (for target
`t`) has a solution exactly when it is an illegal column for the sum-to-`t`
orthogonal arrays. -/
theorem kSum_iff_orthArray {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (t : G) (k : ℕ) {n : ℕ} (x : Fin n → G) :
    KSumProblem t k x ↔
      ∃ (S : Finset (Fin n)) (hS : S.card = k), restrictToG S hS x ∈ sumArray t k := by
  constructor
  · rintro ⟨S, hS, hsum⟩
    refine ⟨S, hS, ?_⟩
    simp only [sumArray, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [sum_restrictTo, hsum]
  · rintro ⟨S, hS, hmem⟩
    refine ⟨S, hS, ?_⟩
    simp only [sumArray, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rwa [sum_restrictTo] at hmem


end Qatlib.Papers.AdversaryKSum12.ArrayWitness
