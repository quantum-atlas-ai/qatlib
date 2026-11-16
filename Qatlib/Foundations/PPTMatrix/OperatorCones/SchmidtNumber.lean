/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.Separable

@[expose] public section




/-!
# Schmidt rank and Schmidt number: basic properties

* closure of `HasSchmidtNumberLE k` under zero, sums and enlarging `k`;
* `schmidtNumber X ≤ k` from a decomposition, and the convention `SN(0) = 0`;
* the coefficient matrix of `(L ⊗ K) v` is `L V Kᵀ`, so local linear maps cannot increase
  Schmidt rank (consequence 3 of the definition in the manuscript).
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace Qatlib.Foundations.PPTMatrix.OperatorCones

variable {κ κ' n n' : Type*}

section decompositions

variable [Fintype n]

/-- A sum of pure operators of Schmidt rank at most `k` over any finite index type. -/
theorem hasSchmidtNumberLE_sum {ι : Type*} [Fintype ι] {k : ℕ} (v : ι → κ × n → ℂ)
    (h : ∀ i, schmidtRank (v i) ≤ k) : HasSchmidtNumberLE k (∑ i, pureState (v i)) := by
  classical
  refine ⟨Fintype.card ι, fun j => v ((Fintype.equivFin ι).symm j), fun j => h _, ?_⟩
  exact (Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => pureState (v i))).symm

/-- Establishes `HasSchmidtNumberLE.zero`: `HasSchmidtNumberLE k (0 : Matrix (κ × n) (κ × n) ℂ)`, for the stated parameters. -/
theorem HasSchmidtNumberLE.zero (k : ℕ) :
    HasSchmidtNumberLE k (0 : Matrix (κ × n) (κ × n) ℂ) :=
  ⟨0, fun i => i.elim0, fun i => i.elim0, by simp⟩

/-- Establishes `HasSchmidtNumberLE.mono`: `HasSchmidtNumberLE l X`, for the stated parameters. -/
theorem HasSchmidtNumberLE.mono {k l : ℕ} {X : Matrix (κ × n) (κ × n) ℂ} (hkl : k ≤ l)
    (h : HasSchmidtNumberLE k X) : HasSchmidtNumberLE l X := by
  obtain ⟨N, v, hv, rfl⟩ := h
  exact ⟨N, v, fun α => (hv α).trans hkl, rfl⟩

/-- Establishes `HasSchmidtNumberLE.add`: `HasSchmidtNumberLE k (X + Y)`, for the stated parameters. -/
theorem HasSchmidtNumberLE.add {k : ℕ} {X Y : Matrix (κ × n) (κ × n) ℂ}
    (hX : HasSchmidtNumberLE k X) (hY : HasSchmidtNumberLE k Y) :
    HasSchmidtNumberLE k (X + Y) := by
  obtain ⟨N, v, hv, rfl⟩ := hX
  obtain ⟨N', w, hw, rfl⟩ := hY
  have h := hasSchmidtNumberLE_sum (ι := Fin N ⊕ Fin N') (k := k) (Sum.elim v w)
    (by rintro (i | i) <;> simp [hv, hw])
  simpa [Fintype.sum_sum_type] using h

/-- Establishes `HasSchmidtNumberLE.sum`: `HasSchmidtNumberLE k (∑ i ∈ s, X i)`, for the stated parameters. -/
theorem HasSchmidtNumberLE.sum {ι : Type*} (s : Finset ι) {k : ℕ}
    {X : ι → Matrix (κ × n) (κ × n) ℂ} (h : ∀ i ∈ s, HasSchmidtNumberLE k (X i)) :
    HasSchmidtNumberLE k (∑ i ∈ s, X i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using (HasSchmidtNumberLE.zero k : HasSchmidtNumberLE k (0 : Matrix (κ × n) (κ × n) ℂ))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A decomposition with Schmidt ranks at most `k` bounds the Schmidt number by `k`. -/
theorem schmidtNumber_le {k : ℕ} {X : Matrix (κ × n) (κ × n) ℂ} (h : HasSchmidtNumberLE k X) :
    schmidtNumber X ≤ k :=
  Nat.sInf_le h

/-- If some decomposition exists, the Schmidt number is attained. -/
theorem hasSchmidtNumberLE_schmidtNumber {k : ℕ} {X : Matrix (κ × n) (κ × n) ℂ}
    (h : HasSchmidtNumberLE k X) : HasSchmidtNumberLE (schmidtNumber X) X :=
  Nat.sInf_mem (s := {k | HasSchmidtNumberLE k X}) ⟨k, h⟩

/-- The convention `SN(0) = 0`. -/
theorem schmidtNumber_zero : schmidtNumber (0 : Matrix (κ × n) (κ × n) ℂ) = 0 :=
  Nat.le_zero.mp (schmidtNumber_le (HasSchmidtNumberLE.zero 0))

end decompositions

section local_maps

variable [Fintype κ] [Fintype n]

/-- The coefficient matrix of `(L ⊗ K) v` is `L V Kᵀ`. -/
theorem coeffMatrix_kronecker_mulVec (L : Matrix κ' κ ℂ) (K : Matrix n' n ℂ) (v : κ × n → ℂ) :
    coeffMatrix ((L ⊗ₖ K) *ᵥ v) = L * coeffMatrix v * Kᵀ := by
  ext i a
  simp only [coeffMatrix_apply, Matrix.mulVec, dotProduct, kroneckerMap_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Local linear maps cannot increase Schmidt rank. -/
theorem schmidtRank_kronecker_mulVec_le [Fintype n'] (L : Matrix κ' κ ℂ) (K : Matrix n' n ℂ)
    (v : κ × n → ℂ) : schmidtRank ((L ⊗ₖ K) *ᵥ v) ≤ schmidtRank v := by
  unfold schmidtRank
  rw [coeffMatrix_kronecker_mulVec]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

end local_maps

end Qatlib.Foundations.PPTMatrix.OperatorCones
