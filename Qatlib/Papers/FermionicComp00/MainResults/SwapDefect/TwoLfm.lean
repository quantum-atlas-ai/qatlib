/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FermionicComp00.MainResults.SwapDefect.Basic

/-!
# Two-mode fermionic matrix units

`lfmUnit2` uses creation, annihilation, and vacuum projections to realize fermionic matrix
units; `lfmApply2` extends this by linear combination. The module computes their action on
computational basis vectors and proves agreement with qubit placement on the complete two-mode
register.

These constructions belong to the formalization of [BravyiKitaev2002].

## Main statements

* `lfmUnit2_two_eq_qubitUnit2`: fermionic and qubit matrix units agree on two modes.
* `lfmApply2_two_eq`: the two placements agree on the two-mode register.

## References

* [Bravyi and Kitaev, 2002][BravyiKitaev2002]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner

namespace Qatlib.Papers.FermionicComp00.MainResults.SwapDefect

/-- The natural-number value of a Boolean, zero for false and one for true. -/
def bitNat (b : Bool) : ℕ := if b then 1 else 0

/-- The fermionic two-mode matrix unit formed by annihilating the input occupations, projecting
onto vacancy, and creating the output occupations. -/
def lfmUnit2 {m : ℕ} (p q : Reg 2) (j k : Fin m) : Matrix (Reg m) (Reg m) ℂ :=
  creation j ^ (bitNat (p 0)) * creation k ^ (bitNat (p 1)) *
    ((1 - numberOp j) * (1 - numberOp k)) *
    annihilation k ^ (bitNat (q 1)) * annihilation j ^ (bitNat (q 0))

/-- The sum of fermionic two-mode matrix units weighted by the entries of `X`. -/
def lfmApply2 {m : ℕ} (X : Matrix (Reg 2) (Reg 2) ℂ) (j k : Fin m) :
    Matrix (Reg m) (Reg m) ℂ :=
  ∑ p : Reg 2, ∑ q : Reg 2, X p q • lfmUnit2 p q j k

/-- The matrix unit that replaces matching occupations at `j` and `k` by the output label and
preserves all other bits. -/
def qubitUnit2 {m : ℕ} (p q : Reg 2) (j k : Fin m) : Matrix (Reg m) (Reg m) ℂ :=
  Matrix.of fun y x =>
    if x j = q 0 ∧ x k = q 1 ∧
        y = Function.update (Function.update x j (p 0)) k (p 1) then 1 else 0

/-- The vacancy projection has diagonal entry one exactly when the selected bit is unoccupied,
and zero entries elsewhere. -/
theorem one_sub_numberOp_apply {m : ℕ} (i : Fin m) (y x : Reg m) :
    (1 - numberOp i : Matrix (Reg m) (Reg m) ℂ) y x =
      if y = x then (if x i then 0 else 1) else 0 := by
  rw [Matrix.sub_apply, Matrix.one_apply]
  by_cases h : y = x
  · rw [if_pos h]
    subst y
    rw [numberOp, Matrix.of_apply]
    simp only [eq_self, true_and, ite_true]
    by_cases hx : x i <;> simp [hx]
  · rw [if_neg h, numberOp, Matrix.of_apply]
    simp [h, Ne.symm h]

/-- The product of two vacancy projections is diagonal, with entries given by the product of
their vacancy indicators. -/
theorem one_sub_numberOp_mul_apply {m : ℕ} (j k : Fin m) (y x : Reg m) :
    ((1 - numberOp j) * (1 - numberOp k) : Matrix (Reg m) (Reg m) ℂ) y x =
      if y = x then (if x j then 0 else 1) * (if x k then 0 else 1) else 0 := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single x]
  · rw [one_sub_numberOp_apply (i := j) (y := y) (x := x),
      one_sub_numberOp_apply (i := k) (y := x) (x := x), if_pos rfl]
    by_cases h : y = x <;> simp [h]
  · intro b _ hb
    rw [one_sub_numberOp_apply (i := k) (y := b) (x := x), if_neg hb, mul_zero]
  · intro h
    simp at h

/-- Left multiplication by a diagonal matrix scales each matrix entry by the corresponding row
value. -/
theorem diagonal_mul_apply {m : ℕ} (d : Reg m → ℂ) (M : Matrix (Reg m) (Reg m) ℂ)
    (y x : Reg m) :
    (Matrix.diagonal d * M) y x = d y * M y x := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single y]
  · rw [Matrix.diagonal, Matrix.of_apply, if_pos rfl]
  · intro b _ hb
    rw [Matrix.diagonal, Matrix.of_apply, if_neg (Ne.symm hb), zero_mul]
  · intro h
    simp at h

/-- Right multiplication by a diagonal matrix scales each matrix entry by the corresponding
column value. -/
theorem mul_diagonal_apply {m : ℕ} (M : Matrix (Reg m) (Reg m) ℂ) (d : Reg m → ℂ)
    (y x : Reg m) :
    (M * Matrix.diagonal d) y x = M y x * d x := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single x]
  · rw [Matrix.diagonal, Matrix.of_apply, if_pos rfl]
  · intro b _ hb
    rw [Matrix.diagonal, Matrix.of_apply, if_neg hb, mul_zero]
  · intro h
    simp at h

/-- The computational basis vector concentrated at register configuration `x`. -/
def ket {m : ℕ} (x : Reg m) : Reg m → ℂ :=
  Qatlib.Foundations.PureStateMath.Ket x

/-- A basis vector evaluates to one at its label and zero elsewhere. -/
theorem ket_apply {m : ℕ} (x y : Reg m) : ket x y = if y = x then 1 else 0 := rfl

/-- Multiplying a matrix by the basis vector at `x` selects its column at `x`. -/
theorem mulVec_ket_apply {m : ℕ} (M : Matrix (Reg m) (Reg m) ℂ) (x y : Reg m) :
    (M *ᵥ ket x) y = M y x := by
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single x]
  · rw [ket_apply, if_pos rfl, mul_one]
  · intro b _ hb
    rw [ket_apply, if_neg hb, mul_zero]
  · intro h
    simp at h

/-- Annihilation clears an occupied bit with the Jordan-Wigner sign and gives zero on an
unoccupied bit. -/
theorem annihilation_mulVec_ket {m : ℕ} (i : Fin m) (x : Reg m) :
    annihilation i *ᵥ ket x =
      (if x i then jwSign i x • ket (Function.update x i false) else 0) := by
  funext y
  rw [mulVec_ket_apply, annihilation, Matrix.of_apply]
  simp only [ite_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, ket_apply]
  by_cases hx : x i
  · by_cases hy : y = Function.update x i false
    · rw [if_pos ⟨hx, hy⟩, if_pos hx, if_pos hy, mul_one]
    · rw [if_neg (by simp [hy]), if_pos hx, if_neg hy, mul_zero]
  · rw [if_neg (by simp [hx]), if_neg hx]

/-- Creation sets an unoccupied bit with the Jordan-Wigner sign of the resulting register and
gives zero on an occupied bit. -/
theorem creation_mulVec_ket {m : ℕ} (i : Fin m) (x : Reg m) :
    creation i *ᵥ ket x =
      (if x i then 0 else
        jwSign i (Function.update x i true) • ket (Function.update x i true)) := by
  funext y
  rw [mulVec_ket_apply, creation, Matrix.of_apply]
  simp only [ite_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, ket_apply]
  by_cases hx : x i
  · rw [if_neg (by simp [hx]), if_pos hx]
  · by_cases hy : y = Function.update x i true
    · rw [if_pos ⟨hx, hy⟩, if_neg hx, if_pos hy, mul_one, hy]
    · rw [if_neg (by simp [hy]), if_neg hx, if_neg hy, mul_zero]

/-- A basis vector is an eigenvector of the number operator with eigenvalue given by its
occupation at the selected mode. -/
theorem numberOp_mulVec_ket {m : ℕ} (i : Fin m) (x : Reg m) :
    numberOp i *ᵥ ket x = (if x i then (1 : ℂ) else 0) • ket x := by
  funext y
  rw [mulVec_ket_apply, numberOp, Matrix.of_apply]
  simp only [Pi.smul_apply, smul_eq_mul, ket_apply]
  by_cases hx : x i
  · by_cases hy : y = x
    · simp [hx, hy]
    · have hxy : ¬ x = y := fun h => hy h.symm
      simp [hx, hy, hxy]
  · simp [hx]

/-- The vacancy projection preserves a basis vector exactly when its selected bit is unoccupied,
and otherwise gives zero. -/
theorem one_sub_numberOp_mulVec_ket {m : ℕ} (i : Fin m) (x : Reg m) :
    (1 - numberOp i : Matrix (Reg m) (Reg m) ℂ) *ᵥ ket x =
      (if x i then 0 else 1) • ket x := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, numberOp_mulVec_ket]
  by_cases hx : x i <;> simp [hx]

/-- The two-mode vacuum projection scales a basis vector by the product of its two vacancy
indicators. -/
theorem vacuumProj_mulVec_ket {m : ℕ} (j k : Fin m) (x : Reg m) :
    ((1 - numberOp j) * (1 - numberOp k) : Matrix (Reg m) (Reg m) ℂ) *ᵥ ket x =
      ((if x j then 0 else 1) * (if x k then 0 else 1)) • ket x := by
  rw [← Matrix.mulVec_mulVec, one_sub_numberOp_mulVec_ket, Matrix.mulVec_smul,
    one_sub_numberOp_mulVec_ket, smul_smul]
  by_cases hj : x j <;> by_cases hk : x k <;> simp [hj, hk]

/-- The product of occupation signs at positions strictly between `j` and `k`. -/
def jwSignProd {m : ℕ} (j k : Fin m) (x : Reg m) : ℂ :=
  ∏ s ∈ (Finset.univ.filter (fun s : Fin m => j < s ∧ s < k)),
    (-1 : ℂ) ^ (bitNat (x s))

/-- The intermediate Jordan-Wigner sign product is the product of powers of negative one
determined by the intermediate occupations. -/
theorem jwSignProd_eq {m : ℕ} (j k : Fin m) (x : Reg m) :
    jwSignProd j k x =
      ∏ s ∈ (Finset.univ.filter (fun s : Fin m => j < s ∧ s < k)),
        (-1 : ℂ) ^ (if x s then 1 else 0) := rfl

/-- Raising a monoid element to the natural-number value of false gives one. -/
theorem pow_bitNat_false {α : Type*} [Monoid α] (a : α) : a ^ (bitNat false) = 1 := by
  simp [bitNat]

/-- Raising a monoid element to the natural-number value of true gives that element. -/
theorem pow_bitNat_true {α : Type*} [Monoid α] (a : α) : a ^ (bitNat true) = a := by
  simp [bitNat]

/-- A qubit matrix unit replaces matching selected occupations by its output label and gives
zero on nonmatching inputs. -/
theorem qubitUnit2_mulVec_ket {m : ℕ} (p q : Reg 2) (j k : Fin m) (x : Reg m) :
    qubitUnit2 p q j k *ᵥ ket x =
      (if x j = q 0 ∧ x k = q 1 then
        ket (Function.update (Function.update x j (p 0)) k (p 1)) else 0) := by
  funext y
  rw [mulVec_ket_apply, qubitUnit2, Matrix.of_apply]
  simp only [ite_apply, ket_apply]
  by_cases h1 : x j = q 0 <;> by_cases h2 : x k = q 1
  · by_cases hy : y = Function.update (Function.update x j (p 0)) k (p 1)
    · simp [h1, h2, hy]
    · simp [h1, h2, hy]
  all_goals simp [h1, h2]

/-- Fermionic and qubit matrix units have the same action on every basis vector of the two-mode
register. -/
theorem lfmUnit2_two_mulVec_ket (p q : Reg 2) (x : Reg 2) :
    lfmUnit2 p q (0 : Fin 2) (1 : Fin 2) *ᵥ ket x =
      qubitUnit2 p q (0 : Fin 2) (1 : Fin 2) *ᵥ ket x := by
  rw [qubitUnit2_mulVec_ket]
  rw [lfmUnit2]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec]
  rcases reg2_cases x with rfl | rfl | rfl | rfl <;>
  cases hp0 : p 0 <;> cases hp1 : p 1 <;> cases hq0 : q 0 <;> cases hq1 : q 1
  all_goals
    funext t
    fin_cases t <;>
    simp +decide [reg2Of, bitNat, Matrix.one_mulVec,
      annihilation_mulVec_ket, creation_mulVec_ket, vacuumProj_mulVec_ket,
      Matrix.mulVec_zero, Matrix.mulVec_neg, Function.update_apply,
      jwSign, ket_apply, smul_eq_mul]

/-- Fermionic and qubit matrix units coincide at the two positions of the two-mode register. -/
theorem lfmUnit2_two_eq_qubitUnit2 (p q : Reg 2) :
    lfmUnit2 p q (0 : Fin 2) (1 : Fin 2) =
      qubitUnit2 p q (0 : Fin 2) (1 : Fin 2) := by
  ext y x
  rw [← mulVec_ket_apply (M := lfmUnit2 p q (0 : Fin 2) (1 : Fin 2)),
    ← mulVec_ket_apply (M := qubitUnit2 p q (0 : Fin 2) (1 : Fin 2))]
  exact congrFun (lfmUnit2_two_mulVec_ket p q x) y

/-- Selecting zero at index zero and one otherwise is the identity function on `Fin 2`. -/
theorem fin2_ite (t : Fin 2) : (if t = 0 then (0 : Fin 2) else 1) = t := by
  fin_cases t <;> simp

/-- Placing a two-mode matrix at both positions of the two-mode register gives the original
matrix. -/
theorem qubitApply2_two_eq (X : Matrix (Reg 2) (Reg 2) ℂ) :
    qubitApply2 X (0 : Fin 2) (1 : Fin 2) = X := by
  ext y x
  rw [qubitApply2, Matrix.of_apply]
  have hy : (fun t : Fin 2 => y (if t = 0 then (0 : Fin 2) else 1)) = y := by
    funext t; rw [fin2_ite]
  have hx : (fun t : Fin 2 => x (if t = 0 then (0 : Fin 2) else 1)) = x := by
    funext t; rw [fin2_ite]
  rw [hy, hx]
  have hfilter : (Finset.univ.filter (fun s : Fin 2 => s ≠ 0 ∧ s ≠ 1)) = ∅ := by
    ext s; fin_cases s <;> simp
  rw [hfilter, Finset.prod_empty, mul_one]

/-- A two-mode matrix is the sum of its matrix units weighted by its entries. -/
theorem sum_qubitUnit2_eq (X : Matrix (Reg 2) (Reg 2) ℂ) :
    (∑ p : Reg 2, ∑ q : Reg 2, X p q • qubitUnit2 p q (0 : Fin 2) (1 : Fin 2)) = X := by
  ext y x
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  have hinner : ∀ p : Reg 2,
      (∑ q : Reg 2, X p q * qubitUnit2 p q (0 : Fin 2) (1 : Fin 2) y x) =
        X p x * qubitUnit2 p x (0 : Fin 2) (1 : Fin 2) y x := by
    intro p
    rw [Finset.sum_eq_single x]
    · intro q _ hq
      have hq' : ¬ (x 0 = q 0 ∧ x 1 = q 1) := by
        rintro ⟨e0, e1⟩
        apply hq
        funext t; fin_cases t <;> simp [e0, e1]
      simp only [qubitUnit2, Matrix.of_apply]
      split_ifs with h
      · exact absurd ⟨h.1, h.2.1⟩ hq'
      · simp
    · intro h; simp at h
  simp_rw [hinner]
  rw [Finset.sum_eq_single y]
  · have hupd : Function.update (Function.update x 0 (y 0)) 1 (y 1) = y := by
      funext t; fin_cases t <;> simp
    have h1 : qubitUnit2 y x (0 : Fin 2) (1 : Fin 2) y x = 1 := by
      simp [qubitUnit2, Matrix.of_apply, hupd]
    rw [h1, mul_one]
  · intro p _ hp
    have hne : Function.update (Function.update x 0 (p 0)) 1 (p 1) ≠ y := by
      intro h
      apply hp
      funext t; fin_cases t
      · have := congrFun h 0; simpa [Function.update_apply] using! this
      · have := congrFun h 1; simpa [Function.update_apply] using! this
    have h0 : qubitUnit2 p x (0 : Fin 2) (1 : Fin 2) y x = 0 := by
      simp only [qubitUnit2, Matrix.of_apply]
      rw [if_neg (by rintro ⟨-, -, hy⟩; exact hne hy.symm)]
    rw [h0, mul_zero]
  · intro h; simp at h

/-- Fermionic and qubit placements of any matrix agree on the complete two-mode register.
[BravyiKitaev2002] -/
theorem lfmApply2_two_eq (X : Matrix (Reg 2) (Reg 2) ℂ) :
    lfmApply2 X (0 : Fin 2) (1 : Fin 2) = qubitApply2 X (0 : Fin 2) (1 : Fin 2) := by
  rw [qubitApply2_two_eq, lfmApply2]
  simp only [lfmUnit2_two_eq_qubitUnit2]
  exact sum_qubitUnit2_eq X

end Qatlib.Papers.FermionicComp00.MainResults.SwapDefect
