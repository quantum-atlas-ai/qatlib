/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FermionAlgebra.CarJordanWigner.Fermion

/-!
# Fermionic swap defects

`swapDefect` is the diagonal sign distinguishing fermionic and qubit swaps. The module proves
its involutivity, the two-mode swap factorization, and the action of the fermionic swap on
annihilation operators. It also introduces the placement `qubitApply2` and the intermediate-mode
sign chain `swapDefectChain`.

These constructions belong to the formalization of [BravyiKitaev2002].

## Main statements

* `source_swap_defect_factorization`: factors the fermionic swap into a qubit swap and a
  diagonal defect.
* `swapDefectChain_mul_self`: the defect chain squares to the identity.

## References

* [Bravyi and Kitaev, 2002][BravyiKitaev2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner

namespace Qatlib.Papers.FermionicComp00.MainResults.SwapDefect

/-- The diagonal sign that is negative exactly when both selected register bits are occupied. -/
def swapDefect {m : ℕ} (l r : Fin m) : Matrix (Reg m) (Reg m) ℂ :=
  Matrix.diagonal (fun x : Reg m => (-1 : ℂ) ^ (if x l ∧ x r then 1 else 0))

/-- Every swap-defect matrix squares to the identity. -/
theorem swapDefect_mul_self {m : ℕ} (l r : Fin m) :
    swapDefect l r * swapDefect l r = 1 := by
  rw [swapDefect, Matrix.diagonal_mul_diagonal]
  ext y x
  rw [Matrix.diagonal, Matrix.of_apply, Matrix.one_apply]
  by_cases h : y = x
  · subst h
    rw [if_pos rfl, if_pos rfl]
    exact neg_one_pow_mul_self _
  · rw [if_neg h, if_neg h]

/-- The two-mode fermionic swap matrix, expressed using number, creation, and annihilation
operators. -/
def fermionSwap2 : Matrix (Reg 2) (Reg 2) ℂ :=
  1 - numberOp (0 : Fin 2) - numberOp (1 : Fin 2)
    + creation (1 : Fin 2) * annihilation (0 : Fin 2)
    + creation (0 : Fin 2) * annihilation (1 : Fin 2)

/-- The permutation matrix interchanging the two qubit positions. -/
def qubitSwap2 : Matrix (Reg 2) (Reg 2) ℂ :=
  permMatrix (fun x : Reg 2 => fun t => x (Equiv.swap (0 : Fin 2) (1 : Fin 2) t))

/-- The two-bit register with first bit `a` and second bit `b`. -/
def reg2Of (a b : Bool) : Reg 2 := fun t => if t = 0 then a else b

/-- The finite set of two-bit registers consists of the four Boolean assignments. -/
theorem univ_reg2 : (Finset.univ : Finset (Reg 2)) =
    {reg2Of false false, reg2Of false true, reg2Of true false, reg2Of true true} := by
  decide

/-- Every two-bit register is one of the four Boolean assignments. -/
theorem reg2_cases (y : Reg 2) :
    y = reg2Of false false ∨ y = reg2Of false true ∨
    y = reg2Of true false ∨ y = reg2Of true true := by
  by_cases h0 : y 0 = false <;> by_cases h1 : y 1 = false
  · left; funext t; fin_cases t <;> simp [reg2Of, h0, h1]
  · right; left; funext t; fin_cases t <;> simp [reg2Of, h0, h1]
  · right; right; left; funext t; fin_cases t <;> simp [reg2Of, h0, h1]
  · right; right; right; funext t; fin_cases t <;> simp [reg2Of, h0, h1]

/-- Conjugating either annihilation operator by the two-mode fermionic swap gives the other
annihilation operator. [BravyiKitaev2002] -/
theorem source_fermion_swap_annihilation :
    fermionSwap2 * annihilation (0 : Fin 2) * fermionSwap2 = annihilation (1 : Fin 2) ∧
    fermionSwap2 * annihilation (1 : Fin 2) * fermionSwap2 = annihilation (0 : Fin 2) := by
  constructor
  · ext y x
    rcases reg2_cases y with rfl | rfl | rfl | rfl <;>
      rcases reg2_cases x with rfl | rfl | rfl | rfl <;>
      simp +decide [fermionSwap2, annihilation, creation, numberOp, Matrix.mul_apply,
        Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, univ_reg2, jwSign]
  · ext y x
    rcases reg2_cases y with rfl | rfl | rfl | rfl <;>
      rcases reg2_cases x with rfl | rfl | rfl | rfl <;>
      simp +decide [fermionSwap2, annihilation, creation, numberOp, Matrix.mul_apply,
        Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, univ_reg2, jwSign]

/-- The two-mode fermionic swap is the product of the qubit swap and the diagonal swap defect.
[BravyiKitaev2002] -/
theorem source_swap_defect_factorization :
    fermionSwap2 = qubitSwap2 * swapDefect (0 : Fin 2) (1 : Fin 2) := by
  ext y x
  rcases reg2_cases y with rfl | rfl | rfl | rfl <;>
    rcases reg2_cases x with rfl | rfl | rfl | rfl <;>
    simp +decide [fermionSwap2, qubitSwap2, swapDefect, permMatrix, numberOp, annihilation,
      creation, Matrix.mul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.of_apply,
      univ_reg2, jwSign, Matrix.diagonal, Equiv.swap_apply_def]

/-- The matrix applying `X` to positions `j` and `k` while leaving all other register bits
unchanged. -/
def qubitApply2 {m : ℕ} (X : Matrix (Reg 2) (Reg 2) ℂ) (j k : Fin m) :
    Matrix (Reg m) (Reg m) ℂ :=
  Matrix.of fun y x =>
    X (fun t => y (if t = 0 then j else k)) (fun t => x (if t = 0 then j else k)) *
      ∏ s ∈ (Finset.univ.filter (fun s : Fin m => s ≠ j ∧ s ≠ k)),
        (if y s = x s then (1 : ℂ) else 0)

/-- The diagonal product of swap-defect signs between each position strictly between `j` and `k`
and the endpoint `k`. -/
def swapDefectChain {m : ℕ} (j k : Fin m) : Matrix (Reg m) (Reg m) ℂ :=
  Matrix.diagonal (fun x : Reg m =>
    ∏ s ∈ (Finset.univ.filter (fun s : Fin m => j < s ∧ s < k)),
      ((-1 : ℂ) ^ (if x s ∧ x k then 1 else 0)))

/-- The swap-defect chain squares to the identity. -/
theorem swapDefectChain_mul_self {m : ℕ} (j k : Fin m) :
    swapDefectChain j k * swapDefectChain j k = 1 := by
  rw [swapDefectChain, Matrix.diagonal_mul_diagonal]
  ext y x
  rw [Matrix.diagonal, Matrix.of_apply, Matrix.one_apply]
  by_cases h : y = x
  · subst h
    rw [if_pos rfl, if_pos rfl]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one (fun s _ => ?_)
    exact neg_one_pow_mul_self _
  · rw [if_neg h, if_neg h]

end Qatlib.Papers.FermionicComp00.MainResults.SwapDefect
