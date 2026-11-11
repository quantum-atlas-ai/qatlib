/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TensorRegisters.RegisterModel.QmaCompletenessLocalSupport
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Qatlib.Foundations.PureStateMath.Tensor

/-!
# Local gates on binary registers

`placeLocalGate` extends a matrix on a chosen set of qubits by the identity on the remaining
qubits and relabels it using binary register indices. The set `gateSet g n` allows arbitrary
unitary gates with support of cardinality at most `g`, as in the local circuit framework of
[Knill1995].

The module proves the entrywise support formula, preservation of unitarity and identity,
monotonicity in the support bound, and diagonality of zero-width gate products.

## Main statements

* `placeLocalGate_apply`: describe local gate entries using agreement outside the support.
* `gateSet_unitary`: every allowed local gate is unitary.
* `zero_width_product_offdiagonal`: products of zero-width gates are diagonal.

## References

* [Knill, 1995][Knill1995]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Kronecker
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.LocalCircuits.LocalGateCosts

/-- Splitting a register of length `n + 1` gives its first `n` bits and its last bit. -/
theorem register_succ_coordinates (n : ℕ) (x : Reg (n+1)) :
    regSuccEquiv n x = (Fin.init x, x (Fin.last n)) := by
  rfl

/-- The binary value of a register is twice the value of its initial segment plus the value of
its last bit. -/
theorem bitVec_value_succ (n : ℕ) (x : Reg (n+1)) :
    (bitVecEquiv (n+1) x).val =
      (boolEquivFin2 (x (Fin.last n))).val + 2 * (bitVecEquiv n (Fin.init x)).val := by
  have castVal : ∀ (e : 2 ^ n * 2 = 2 ^ (n+1)) (y : Fin (2 ^ n * 2)),
      ((Equiv.cast (congrArg Fin e)) y).val = y.val := by
    intro e y
    cases e
    rfl
  change ((Equiv.cast (congrArg Fin (Nat.pow_succ 2 n).symm))
    (finProdFinEquiv ((Equiv.prodCongr (bitVecEquiv n) boolEquivFin2)
      (regSuccEquiv n x)))).val = _
  rw [castVal (Nat.pow_succ 2 n).symm, register_succ_coordinates]
  rfl

/-- Extend a gate on the qubits in `S` by identity on the complement and express it in
binary-encoded coordinates. -/
def placeLocalGate {n : ℕ} (S : Finset (Fin n))
    (V : Matrix (Reg S.card) (Reg S.card) ℂ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  relabelGate (bitVecEquiv n) (partitionLift (split S) V)

/-- Placing a unitary gate on a subset of qubits preserves unitarity. -/
theorem placeLocalGate_unitary {n : ℕ} (S : Finset (Fin n))
    (V : Matrix (Reg S.card) (Reg S.card) ℂ)
    (hV : V ∈ Matrix.unitaryGroup (Reg S.card) ℂ) :
    placeLocalGate S V ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  have h : partitionLift (split S) V ∈ Matrix.unitaryGroup (Reg n) ℂ := by
    exact (relabelGate_mem_unitaryGroup (split S).symm _).mpr
      (tensorGate_unitary hV (Submonoid.one_mem _))
  exact (relabelGate_mem_unitaryGroup _ _).mpr h

/-- A placed gate has the local matrix entry when the registers agree outside `S`, and zero
otherwise. -/
theorem placeLocalGate_apply {n : ℕ} (S : Finset (Fin n))
    (V : Matrix (Reg S.card) (Reg S.card) ℂ) (x y : Reg n) :
    placeLocalGate S V (bitVecEquiv n x) (bitVecEquiv n y) =
      if outside S x = outside S y then V (mask S x) (mask S y) else 0 := by
  simpa only [placeLocalGate, relabelGate, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply] using partitionLift_apply S V x y

/-- Placing the identity gate on any support gives the identity on the full register. -/
theorem placeLocalGate_one {n : ℕ} (S : Finset (Fin n)) :
    placeLocalGate S 1 = 1 := by
  simp only [placeLocalGate, partitionLift, Matrix.one_kronecker_one]
  change relabelGate (bitVecEquiv n) (relabelGate (split S).symm 1) = 1
  rw [CircuitRelabel.relabelGate_one, CircuitRelabel.relabelGate_one]

/-- The unitary matrices obtained by placing a gate on at most `g` of the `n` qubits. -/
def gateSet (g n : ℕ) : Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  {U | ∃ S : Finset (Fin n), S.card ≤ g ∧
    ∃ V : Matrix (Reg S.card) (Reg S.card) ℂ,
      V ∈ Matrix.unitaryGroup (Reg S.card) ℂ ∧ U = placeLocalGate S V}

/-- Every member of `gateSet g n` is a unitary matrix. -/
theorem gateSet_unitary {g n : ℕ} {U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ}
    (h : U ∈ gateSet g n) : U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ := by
  obtain ⟨S, _, V, hV, rfl⟩ := h
  exact placeLocalGate_unitary S V hV

/-- Increasing the allowed support width enlarges the local gate set. -/
theorem gateSet_mono {g h n : ℕ} (hgh : g ≤ h) : gateSet g n ⊆ gateSet h n := by
  rintro U ⟨S, hS, V, hV, he⟩
  exact ⟨S, hS.trans hgh, V, hV, he⟩

/-- The identity matrix belongs to the local gate set for every support bound and register size. -/
theorem one_mem_gateSet (g n : ℕ) :
    (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) ∈ gateSet g n := by
  refine ⟨∅, by simp, 1, Submonoid.one_mem _, ?_⟩
  exact (placeLocalGate_one ∅).symm

/-- Every off-diagonal entry of a zero-width local gate vanishes. -/
theorem zero_width_offdiagonal {n : ℕ}
    {U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ} (hU : U ∈ gateSet 0 n)
    (i j : Fin (2 ^ n)) (hij : i ≠ j) : U i j = 0 := by
  obtain ⟨S, hS, V, _, he⟩ := hU
  have hs : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hS)
  subst S
  rw [he]
  change partitionLift (split (∅ : Finset (Fin n))) V
    ((bitVecEquiv n).symm i) ((bitVecEquiv n).symm j) = 0
  rw [partitionLift_apply]
  apply if_neg
  intro h
  apply hij
  apply (bitVecEquiv n).symm.injective
  funext a
  exact congrFun h ⟨a, by simp⟩

/-- Every off-diagonal entry of a product of zero-width local gates vanishes. -/
theorem zero_width_product_offdiagonal {n : ℕ}
    (word : List (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ))
    (hword : ∀ G ∈ word, G ∈ gateSet 0 n)
    (i j : Fin (2 ^ n)) (hij : i ≠ j) : word.prod i j = 0 := by
  induction word with
  | nil => simp [hij]
  | cons G word ih =>
    simp only [List.prod_cons, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : a = i
    · subst a
      rw [ih (fun H hH => hword H (by simp [hH]))]
      exact mul_zero _
    · rw [zero_width_offdiagonal (hword G (by simp)) i a (Ne.symm ha), zero_mul]

end Qatlib.Concepts.LocalCircuits.LocalGateCosts
