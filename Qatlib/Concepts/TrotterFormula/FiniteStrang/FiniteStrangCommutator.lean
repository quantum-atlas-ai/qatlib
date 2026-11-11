/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.LieStrang.CommutatorProductFormula
import Mathlib.Data.List.FinRange

/-!
# Finite Strang formulas with nested commutator bounds

The word `finiteStrangWord` implements the symmetric product formula for a finite Hamiltonian
family. The coefficient `finiteStrangConstant` sums two kinds of nested commutator norms with
weights `1/12` and `1/24`; `finite_strang_tight_nested_commutator` bounds the single-step error
by this coefficient times `|t| ^ 3`. For background, see [ChildsEtAl2021Trotter].

## Main statements

* `finiteStrangConstant`: explicit nested commutator coefficient.
* `finite_strang_tight_nested_commutator`: cubic single-step Strang error bound.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.TrotterFormula.LieStrang

namespace Qatlib.Concepts.TrotterFormula.FiniteStrang
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The sum of Hamiltonian terms whose indices are strictly greater than `j`. -/
def finiteStrangTail {D m : ℕ} (H : Fin m → Operator D) (j : Fin m) : Operator D :=
  ∑ i : Fin m, if j < i then H i else 0

/-- The Strang error coefficient formed from tail-tail-term and term-term-tail commutator norms
with weights `1/12` and `1/24`. -/
def finiteStrangConstant {D m : ℕ} (H : Fin m → Operator D) : ℝ :=
  (∑ j : Fin m, ‖pfComm (finiteStrangTail H j) (pfComm (finiteStrangTail H j) (H j))‖)/12 +
  (∑ j : Fin m, ‖pfComm (H j) (pfComm (H j) (finiteStrangTail H j))‖)/24

/-- The tagged gate word consisting of `r` repetitions of the forward and reverse Hamiltonian
half-step lists. -/
def finiteStrangWord {D m : ℕ} (H : Fin m → Operator D) (t : ℝ) (r : ℕ) :
    List (Operator D × ℕ) :=
  let ids := List.finRange m
  let step := (ids ++ ids.reverse).map (fun j => (HamiltonianEvolution (H j) (t/(2*r)),j.val))
  (List.replicate r step).flatten

/-- Interpreting a tagged word equals folding its matrix components by left multiplication,
starting at the identity. -/
private theorem fs_interpret_first {D : ℕ} (xs : List (Operator D × ℕ)) :
    pfInterpret xs = (xs.map Prod.fst).foldl (fun U V => V*U) 1 := by
  unfold pfInterpret
  exact (List.foldl_map (f := Prod.fst) (g := fun U V => V*U)).symm

/-- The interpreted gate word formed by appending the reverse of a matrix list to itself, with
all tags set to zero. -/
private def fsPal {D : ℕ} (xs : List (Operator D)) : Operator D :=
  pfInterpret ((xs ++ xs.reverse).map (fun U => (U, 0)))

/-- Prepending a gate to a word multiplies the interpreted tail on the right by that gate. -/
private theorem fs_interpret_cons {D : ℕ} (x : Operator D × ℕ) (xs) :
    pfInterpret (x :: xs) = pfInterpret xs * x.1 := by
  change xs.foldl (fun V y => y.1*V) (x.1*1) = _
  rw [pfInterpret_start, mul_one]

/-- The palindrome associated with `A :: xs` equals `A * fsPal xs * A`. -/
private theorem fsPal_cons {D : ℕ} (A : Operator D) (xs) :
    fsPal (A :: xs) = A * fsPal xs * A := by
  simp only [fsPal, List.reverse_cons, List.cons_append, List.map_cons,
    List.map_append, List.map_nil]
  rw [← List.append_assoc, fs_interpret_cons, pfInterpret_append]
  have hsingle : pfInterpret [(A, 0)] = A := by simp [pfInterpret]
  rw [hsingle]

/-- A single Strang segment is the palindrome of the Hamiltonian half-step evolutions in index
order. -/
private theorem finiteStrangWord_one {D m : ℕ} (H : Fin m → Operator D) (t : ℝ) :
    pfInterpret (finiteStrangWord H t 1) =
      fsPal (List.ofFn (fun j => HamiltonianEvolution (H j) (t/2))) := by
  simp only [finiteStrangWord, Nat.cast_one, mul_one, List.replicate_one,
    List.flatten_cons, List.flatten_nil, List.append_nil, fsPal, List.map_append,
    List.map_reverse, List.ofFn_eq_map, List.map_map, fs_interpret_first]
  rfl

/-- The tail after index zero is the sum of the Hamiltonian terms indexed by successors. -/
private theorem fs_tail_zero {D m : ℕ} (H : Fin (m+1) → Operator D) :
    finiteStrangTail H 0 = ∑ j : Fin m, H j.succ := by
  simp [finiteStrangTail, Fin.sum_univ_succ]

/-- A tail at a successor index is the corresponding tail of the family with its first term
removed. -/
private theorem fs_tail_succ {D m : ℕ} (H : Fin (m+1) → Operator D) (j : Fin m) :
    finiteStrangTail H j.succ = finiteStrangTail (fun i : Fin m => H i.succ) j := by
  simp [finiteStrangTail, Fin.sum_univ_succ]

/-- Removing the first Hamiltonian term splits the Strang coefficient into the remaining
coefficient and the two nested commutator contributions of that first term. -/
private theorem fs_constant_succ {D m : ℕ} (H : Fin (m+1) → Operator D) :
    finiteStrangConstant H = finiteStrangConstant (fun j : Fin m => H j.succ) +
      ‖pfComm (∑ j : Fin m, H j.succ) (pfComm (∑ j : Fin m, H j.succ) (H 0))‖/12 +
      ‖pfComm (H 0) (pfComm (H 0) (∑ j : Fin m, H j.succ))‖/24 := by
  simp only [finiteStrangConstant, Fin.sum_univ_succ, fs_tail_zero, fs_tail_succ]
  ring

/-- If `‖A‖ ≤ 1`, then sandwiching `X` as `A * X * A` has norm at most `‖X‖`. -/
private theorem fs_sandwich_norm {D : ℕ} (A X : Operator D) (hA : ‖A‖ ≤ 1) :
    ‖A*X*A‖ ≤ ‖X‖ := by
  calc
    _ ≤ ‖A‖*‖X‖*‖A‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1*‖X‖*1 := by gcongr
    _ = _ := by ring

/-- For Hermitian terms, the palindromic half-step product differs from the exact sum evolution
by at most `|t| ^ 3 * finiteStrangConstant H`. -/
private theorem fs_step_error (D m : ℕ) (H : Fin m → Operator D) (t : ℝ)
    (hH : ∀ j, (H j).IsHermitian) :
    ‖fsPal (List.ofFn (fun j => HamiltonianEvolution (H j) (t/2))) -
      HamiltonianEvolution (∑ j, H j) t‖ ≤ |t|^3*finiteStrangConstant H := by
  induction m with
  | zero => simp [fsPal, pfInterpret, HamiltonianEvolution, finiteStrangConstant]
  | succ m ih =>
    let tail : Fin m → Operator D := fun j => H j.succ
    let B : Operator D := ∑ j, tail j
    let E := HamiltonianEvolution (H 0) (t/2)
    let S := fsPal (List.ofFn (fun j => HamiltonianEvolution (tail j) (t/2)))
    have hB : B.IsHermitian := by
      change (∑ j : Fin m, H j.succ)ᴴ = _
      rw [Matrix.conjTranspose_sum]
      exact Finset.sum_congr rfl fun j _ => (hH j.succ).eq
    have hi := ih tail (fun j => hH j.succ)
    have hs := product_formula_strang_nested_commutator D (H 0) B t (hH 0) hB
    have he : fsPal (List.ofFn (fun j => HamiltonianEvolution (H j) (t/2))) -
        HamiltonianEvolution (∑ j, H j) t =
        E*(S-HamiltonianEvolution B t)*E +
          (pfStrang (H 0) B t - HamiltonianEvolution (H 0+B) t) := by
      rw [List.ofFn_succ, fsPal_cons, Fin.sum_univ_succ]
      dsimp only [E, S, B, tail, pfStrang]
      noncomm_ring
    rw [he]
    calc
      _ ≤ ‖E*(S-HamiltonianEvolution B t)*E‖ +
          ‖pfStrang (H 0) B t-HamiltonianEvolution (H 0+B) t‖ := norm_add_le _ _
      _ ≤ ‖S-HamiltonianEvolution B t‖ +
          ‖pfStrang (H 0) B t-HamiltonianEvolution (H 0+B) t‖ := by
        have hn : ‖E‖ ≤ 1 :=
          l2_norm_unitary_le_one (hamiltonianEvolution_unitary (hH 0) (t/2))
        exact add_le_add (fs_sandwich_norm (D := D) E (S-HamiltonianEvolution B t) hn) le_rfl
      _ ≤ |t|^3*finiteStrangConstant tail +
          (|t|^3/12*‖pfComm B (pfComm B (H 0))‖ +
            |t|^3/24*‖pfComm (H 0) (pfComm (H 0) B)‖) := add_le_add hi hs
      _ = _ := by
        have hC : finiteStrangConstant H = finiteStrangConstant tail +
            ‖pfComm B (pfComm B (H 0))‖/12 +
            ‖pfComm (H 0) (pfComm (H 0) B)‖/24 := fs_constant_succ H
        rw [hC]
        ring

/-- For a finite Hermitian family, the single-step Strang word has error at most `|t| ^ 3 *
finiteStrangConstant H` [Childs et al., Proposition 16][ChildsEtAl2021Trotter]. -/
theorem finite_strang_tight_nested_commutator :
    ∀ (D m : ℕ) (H : Fin m → Operator D) (t : ℝ),
      (∀ j, (H j).IsHermitian) →
      ‖pfInterpret (finiteStrangWord H t 1) - HamiltonianEvolution (∑ j, H j) t‖ ≤
        |t|^3*finiteStrangConstant H := by
  intro D m H t hH
  rw [finiteStrangWord_one]
  exact fs_step_error D m H t hH

end Qatlib.Concepts.TrotterFormula.FiniteStrang
