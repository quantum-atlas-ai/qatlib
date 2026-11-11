/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.LieStrang.TrotterFirstOrderTailSumStat

/-!
# First-order Trotter bounds using tail sums

This module proves a first-order finite-family error bound that retains each commutator with the
sum of later terms before taking its norm. It formalizes the tail-sum form of the estimate in
[ChildsEtAl2021Trotter].

The proof establishes a one-segment bound and then accumulates the error through unitary powers
to obtain the positive-segment statement `trotterFirstOrderTailSum`.

## Main statements

* `tailSegment_error`: the one-segment tail-commutator bound.
* `trotterFirstOrderTailSum`: the segmented first-order tail-sum specification.

## References

* [Childs et al., Proposition 15][ChildsEtAl2021Trotter]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.TrotterFormula.FiniteStrang

namespace Qatlib.Concepts.TrotterFormula.LieStrang
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The single family segment interpreted from the ordered evolutions with dummy labels. -/
private def tailSegment {D m : ℕ} (H : Fin m → Operator D) (t : ℝ) : Operator D :=
  pfInterpret (List.ofFn (fun j => (HamiltonianEvolution (H j) t, 0)))

/-- Interpreting a word with head `x` equals the tail interpretation multiplied on the right by
`x.1`. -/
private theorem tail_interpret_cons {D : ℕ} (x : Operator D × ℕ) (xs) :
    pfInterpret (x :: xs) = pfInterpret xs*x.1 := by
  change xs.foldl (fun V y => y.1*V) (x.1*1) = _
  rw [pfInterpret_start, mul_one]

/-- A nonempty family segment is the segment for later terms multiplied on the right by the
first term's evolution. -/
private theorem tailSegment_cons {D m : ℕ} (H : Fin (m+1) → Operator D) (t : ℝ) :
    tailSegment H t = tailSegment (fun i : Fin m => H i.succ) t*HamiltonianEvolution (H 0) t := by
  rw [tailSegment, List.ofFn_succ, tail_interpret_cons]
  rfl

/-- The tail sum after index zero is the sum of the successor-indexed family terms. -/
private theorem tail_zero {D m : ℕ} (H : Fin (m+1) → Operator D) :
    finiteStrangTail H 0 = ∑ j : Fin m, H j.succ := by
  simp [finiteStrangTail, Fin.sum_univ_succ]

/-- A tail sum at a successor index equals the corresponding tail sum in the family with its
first term removed. -/
private theorem tail_succ {D m : ℕ} (H : Fin (m+1) → Operator D) (j : Fin m) :
    finiteStrangTail H j.succ = finiteStrangTail (fun i : Fin m => H i.succ) j := by
  simp [finiteStrangTail, Fin.sum_univ_succ]

/-- For Hermitian family terms, the one-segment error is at most `t² / 2` times the sum of norms
of commutators between each term and its later-term sum. -/
private theorem tailSegment_error (D m : ℕ) (H : Fin m → Operator D) (t : ℝ)
    (hH : ∀ j, (H j).IsHermitian) :
    ‖tailSegment H t-HamiltonianEvolution (∑ j, H j) t‖ ≤
      t^2/2*∑ j : Fin m, ‖pfComm (finiteStrangTail H j) (H j)‖ := by
  induction m with
  | zero => simp [tailSegment, pfInterpret, HamiltonianEvolution]
  | succ m ih =>
    let tail : Fin m → Operator D := fun j => H j.succ
    let B := ∑ j, tail j
    have hB : B.IsHermitian := by
      change (∑ j : Fin m, H j.succ)ᴴ = _
      rw [Matrix.conjTranspose_sum]
      exact Finset.sum_congr rfl (fun j _ => (hH j.succ).eq)
    have hi := ih tail (fun j => hH j.succ)
    have hLie := product_formula_lie_two_term D (H 0) B t (hH 0) hB
    have he : tailSegment H t-HamiltonianEvolution (∑ j, H j) t =
        (tailSegment tail t-HamiltonianEvolution B t)*HamiltonianEvolution (H 0) t+
        (pfLie (H 0) B t-HamiltonianEvolution (H 0+B) t) := by
      rw [tailSegment_cons, Fin.sum_univ_succ]
      dsimp only [pfLie, B, tail]
      noncomm_ring
    rw [he]
    calc
      _ ≤ ‖(tailSegment tail t-HamiltonianEvolution B t)*HamiltonianEvolution (H 0) t‖+
          ‖pfLie (H 0) B t-HamiltonianEvolution (H 0+B) t‖ := norm_add_le _ _
      _ ≤ ‖tailSegment tail t-HamiltonianEvolution B t‖+
          ‖pfLie (H 0) B t-HamiltonianEvolution (H 0+B) t‖ := by
        apply add_le_add _ le_rfl
        exact (norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left
          (l2_norm_unitary_le_one (hamiltonianEvolution_unitary (hH 0) t))
          (norm_nonneg _)).trans_eq (mul_one _))
      _ ≤ t^2/2*(∑ j : Fin m, ‖pfComm (finiteStrangTail tail j) (tail j)‖)+
          t^2/2*‖pfComm B (H 0)‖ := add_le_add hi hLie
      _ = _ := by
        rw [Fin.sum_univ_succ, tail_zero]
        simp only [tail_succ]
        dsimp only [B, tail]
        ring

/-- Word interpretation equals the left-multiplication fold of its matrix entries. -/
private theorem tail_interpret_fst {D : ℕ} (xs : List (Operator D × ℕ)) :
    pfInterpret xs = (xs.map Prod.fst).foldl (fun U V => V*U) 1 := by
  unfold pfInterpret
  exact (List.foldl_map (f := Prod.fst) (g := fun U V => V*U)).symm

/-- The segmented family operator is the `r`th power of the tail segment at step size `t / r`. -/
private theorem tailFamily_power {D m : ℕ} (H : Fin m → Operator D) (t : ℝ) (r : ℕ) :
    pfFamily H t r = (tailSegment H (t/r))^r := by
  unfold pfFamily pfFamilyWord
  rw [pfInterpret_repeat]
  congr 1
  rw [tail_interpret_fst, tailSegment, tail_interpret_fst, List.map_ofFn, List.map_ofFn]
  rfl

/-- The first-order tail-sum specification holds for Hermitian finite families and positive
segment counts, in the form of [Childs et al., Proposition 15][ChildsEtAl2021Trotter]. -/
theorem trotterFirstOrderTailSum : TrotterFirstOrderTailSum := by
  intro D m r H t hr hH
  have hR : (0 : ℝ) < r := by exact_mod_cast hr
  let s := t/(r : ℝ)
  have hU : tailSegment H s ∈ Matrix.unitaryGroup (Fin D) ℂ := by
    have h := (product_formula_actual_word_and_tariffs D m 1 H s (fun _ => 0) hH).1
    rwa [tailFamily_power, Nat.cast_one, div_one, pow_one] at h
  have hSum : (∑ j, H j).IsHermitian := by
    change (∑ j : Fin m, H j)ᴴ = _
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl (fun j _ => (hH j).eq)
  have hV := hamiltonianEvolution_unitary hSum s
  have hpow : (HamiltonianEvolution (∑ j, H j) s)^r = HamiltonianEvolution (∑ j, H j) t := by
    rw [pf_evolution_pow]
    congr 1
    dsimp [s]
    field_simp
  rw [tailFamily_power, ← hpow]
  have hbound :=
      pf_unitary_power_error (tailSegment H s) (HamiltonianEvolution (∑ j, H j) s) hU hV r
  refine hbound.trans
      ((mul_le_mul_of_nonneg_left (tailSegment_error D m H s hH) (Nat.cast_nonneg r)).trans_eq ?_)
  rw [sq_abs]
  dsimp [s]
  field_simp

end Qatlib.Concepts.TrotterFormula.LieStrang
