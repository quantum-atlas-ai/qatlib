/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Order.RelClasses
import Mathlib.Order.SuccPred.Nat
import Mathlib.Tactic

/-!
# Balanced NAND evaluation and certificate-size recurrences

This module defines leaf assignments and recursive evaluation for balanced `d`-ary NAND trees.
It also defines the certificate-size recurrence from [AmbainisEtAl2009] and proves its
parity-dependent closed forms, positivity, and leaf-count bound.

## Main statements

* `certSize_closed_form`: solves the two size recurrences.
* `certSize_pos`: gives positivity for branching factor at least one.
* `certSize_le_leafCount`: bounds the recurrence by the number of leaves.

## References

* [Ambainis et al., 2009][AmbainisEtAl2009]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CertQuery09.MainResults.Source

/-- A Boolean assignment to the `d ^ k` leaves of a balanced `d`-ary tree of depth `k`. -/
abbrev LeafAssignment (d k : ℕ) : Type := Fin (d ^ k) → Bool

/-- Recursive balanced NAND evaluation, returning the leaf bit at depth zero and the negation of
the conjunction of all child values at positive depth. -/
def nandEval (d : ℕ) : (k : ℕ) → LeafAssignment d k → Bool
  | 0, x => x ⟨0, by simp⟩
  | k + 1, x =>
      !(∀ j : Fin d,
          nandEval d k
            (fun i => x (Fin.cast (pow_succ' d k).symm (finProdFinEquiv (j, i)))))

/-- The NAND certificate-size recurrence with value one at depth zero, zero-output size `d`
times the preceding one-output size, and one-output size equal to the preceding zero-output
size. -/
def certSize (d : ℕ) : Bool → ℕ → ℕ
  | _, 0 => 1
  | false, k + 1 => d * certSize d true k
  | true, k + 1 => certSize d false k

/-- The parity-dependent closed expression for the zero-output size recurrence: `d ^ (k / 2)` at
even depth and `d ^ ((k + 1) / 2)` at odd depth. -/
def certSizeZeroClosed (d k : ℕ) : ℕ :=
  if k % 2 = 0 then d ^ (k / 2) else d ^ ((k + 1) / 2)

/-- The parity-dependent closed expression for the one-output size recurrence: `d ^ (k / 2)` at
even depth and `d ^ ((k - 1) / 2)` at odd depth. -/
def certSizeOneClosed (d k : ℕ) : ℕ :=
  if k % 2 = 0 then d ^ (k / 2) else d ^ ((k - 1) / 2)

/-- Both certificate-size recurrences equal their parity-dependent closed expressions,
corresponding to the size formulas in [Ambainis et al., Eqs. (1)-(2)][AmbainisEtAl2009]. -/
theorem certSize_closed_form (d : ℕ) (k : ℕ) :
    certSize d false k = certSizeZeroClosed d k ∧
      certSize d true k = certSizeOneClosed d k := by
  induction k with
  | zero => simp [certSize, certSizeZeroClosed, certSizeOneClosed]
  | succ k ih =>
      obtain ⟨ih0, ih1⟩ := ih
      constructor
      · show d * certSize d true k = certSizeZeroClosed d (k + 1)
        rw [ih1]
        unfold certSizeZeroClosed certSizeOneClosed
        rcases Nat.even_or_odd k with hk | hk
        · have h0 : k % 2 = 0 := Nat.even_iff.mp hk
          have h1 : (k + 1) % 2 ≠ 0 := by omega
          have hdiv : (k + 1 + 1) / 2 = k / 2 + 1 := by omega
          simp [h0, h1, hdiv, Nat.pow_succ, mul_comm]
        · have h0 : k % 2 ≠ 0 := by
            intro h
            have := Nat.odd_iff.mp hk
            omega
          have h1 : (k + 1) % 2 = 0 := by omega
          have hdiv : (k + 1) / 2 = (k - 1) / 2 + 1 := by omega
          simp [h0, h1, hdiv, Nat.pow_succ, mul_comm]
      · show certSize d false k = certSizeOneClosed d (k + 1)
        rw [ih0]
        unfold certSizeZeroClosed certSizeOneClosed
        rcases Nat.even_or_odd k with hk | hk
        · have h0 : k % 2 = 0 := Nat.even_iff.mp hk
          have h1 : (k + 1) % 2 ≠ 0 := by omega
          simp [h0, h1]
        · have h0 : k % 2 ≠ 0 := by
            intro h
            have := Nat.odd_iff.mp hk
            omega
          have h1 : (k + 1) % 2 = 0 := by omega
          simp [h0, h1]

/-- For branching factor `d ≥ 1`, the size recurrence is positive for either output bit and
every depth. -/
theorem certSize_pos (d b k) (hd : 1 ≤ d) : 0 < certSize d b k := by
  induction k generalizing b with
  | zero => cases b <;> simp [certSize]
  | succ k ih =>
      cases b
      · simp only [certSize]
        exact Nat.mul_pos (by omega) (ih true)
      · simpa [certSize] using ih false

/-- For `d ≥ 1`, either certificate-size recurrence is at most the leaf count `d ^ k`. -/
theorem certSize_le_leafCount (d b k) (hd : 1 ≤ d) : certSize d b k ≤ d ^ k := by
  induction k generalizing b with
  | zero => cases b <;> simp [certSize]
  | succ k ih =>
      cases b
      · calc certSize d false (k + 1) = d * certSize d true k := rfl
          _ ≤ d * d ^ k := Nat.mul_le_mul_left d (ih true)
          _ = d ^ (k + 1) := (pow_succ' d k).symm
      · calc certSize d true (k + 1) = certSize d false k := rfl
          _ ≤ d ^ k := ih false
          _ ≤ d ^ (k + 1) := Nat.pow_le_pow_right hd (by omega)

end Qatlib.Papers.CertQuery09.MainResults.Source
