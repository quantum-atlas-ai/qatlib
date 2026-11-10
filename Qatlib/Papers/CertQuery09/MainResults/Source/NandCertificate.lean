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

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CertQuery09.MainResults.Source

abbrev LeafAssignment (d k : ℕ) : Type := Fin (d ^ k) → Bool

def nandEval (d : ℕ) : (k : ℕ) → LeafAssignment d k → Bool
  | 0, x => x ⟨0, by simp⟩
  | k + 1, x =>
      !(∀ j : Fin d,
          nandEval d k
            (fun i => x (Fin.cast (pow_succ' d k).symm (finProdFinEquiv (j, i)))))

def certSize (d : ℕ) : Bool → ℕ → ℕ
  | _, 0 => 1
  | false, k + 1 => d * certSize d true k
  | true, k + 1 => certSize d false k

def certSizeZeroClosed (d k : ℕ) : ℕ :=
  if k % 2 = 0 then d ^ (k / 2) else d ^ ((k + 1) / 2)

def certSizeOneClosed (d k : ℕ) : ℕ :=
  if k % 2 = 0 then d ^ (k / 2) else d ^ ((k - 1) / 2)

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

theorem certSize_pos (d b k) (hd : 1 ≤ d) : 0 < certSize d b k := by
  induction k generalizing b with
  | zero => cases b <;> simp [certSize]
  | succ k ih =>
      cases b
      · simp only [certSize]
        exact Nat.mul_pos (by omega) (ih true)
      · simpa [certSize] using ih false

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
