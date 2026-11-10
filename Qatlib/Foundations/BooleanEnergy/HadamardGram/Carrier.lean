/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Foundations.BooleanEnergy.HadamardGram

abbrev ColumnPair (N : ℕ) := {p : Fin N × Fin N // p.1 < p.2}

def left {N : ℕ} (p : ColumnPair N) : Fin N := p.val.1

def right {N : ℕ} (p : ColumnPair N) : Fin N := p.val.2

abbrev Variable (M N : ℕ) := (Fin M × Fin N) ⊕ (Fin M × ColumnPair N)

abbrev Configuration (M N : ℕ) := Variable M N → Bool

def main {M N : ℕ} (x : Configuration M N) (r : Fin M) (c : Fin N) : Bool :=
  x (Sum.inl (r,c))

def ancilla {M N : ℕ} (x : Configuration M N) (r : Fin M) (p : ColumnPair N) : Bool :=
  x (Sum.inr (r,p))

def bit (b : Bool) : ℝ := if b then 1 else 0

def spin (b : Bool) : ℝ := 1-2*bit b

theorem bit_values (b : Bool) : bit b = 0 ∨ bit b = 1 := by cases b <;> simp [bit]

theorem spin_values (b : Bool) : spin b = -1 ∨ spin b = 1 := by cases b <;> norm_num [spin,bit]

theorem spin_sq (b : Bool) : spin b ^ 2 = 1 := by cases b <;> norm_num [spin,bit]

def columnPairEquiv (N : ℕ) : ColumnPair N ≃ ((j : Fin N) × Fin j.val) where
  toFun p := ⟨p.val.2,⟨p.val.1.val,p.property⟩⟩
  invFun p := ⟨(⟨p.2.val,lt_trans p.2.isLt p.1.isLt⟩,p.1),p.2.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_columnPair (N : ℕ) : Fintype.card (ColumnPair N) = N*(N-1)/2 := by
  rw [Fintype.card_congr (columnPairEquiv N),Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) N,Finset.sum_range_id]

theorem card_variable (M N : ℕ) :
    Fintype.card (Variable M N) = M*N + M*(N*(N-1)/2) := by
  simp [Variable,Fintype.card_sum,Fintype.card_prod,card_columnPair]

theorem card_configuration (M N : ℕ) :
    Fintype.card (Configuration M N) = 2^(M*N + M*(N*(N-1)/2)) := by
  calc
    Fintype.card (Configuration M N) = Fintype.card Bool ^ Fintype.card (Variable M N) :=
      Fintype.card_fun
    _ = _ := by rw [card_variable]; rfl

def complete {M N : ℕ} (q : Fin M → Fin N → Bool) : Configuration M N
  | .inl (r,c) => q r c
  | .inr (r,p) => q r (left p) && q r (right p)

theorem main_complete {M N : ℕ} (q : Fin M → Fin N → Bool) : main (complete q) = q := rfl

theorem ancilla_complete {M N : ℕ} (q : Fin M → Fin N → Bool) (r : Fin M)
    (p : ColumnPair N) : ancilla (complete q) r p = (q r (left p) && q r (right p)) := rfl

end Qatlib.Foundations.BooleanEnergy.HadamardGram
