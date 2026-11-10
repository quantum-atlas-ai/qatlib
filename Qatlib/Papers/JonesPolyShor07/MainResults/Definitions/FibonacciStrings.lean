/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JonesPolyShor07.MainResults.Definitions

def NoAdjList : List Bool → Prop
  | [] => True
  | [_] => True
  | a :: b :: t => ¬ (a = true ∧ b = true) ∧ NoAdjList (b :: t)

def FibString (m : ℕ) : Type := {l : List Bool // l.length = m ∧ NoAdjList l}

def zList : List Bool → ℕ
  | [] => 0
  | b :: rest => (if b = true then Nat.fib (rest.length + 2) else 0) + zList rest

def fibStringValue {m : ℕ} (s : FibString m) : ℕ := zList s.1

@[simp] theorem zList_nil : zList [] = 0 := rfl

theorem zList_cons (b : Bool) (rest : List Bool) :
    zList (b :: rest) = (if b = true then Nat.fib (rest.length + 2) else 0) + zList rest := rfl

@[simp] theorem zList_false_cons (rest : List Bool) :
    zList (false :: rest) = zList rest := by
  rw [zList_cons]; simp

@[simp] theorem zList_true_cons (rest : List Bool) :
    zList (true :: rest) = Nat.fib (rest.length + 2) + zList rest := by
  rw [zList_cons]; simp

theorem NoAdjList.tail {l : List Bool} (h : NoAdjList l) : NoAdjList l.tail := by
  cases l with
  | nil => simp [NoAdjList]
  | cons a r =>
    cases r with
    | nil => simp [NoAdjList]
    | cons b t => exact h.2

theorem NoAdjList.of_cons_false {rest : List Bool} (h : NoAdjList rest) :
    NoAdjList (false :: rest) := by
  cases rest with
  | nil => simp [NoAdjList]
  | cons b t => simp [NoAdjList]; exact h

theorem NoAdjList.of_cons_true_false {t : List Bool} (h : NoAdjList t) :
    NoAdjList (true :: false :: t) := by
  simp only [NoAdjList]
  refine ⟨by simp, ?_⟩
  exact NoAdjList.of_cons_false h

end Qatlib.Papers.JonesPolyShor07.MainResults.Definitions

namespace Qatlib.Papers.JonesPolyShor07.MainResults.Definitions

theorem NoAdjList.of_false_cons {t : List Bool} (h : NoAdjList (false :: t)) : NoAdjList t := by
  cases t with
  | nil => trivial
  | cons b t => exact h.2

end Qatlib.Papers.JonesPolyShor07.MainResults.Definitions

namespace Qatlib.Papers.JonesPolyShor07.MainResults.Definitions

theorem NoAdjList.of_true_false_cons {t : List Bool} (h : NoAdjList (true :: false :: t)) :
    NoAdjList t := by
  have h' : NoAdjList (false :: t) := by simpa [NoAdjList] using h
  exact NoAdjList.of_false_cons h'

end Qatlib.Papers.JonesPolyShor07.MainResults.Definitions
