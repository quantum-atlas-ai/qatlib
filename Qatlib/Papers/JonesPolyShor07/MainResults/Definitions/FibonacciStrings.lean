/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-!
# Fibonacci strings and their weighted values

`FibString` consists of fixed-length Boolean lists with no adjacent true entries. The function
`zList` assigns Fibonacci weights to true entries, and `fibStringValue` restricts it to these
strings; elementary prefix and tail lemmas support later encoding arguments. See
[ShorJordan2008].

## Main statements

* `zList_cons`: Prepending a bit adds its Fibonacci weight when it is true and adds zero when it
  is false.
* `NoAdjList.of_cons_true_false`: Prepending true followed by false preserves `NoAdjList`.

## References

* [Shor and Jordan, 2008][ShorJordan2008]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JonesPolyShor07.MainResults.Definitions

/-- The condition that a Boolean list has no consecutive entries both equal to true. -/
def NoAdjList : List Bool → Prop
  | [] => True
  | [_] => True
  | a :: b :: t => ¬ (a = true ∧ b = true) ∧ NoAdjList (b :: t)

/-- Boolean lists of length m satisfying `NoAdjList`. -/
def FibString (m : ℕ) : Type := {l : List Bool // l.length = m ∧ NoAdjList l}

/-- The sum of Fibonacci weights of true entries, with a head entry weighted by the Fibonacci
number at the tail length plus two. -/
def zList : List Bool → ℕ
  | [] => 0
  | b :: rest => (if b = true then Nat.fib (rest.length + 2) else 0) + zList rest

/-- The Fibonacci-weighted value `zList` of a fixed-length Fibonacci string. -/
def fibStringValue {m : ℕ} (s : FibString m) : ℕ := zList s.1

/-- The empty Boolean list has Fibonacci-weighted value zero. -/
@[simp] theorem zList_nil : zList [] = 0 := rfl

/-- Prepending a bit adds its Fibonacci weight when it is true and adds zero when it is false. -/
theorem zList_cons (b : Bool) (rest : List Bool) :
    zList (b :: rest) = (if b = true then Nat.fib (rest.length + 2) else 0) + zList rest := rfl

/-- Prepending false leaves the Fibonacci-weighted value unchanged. -/
@[simp] theorem zList_false_cons (rest : List Bool) :
    zList (false :: rest) = zList rest := by
  rw [zList_cons]; simp

/-- Prepending true adds the Fibonacci number indexed by the tail length plus two. -/
@[simp] theorem zList_true_cons (rest : List Bool) :
    zList (true :: rest) = Nat.fib (rest.length + 2) + zList rest := by
  rw [zList_cons]; simp

/-- The tail of a list satisfying `NoAdjList` also satisfies `NoAdjList`. -/
theorem NoAdjList.tail {l : List Bool} (h : NoAdjList l) : NoAdjList l.tail := by
  cases l with
  | nil => simp [NoAdjList]
  | cons a r =>
    cases r with
    | nil => simp [NoAdjList]
    | cons b t => exact h.2

/-- Prepending false preserves `NoAdjList`. -/
theorem NoAdjList.of_cons_false {rest : List Bool} (h : NoAdjList rest) :
    NoAdjList (false :: rest) := by
  cases rest with
  | nil => simp [NoAdjList]
  | cons b t => simp [NoAdjList]; exact h

/-- Prepending true followed by false preserves `NoAdjList`. -/
theorem NoAdjList.of_cons_true_false {t : List Bool} (h : NoAdjList t) :
    NoAdjList (true :: false :: t) := by
  simp only [NoAdjList]
  refine ⟨by simp, ?_⟩
  exact NoAdjList.of_cons_false h

end Qatlib.Papers.JonesPolyShor07.MainResults.Definitions

namespace Qatlib.Papers.JonesPolyShor07.MainResults.Definitions

/-- Removing an initial false from a list satisfying `NoAdjList` preserves the condition. -/
theorem NoAdjList.of_false_cons {t : List Bool} (h : NoAdjList (false :: t)) : NoAdjList t := by
  cases t with
  | nil => trivial
  | cons b t => exact h.2

end Qatlib.Papers.JonesPolyShor07.MainResults.Definitions

namespace Qatlib.Papers.JonesPolyShor07.MainResults.Definitions

/-- Removing an initial true-false pair from a list satisfying `NoAdjList` preserves the
condition. -/
theorem NoAdjList.of_true_false_cons {t : List Bool} (h : NoAdjList (true :: false :: t)) :
    NoAdjList t := by
  have h' : NoAdjList (false :: t) := by simpa [NoAdjList] using h
  exact NoAdjList.of_false_cons h'

end Qatlib.Papers.JonesPolyShor07.MainResults.Definitions
