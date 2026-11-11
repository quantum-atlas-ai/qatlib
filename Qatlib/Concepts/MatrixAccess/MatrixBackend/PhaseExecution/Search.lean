/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution.Response
import Qatlib.Concepts.NativeNumerics.PhaseSynthesis.FinitePhaseSynthesis

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

/-! Materialized finite enumeration and actual early-stop search.
The refined interpreter may share previously produced tails, but it emits
every list cell it actually constructs. The full Cartesian list is produced
before search, including candidates that an early successful search never
tests. Values and the original tested/round/visit counters agree exactly with
the pinned producer; the new arithmetic/access ledger belongs to this same
refined interpreter, not to a claimed host evaluation strategy for old Lean.
-/
set_option autoImplicit false

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis

/-- Construction for append Run in the search model. -/
def appendRun {α : Type} : List α → List α → Run (List α)
  | [],ys => pure ys
  | x::xs,ys => do
    let tail ← appendRun xs ys
    allocate x tail

/-- Traced append returns the original concatenation, charging its copied cells. -/
@[simp] theorem appendRun_value {α : Type} (xs ys : List α) :
    (appendRun xs ys).value = xs ++ ys := by
  induction xs with
  | nil => simp [appendRun]
  | cons x xs ih => simp [appendRun, ih]

/-- Construction for flat Map Run in the search model. -/
def flatMapRun {α β : Type} (f : α → Run (List β)) : List α → Run (List β)
  | [] => pure []
  | x::xs => do
    let head ← f x
    let tail ← flatMapRun f xs
    appendRun head tail

/-- Traced concatenating map retains both value order and all actual construction work. -/
@[simp] theorem flatMapRun_value {α β : Type} (f : α → Run (List β)) (xs : List α) :
    (flatMapRun f xs).value = xs.flatMap (fun x => (f x).value) := by
  induction xs with
  | nil => simp [flatMapRun]
  | cons x xs ih => simp [flatMapRun, ih]

/-- Construction for range Run in the search model. -/
def rangeRun : ℕ → Run (List ℕ)
  | 0 => pure []
  | n+1 => do
    let previous ← rangeRun n
    let final ← allocate n []
    appendRun previous final

/-- The finite traced range is exactly the original ordered range. -/
@[simp] theorem rangeRun_value (n : ℕ) : (rangeRun n).value = List.range n := by
  induction n with
  | zero => simp [rangeRun]
  | succ n ih => simp [rangeRun, List.range_succ, ih]

/-- Construction for words in the search model. -/
def words (n : ℕ) : ℕ → Run (List (List ℕ))
  | 0 => allocate [] []
  | degree+1 => do
    let indices ← rangeRun n
    let tails ← words n degree
    flatMapRun (fun j => mapRun (fun tail => allocate j tail) tails) indices

/-- Traced enumeration constructs every original Cartesian candidate in the same order. -/
@[simp] theorem words_value (n degree : ℕ) :
    (words n degree).value = gridWords n degree := by
  induction degree with
  | zero => simp [words, gridWords]
  | succ degree ih => simp [words, gridWords, ih]

/-- Construction for decode in the search model. -/
def decode (points : List GaussianRat) (word : List ℕ) : Run PhaseData := do
  let index ← visit word 0 0
  let base ← visit points index gone
  let phases ← mapRun (fun j => visit points j gone) word.tail
  pure ⟨base,phases⟩

/-- Traced decoding preserves the actual phase packet and all out-of-range fallbacks. -/
@[simp] theorem decode_value (points : List GaussianRat) (word : List ℕ) :
    (decode points word).value = decodeGridWord points word := by
  cases word <;> simp [decode, decodeGridWord]

/-- Construction for search in the search model. -/
def search (p : List ℚ) (degree : ℕ) (tolerance : ℚ) (points : List GaussianRat) :
    List (List ℕ) → Run SearchResult
  | [] => pure ⟨none,0,0,0⟩
  | word::rest => do
    let data ← decode points word
    let actual ← score p degree data
    let accepted ← compare actual.1.1 tolerance
    if accepted then
      pure ⟨some data,1,actual.1.2,actual.2⟩
    else
      let tail ← search p degree tolerance points rest
      pure ⟨tail.value,tail.tested+1,tail.responseRounds+actual.1.2,
        tail.coefficientVisits+actual.2⟩

/-- Traced early-stop search returns exactly the original result and all original counters. -/
@[simp] theorem search_value (p : List ℚ) (degree : ℕ) (tolerance : ℚ)
    (points : List GaussianRat) (candidates : List (List ℕ)) :
    (search p degree tolerance points candidates).value =
      findGridWord p degree tolerance points candidates := by
  induction candidates with
  | nil => simp [search, findGridWord]
  | cons word rest ih =>
    simp only [search, value_bind, decode_value, score_value, compare_value]
    by_cases hs : (scoreData p degree (decodeGridWord points word)).1.1 ≤ tolerance
    · simp [findGridWord, hs]
    · simp [findGridWord, hs, ih]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution
