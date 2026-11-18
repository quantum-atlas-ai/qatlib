/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.QueryWordCore.Circuit
public import Qatlib.Concepts.CostModels.Profile
public import Qatlib.Concepts.CostModels.Compose

@[expose] public section

/-!
# Counting bridge from query words to cost profiles

`wordProfile` reads the measured counts of a public `Circuit` word — oracle
queries and explicit matrix macro gates — into the seven-field `CostProfile`
of the toolkit contract. Elementary gates, T-count, depth, and width stay
unmodeled (`none`): a macro gate has not been decomposed into a finite
elementary gate set yet, and unmodeled is never a zero. Concatenation and
repetition of words agree with `serial` composition and with the serial
repetition algebra (`Nat.mul_comm` welds the two multiplication
orientations), which identifies the two count-level composition conventions. Circuit-level end-to-end instances (Deutsch-Jozsa)
live in the verification regression, not in the Concepts layer.

## Main statements

* `profAppend`: the profile of `C ++ D` is the serial composition of the two
  profiles.
* `profRepeatQ` / `profRepeatM`: repeating a word multiplies its measured
  counts exactly as the public repetition lemmas do.
* `repeatBridgeQ` / `repeatBridgeM`: the serial cost-tree repetition of a word
  profile yields the public repeated counts.
* `emptyProfEq` / `emptyProfNe`: the empty word measures two genuine zeros
  and five unmodeled fields, and is not the all-zero empty profile.
* `opaqueAbsorbQ`: serial composition with an unmodeled segment leaves the
  query total unmodeled.
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CostModels.Profile
open Qatlib.Concepts.CostModels.Compose

namespace Qatlib.Concepts.CostModels.CountBridge

variable {I : Type*}

/-- The measured count profile of a query word: oracle queries and explicit
matrix macro gates are counted; elementary gates, T-count, depth, and width
are not modeled yet and stay `none`, never a fake zero. -/
def wordProfile (C : Circuit I) : CostProfile where
  queries := some (QueryCount C)
  macroGates := some (GateCount C)
  oneQ := none
  twoQ := none
  tCount := none
  depth := none
  width := none

/-- The profile of a concatenation is the serial composition of the two
profiles: query and macro-gate counts add, and the unmodeled fields remain
unmodeled, including width. -/
theorem profAppend (C D : Circuit I) :
    wordProfile (C ++ D) = serial (wordProfile C) (wordProfile D) := by
  ext <;> simp [wordProfile, serial, optAdd, queryCount_append, gateCount_append]

/-- Repeating a word `k` times multiplies its measured query count by `k`,
matching the public repetition count `queryCount_repeatCircuit`. -/
theorem profRepeatQ [Fintype I] [DecidableEq I] (C : Circuit I) (k : ℕ) :
    (wordProfile (RepeatCircuit C k)).queries = some (k * QueryCount C) := by
  simp [wordProfile, queryCount_repeatCircuit]

/-- Repeating a word `k` times multiplies its measured macro-gate count by
`k`, matching the public repetition count `gateCount_repeatCircuit`. -/
theorem profRepeatM [Fintype I] [DecidableEq I] (C : Circuit I) (k : ℕ) :
    (wordProfile (RepeatCircuit C k)).macroGates = some (k * GateCount C) := by
  simp [wordProfile, gateCount_repeatCircuit]

/-- The query-count bridge welded to the serial repetition algebra: serially
repeating the word profile `k` times in a cost tree yields exactly the
public repeated query count; `Nat.mul_comm` reconciles the cost-tree `a * k`
orientation with the public `k * a`. -/
theorem repeatBridgeQ (C : Circuit I) (k : ℕ) :
    (treeCost (treeRepeat (wordProfile C) k)).queries = some (k * QueryCount C) := by
  rw [repeatQueryMul rfl k, Nat.mul_comm]

/-- Macro-gate counterpart of `repeatBridgeQ`: the serial repetition tree yields
exactly the public repeated macro-gate count. -/
theorem repeatBridgeM (C : Circuit I) (k : ℕ) :
    (treeCost (treeRepeat (wordProfile C) k)).macroGates = some (k * GateCount C) := by
  rw [repeatMacroMul rfl k, Nat.mul_comm]

/-- Positive example: the empty word carries genuine measured zeros for
queries and macro gates while the five remaining fields stay unmodeled. -/
theorem emptyProfEq :
    wordProfile ([] : Circuit I)
      = { queries := some 0, macroGates := some 0, oneQ := none, twoQ := none,
          tCount := none, depth := none, width := none } := rfl

/-- The empty word profile is not the all-zero empty profile: the five
unmodeled fields keep "not modeled" distinguishable from a measured zero. -/
theorem emptyProfNe : wordProfile ([] : Circuit I) ≠ emptyProfile := by
  intro h
  have hw : (wordProfile ([] : Circuit I)).width = emptyProfile.width :=
    congrArg _ h
  simp [wordProfile, emptyProfile] at hw

/-- Serial composition with a fully unmodeled segment leaves the query total
unmodeled — opaque absorption on the count side, mirroring `budgetNoOpaque`
on the budget side. -/
theorem opaqueAbsorbQ (C : Circuit I) :
    (serial opaqueProfile (wordProfile C)).queries = none := rfl

end Qatlib.Concepts.CostModels.CountBridge
