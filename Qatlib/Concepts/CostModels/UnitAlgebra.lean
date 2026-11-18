/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CostModels.CountBridge
public import Qatlib.Concepts.CostModels.Budget
public import Qatlib.Concepts.CostModels.Recurrence

@[expose] public section

/-!
# Units, unknown propagation, and same-artifact counting

This module defines the unit algebra of the toolkit. The macro-expansion contract carries a
positive elementary cost per macro gate; expansion counts add over serial composition
and never invent zero. Unknown propagation is strict: composing with an unmodeled
profile stays unmodeled in every field, so `none` never acts as a silent zero. The
same-artifact bridge re-exports that word profiles count queries and macro gates with
the public `QueryCount` and `GateCount`, and that concatenation is exactly serial
addition; recursion feeders over actual subcalls remain those of `Recurrence`.

## Main statements

* `macroCounts_add`: expansion counts add over serial composition.
* `opaqueSerial`: composing with the unmodeled profile stays unmodeled.
* `wordProfileQ`/`wordProfileG`: word profiles use the public counters.
* `profAppend`: concatenation is serial addition (re-export from `CountBridge`).
-/

set_option autoImplicit false
set_option warningAsError true

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CostModels.Profile
open Qatlib.Concepts.CostModels.CountBridge
open Qatlib.Concepts.CostModels.Budget
open Qatlib.Concepts.CostModels.Compose
open Qatlib.Concepts.CostModels.Recurrence

namespace Qatlib.Concepts.CostModels.UnitAlgebra

/-- A macro-expansion unit contract: one macro gate accounts for `basic` elementary
gates in the compiled artifact. The contract is a bookkeeping bridge between the
macro-gate unit and the elementary unit; it does not construct a compiler and does not
claim that any given macro realizes this cost. -/
structure MacroUnit where
  /-- Elementary gates accounted per macro gate. -/
  basic : ℕ
  /-- The accounted cost is positive: a macro is never free. -/
  basic_pos : 0 < basic

/-- The elementary count of `k` macro gates under a unit contract. -/
def macroCounts (u : MacroUnit) (k : ℕ) : ℕ := k * u.basic

/-- Expansion counts add over serial composition. -/
theorem macroCounts_add (u : MacroUnit) (a b : ℕ) :
    macroCounts u (a + b) = macroCounts u a + macroCounts u b := by
  simp only [macroCounts]
  ring

/-- The expansion of `k` macros is positive whenever `k` is. -/
theorem macroCounts_pos (u : MacroUnit) {k : ℕ} (hk : 0 < k) :
    0 < macroCounts u k :=
  Nat.mul_pos hk u.basic_pos

/-- Composing with the unmodeled profile stays unmodeled in every field: unknown
propagation is strict and `none` never silently acts as zero. -/
theorem opaqueSerial (p : CostProfile) :
    serial opaqueProfile p = opaqueProfile := by
  ext1 <;> simp [serial, opaqueProfile, optAdd]

/-- A profile with a measured query count never satisfies an opaque budget: the
same-artifact counting keeps `some k` and `none` apart (re-exported from
`Qatlib.Concepts.CostModels.Budget.budgetNoOpaque`). -/
theorem budgetZeroNotOpaque {k : ℕ} {b : CostProfile} (hb : b.queries = some k) :
    ¬ BudgetLe opaqueProfile b :=
  budgetNoOpaque hb

/-- Word profiles count queries with the public `QueryCount`. -/
theorem wordProfileQ {I : Type*} (C : Circuit I) :
    (wordProfile C).queries = some (QueryCount C) := rfl

/-- Word profiles count macro gates with the public `GateCount`. -/
theorem wordProfileG {I : Type*} (C : Circuit I) :
    (wordProfile C).macroGates = some (GateCount C) := rfl

/-- The concatenation of words counts exactly as serial addition of their profiles
(same-artifact counting; re-exported from `Qatlib.Concepts.CostModels.CountBridge.profAppend`). -/
theorem profAppend {I : Type*} (C D : Circuit I) :
    wordProfile (C ++ D) = serial (wordProfile C) (wordProfile D) :=
  CountBridge.profAppend C D

/-- Recurrence feeders over actual subcalls stay those of `Recurrence`: the
factorization-tree query total is the root call plus the prime-factor subcalls
(re-export of `Qatlib.Concepts.CostModels.Recurrence.facQueryEq`). -/
theorem recFeeder (q : ℕ → ℕ) (N : ℕ) :
    (treeCost (facTree q N)).queries
      = some (q N + ∑ p ∈ (N - 1).primeFactors, q p) :=
  facQueryEq q N

end Qatlib.Concepts.CostModels.UnitAlgebra
