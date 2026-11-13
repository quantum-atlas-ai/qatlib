/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.ClassificationLedger

/-!
# Budget preflight for finite search

`safeGroverPreflight` compares a worst-case search reservation against an available budget
before running an `SGSExecution`. Completed calls preserve the underlying search result and have
a charge within budget; insufficient reservations produce `timeout`.

The reservation uses the logarithmic and square-root search cost structure associated with
[BoyerEtAl1998].

## Main statements

* `safeGroverPreflight_charge`: every completed charge is within budget.
* `safeGroverPreflight_preserves`: sufficient budget preserves execution and cost.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical BigOperators

/-- The stated worst-case search cost bound for database size `N`, checker cost `check`, and
parameter `floor`. -/
def safeGroverReservation (sgs : SGSExecution) (N check floor : ℕ) : ℕ :=
  sgs.κ*(Nat.log 2 (max N floor+1)+2)*(check+1)*(Nat.sqrt (max N floor+1)+1)

/-- A search outcome that either records a timeout or a completed optional result together with
its charge. -/
inductive PreflightSearchResult (α : Type) where
  | timeout : PreflightSearchResult α
  | completed : Option α→ℕ→PreflightSearchResult α

/-- Runs the finite search and records its cost if the reservation fits the budget, and returns
`timeout` otherwise. -/
def safeGroverPreflight (sgs : SGSExecution) {α : Type} [Fintype α] (marked : α→Bool)
    (check floor budget : ℕ) (ρ : sgs.seed) : PreflightSearchResult α :=
  if safeGroverReservation sgs (Fintype.card α) check floor≤ budget then
    .completed (operationalSgsFind sgs marked check floor ρ) (operationalSgsFindCost sgs marked check floor ρ)
  else .timeout

/-- The transported search cost is at most its worst-case reservation. -/
theorem sgsFindCost_le_reservation (sgs : SGSExecution) {α : Type} [Fintype α] (marked : α→Bool)
    (check floor : ℕ) (ρ : sgs.seed) :
    operationalSgsFindCost sgs marked check floor ρ≤ safeGroverReservation sgs (Fintype.card α) check floor :=
  sgs.charges _ check floor ρ

/-- A completed preflight search has recorded charge at most the supplied budget. -/
theorem safeGroverPreflight_charge (sgs : SGSExecution) {α : Type} [Fintype α] (marked : α→Bool)
    (check floor budget : ℕ) (ρ : sgs.seed) (out : Option α) (q : ℕ)
    (h : safeGroverPreflight sgs marked check floor budget ρ=.completed out q) : q≤ budget := by
  unfold safeGroverPreflight at h
  split_ifs at h with hb
  · have he:=PreflightSearchResult.completed.inj h
    exact he.2 ▸ (sgsFindCost_le_reservation sgs marked check floor ρ).trans hb

/-- A budget strictly smaller than the reservation causes the preflight search to return
`timeout`. -/
theorem safeGroverPreflight_timeout (sgs : SGSExecution) {α : Type} [Fintype α] (marked : α→Bool)
    (check floor budget : ℕ) (ρ : sgs.seed)
    (h : budget< safeGroverReservation sgs (Fintype.card α) check floor) :
    safeGroverPreflight sgs marked check floor budget ρ=.timeout := by
  exact if_neg (by omega)

/-- When the reservation fits the budget, preflight returns the underlying search result and its
execution cost. -/
theorem safeGroverPreflight_preserves (sgs : SGSExecution) {α : Type} [Fintype α] (marked : α→Bool)
    (check floor budget : ℕ) (ρ : sgs.seed)
    (h : safeGroverReservation sgs (Fintype.card α) check floor≤ budget) :
    safeGroverPreflight sgs marked check floor budget ρ=
      .completed (operationalSgsFind sgs marked check floor ρ) (operationalSgsFindCost sgs marked check floor ρ) := if_pos h

/-- The optional output of a completed preflight search equals the result of the underlying
finite search. -/
theorem safeGroverPreflight_output (sgs : SGSExecution) {α : Type} [Fintype α] (marked : α→Bool)
    (check floor budget : ℕ) (ρ : sgs.seed) (out : Option α) (q : ℕ)
    (h : safeGroverPreflight sgs marked check floor budget ρ=.completed out q) :
    operationalSgsFind sgs marked check floor ρ=out := by
  unfold safeGroverPreflight at h
  split_ifs at h with hb
  exact (PreflightSearchResult.completed.inj h).1
end Qatlib.Concepts.WalkSearch.Primitives
