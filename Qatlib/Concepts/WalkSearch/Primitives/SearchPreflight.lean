/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.ClassificationLedger
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical BigOperators

def safeGroverReservation (sgs : SGSExecution) (N check floor : ℕ) : ℕ :=
  sgs.κ*(Nat.log 2 (max N floor+1)+2)*(check+1)*(Nat.sqrt (max N floor+1)+1)

inductive PreflightSearchResult (α : Type) where
  | timeout : PreflightSearchResult α
  | completed : Option α→ℕ→PreflightSearchResult α

def safeGroverPreflight (sgs : SGSExecution) {α : Type} [Fintype α] (marked : α→Bool)
    (check floor budget : ℕ) (ρ : sgs.seed) : PreflightSearchResult α :=
  if safeGroverReservation sgs (Fintype.card α) check floor≤ budget then
    .completed (operationalSgsFind sgs marked check floor ρ) (operationalSgsFindCost sgs marked check floor ρ)
  else .timeout

theorem sgsFindCost_le_reservation (sgs : SGSExecution) {α : Type} [Fintype α] (marked : α→Bool)
    (check floor : ℕ) (ρ : sgs.seed) :
    operationalSgsFindCost sgs marked check floor ρ≤ safeGroverReservation sgs (Fintype.card α) check floor :=
  sgs.charges _ check floor ρ

theorem safeGroverPreflight_charge (sgs : SGSExecution) {α : Type} [Fintype α] (marked : α→Bool)
    (check floor budget : ℕ) (ρ : sgs.seed) (out : Option α) (q : ℕ)
    (h : safeGroverPreflight sgs marked check floor budget ρ=.completed out q) : q≤ budget := by
  unfold safeGroverPreflight at h
  split_ifs at h with hb
  · have he:=PreflightSearchResult.completed.inj h
    exact he.2 ▸ (sgsFindCost_le_reservation sgs marked check floor ρ).trans hb

theorem safeGroverPreflight_timeout (sgs : SGSExecution) {α : Type} [Fintype α] (marked : α→Bool)
    (check floor budget : ℕ) (ρ : sgs.seed)
    (h : budget< safeGroverReservation sgs (Fintype.card α) check floor) :
    safeGroverPreflight sgs marked check floor budget ρ=.timeout := by
  exact if_neg (by omega)

theorem safeGroverPreflight_preserves (sgs : SGSExecution) {α : Type} [Fintype α] (marked : α→Bool)
    (check floor budget : ℕ) (ρ : sgs.seed)
    (h : safeGroverReservation sgs (Fintype.card α) check floor≤ budget) :
    safeGroverPreflight sgs marked check floor budget ρ=
      .completed (operationalSgsFind sgs marked check floor ρ) (operationalSgsFindCost sgs marked check floor ρ) := if_pos h

theorem safeGroverPreflight_output (sgs : SGSExecution) {α : Type} [Fintype α] (marked : α→Bool)
    (check floor budget : ℕ) (ρ : sgs.seed) (out : Option α) (q : ℕ)
    (h : safeGroverPreflight sgs marked check floor budget ρ=.completed out q) :
    operationalSgsFind sgs marked check floor ρ=out := by
  unfold safeGroverPreflight at h
  split_ifs at h with hb
  exact (PreflightSearchResult.completed.inj h).1
end Qatlib.Concepts.WalkSearch.Primitives
