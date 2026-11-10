/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.CombinatorialBudgetRun
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.WalkSearch.Primitives
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MainResults
open scoped Classical

def sourceSearchScope (n τ : ℕ) : SearchCallScope :=
  ⟨max (n*n) (n.choose 2*τ),n*n,3⟩

def sourceSearchExecution (family : ScopedGroverFamily) (n τ : ℕ) : SGSExecution :=
  family.execution (sourceSearchScope n τ)

def sourceCapabilityFeeFactor (sgs : ScopedGroverFamily) (ets : PromisedEdgeSearchFamily) : ℕ :=
  max 1 (max sgs.κ ets.κ)

theorem source_preparation_call_supported (n τ : ℕ) : (sourceSearchScope n τ).contains (n*n) 2 (n*n) :=
  ⟨Nat.le_max_left _ _,le_rfl,by norm_num [sourceSearchScope]⟩

theorem source_triangle_call_supported (n τ : ℕ) (T : Finset (Fin n×Fin n))
    (hT : triCount T≤ n.choose 2*τ) :
    (sourceSearchScope n τ).contains (Fintype.card {t //t∈trianglesOf T}) 3 (n*n) := by
  refine ⟨?_,le_rfl,le_rfl⟩
  simpa only [Fintype.card_coe] using! hT.trans (Nat.le_max_right _ _)

theorem safeGroverReservation_mono (sgs : SGSExecution) (N M check floor : ℕ) (hNM : N≤ M) :
    safeGroverReservation sgs N check floor≤ safeGroverReservation sgs M check floor := by
  unfold safeGroverReservation
  gcongr

theorem source_triangle_preflight_fits (sgs : SGSExecution) (n τ : ℕ) (T : Finset (Fin n×Fin n))
    (hT : triCount T≤ n.choose 2*τ) :
    safeGroverReservation sgs (Fintype.card {t //t∈trianglesOf T}) 3 (n*n)≤ sourceTriangleReservation sgs n τ := by
  apply safeGroverReservation_mono
  simpa only [Fintype.card_coe] using! hT
end Qatlib.Concepts.WalkSearch.MainResults
