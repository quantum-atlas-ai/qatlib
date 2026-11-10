/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.ObservedDecisionLowerBoundStat
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib
open scoped Classical

theorem observedDecisionLowerBound : ObservedDecisionLowerBound := by
  intro n W _ _ _ P ψ hP hψ hnull hmark
  by_cases hn : 0 < n
  · obtain ⟨R,C,hC,hq,_,hfull⟩ :=
      observed_query_same_cost_full_branch_purification n W P hn hP
    let φ := deferredObservedInput (R := R) ψ
    let E := adaptiveObservedHistoryEvent P R
    have hφ : Normalized φ := deferredObservedInput_normalized hψ
    have htransport (f : Fin n → Bool) :
        MeasureProb (Run (workspaceBitOracle (W := W × Fin (R+1) × Bool) f) C φ) E =
        observedAcceptance (workspaceBitOracle (W := W) f) P ψ :=
      observed_full_history_acceptance_transport P R C f ψ (hfull f ψ).1 (hfull f ψ).2
    have hnull' : MeasureProb (Run (1 : Matrix ((Fin n × Bool) × (W × Fin (R+1) × Bool))
        ((Fin n × Bool) × (W × Fin (R+1) × Bool)) ℂ) C φ) E ≤ 1/3 := by
      have hh := htransport (fun _ => false)
      rw [workspaceBitOracle_null] at hh
      exact hh.symm ▸ hnull
    have hmark' (w : Fin n) : (2/3 : ℝ) ≤ MeasureProb
        (Run (workspaceBitOracle (W := W × Fin (R+1) × Bool) (fun z => decide (z=w))) C φ) E := by
      rw [htransport]
      exact hmark w
    have hb := workspace_decision_query_lower_bound C φ E hC hφ hnull' hmark'
    simpa only [Fintype.card_fin,hq] using hb
  · have hz : n=0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp only [Nat.cast_zero]
    positivity

end Qatlib.Concepts.SearchStopping.KnownCount
