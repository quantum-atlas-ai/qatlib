/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.KnownCount.ObservedSearchLowerBoundStat
import Qatlib.Concepts.SearchStopping.KnownCount.ObservedSearchConsumers
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib
open scoped Classical

theorem observedSearchLowerBound : ObservedSearchLowerBound := by
  intro n W _ _ _ P ψ decode hP hψ hs
  by_cases hn : 2 ≤ n
  · obtain ⟨R,C,hC,hq,_,hout⟩ :=
      observed_all_output_query_purification n W P (by omega) hP
    let φ := deferredObservedInput (R := R) ψ
    let d : ((Fin n × Bool) × (W × Fin (R+1) × Bool)) → Option (Fin n) :=
      fun z => decode z.2.2.1.val (z.1,z.2.1)
    have hφ : Normalized φ := deferredObservedInput_normalized hψ
    have hmark (w : Fin n) : (2/3 : ℝ) ≤ MeasureProb
        (Run (workspaceBitOracle (W := W × Fin (R+1) × Bool) (fun z => decide (z=w))) C φ)
        (Finset.univ.filter fun z => d z = some w) := by
      rw [hout (Fin n) decode (fun z => decide (z=w)) ψ (some w)]
      exact hs w
    have hb := groverDecodedSearch_sharp_all_nontrivial C φ d hn hC hφ hmark
    rw [hq] at hb
    exact ⟨hb.trans (le_max_right _ _),fun _ => hb⟩
  · have hn' : (n : ℝ) ≤ 1 := by exact_mod_cast (by omega : n ≤ 1)
    refine ⟨hn'.trans (le_max_left _ _),?_⟩
    intro h
    exact (hn h).elim

end Qatlib.Concepts.SearchStopping.KnownCount
