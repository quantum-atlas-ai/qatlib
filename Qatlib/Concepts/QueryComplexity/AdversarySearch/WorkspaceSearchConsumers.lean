/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceSearchBounds

/-!
# Matching workspace search query bounds

This module combines the workspace hybrid lower bound from [BennettEtAl1997] with the explicit
Grover upper bound from [BrassardEtAl2002]. For `n ≥ 3`, a unitary circuit that identifies every
singleton with probability at least 2/3 satisfies N ≤ 64Q², and the constructed circuit achieves
the same success threshold using at most π√N/4 queries.

## Main statements

* `workspace_search_matching_actual_consumer`: combine the search lower bound with an explicit
  successful Grover circuit.

## References

* [Bennett et al., 1997][BennettEtAl1997]
* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.AdversarySearch

/-- For `n ≥ 3`, any unitary workspace search circuit identifying every singleton with
probability at least 2/3 satisfies N ≤ 64Q², while the explicit workspace Grover circuit
succeeds with probability at least 2/3 using at most π√N/4 queries. The lower bound follows
the hybrid method of [BennettEtAl1997]. -/
theorem workspace_search_matching_actual_consumer {W : Type} [Fintype W] [DecidableEq W]
    (n : ℕ) (w : W) (C : Circuit ((Reg n × Bool) × W)) (ψ : QState ((Reg n × Bool) × W))
    (decode : ((Reg n × Bool) × W) → Option (Reg n))
    (hn : 3 ≤ n) (hC : IsUnitaryCircuit C) (hψ : Normalized ψ)
    (hmark : ∀ x : Reg n, MeasureProb
        (Run (workspaceBitOracle (W := W) (fun y : Reg n => decide (y = x))) C ψ)
        (Finset.univ.filter (fun p => decode p = some x)) ≥ 2 / 3) :
    (Fintype.card (Reg n) : ℝ) ≤ 64 * (QueryCount C : ℝ) ^ 2 ∧
    (QueryCount (workspaceGroverCircuit (W := W) n (singletonSearchIterations n)) : ℝ) ≤
      Real.pi * Real.sqrt (Fintype.card (Reg n) : ℝ) / 4 ∧
    (∀ x : Reg n, MeasureProb
      (Run (workspaceBitOracle (W := W) (fun y : Reg n => decide (y = x)))
        (workspaceGroverCircuit (W := W) n (singletonSearchIterations n))
        (Ket ((ZeroStr n, false), w)))
      (Finset.univ.filter (fun p => (some p.1.1 : Option (Reg n)) = some x)) ≥ 2 / 3) := by
  have hn2 : 2 ≤ n := by omega
  have h8 : (8 : ℕ) ≤ 2 ^ n := by
    calc (8 : ℕ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hcard : 6 ≤ Fintype.card (Reg n) := by
    rw [card_reg n]
    omega
  have hN8 : (8 : ℝ) ≤ (Fintype.card (Reg n) : ℝ) := by
    rw [card_reg]
    exact_mod_cast h8
  have hNpos : (0 : ℝ) < (Fintype.card (Reg n) : ℝ) := by linarith
  refine ⟨workspace_search_query_lower_bound C ψ decode hC hψ hcard hmark, ?_, ?_⟩
  · exact (workspace_singleton_search_actual_upper n w (ZeroStr n) hn2).2.1
  · intro x
    have hev : (Finset.univ.filter (fun p : (Reg n × Bool) × W =>
          (some p.1.1 : Option (Reg n)) = some x))
        = workspaceQueryFiber (W := W) x := by
      ext p
      simp [workspaceQueryFiber, Finset.mem_filter]
    rw [hev]
    have h := (workspace_singleton_search_actual_upper n w x hn2).1
    have h23 : (2 / 3 : ℝ) ≤ 1 - 1 / (Fintype.card (Reg n) : ℝ) := by
      have hle : (1 : ℝ) / (Fintype.card (Reg n) : ℝ) ≤ 1 / 3 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith
    exact h23.trans h

end Qatlib.Concepts.QueryComplexity.AdversarySearch
