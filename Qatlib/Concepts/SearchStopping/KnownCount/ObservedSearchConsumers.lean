/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.ObservedOutputReadout

/-!
# Decoded search query bounds

`groverDecodedSearch_query_positive` rules out zero-query decoded singleton search on at least
two addresses. `groverDecodedSearch_sharp_all_nontrivial` proves n ≤ 64q² for a unitary circuit
whose decoder succeeds with probability at least 2/3 for every singleton bit oracle.

For the mathematical background, see [BealsEtAl2001].

## Main statements

* `groverDecodedSearch_sharp_all_nontrivial`: For at least two addresses, decoded singleton
  search with success at least 2/3 for every target satisfies n ≤ 64 times the squared circuit
  query count.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability

open Qatlib.Concepts.QueryComplexity.AdversarySearch

namespace Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib
open scoped Classical

/-- On at least two addresses, a normalized unitary circuit whose decoder finds every singleton
marked address with probability at least 2/3 uses a positive number of queries. -/
theorem groverDecodedSearch_query_positive {n : ℕ} {W : Type}
    [Fintype W] [DecidableEq W] (C : Circuit ((Fin n × Bool) × W))
    (ψ : QState ((Fin n × Bool) × W))
    (decode : ((Fin n × Bool) × W) → Option (Fin n))
    (hn : 2 ≤ n) (hC : IsUnitaryCircuit C) (hψ : Normalized ψ)
    (hs : ∀ w : Fin n, (2/3 : ℝ) ≤ MeasureProb
      (Run (workspaceBitOracle (W := W) (fun z => decide (z=w))) C ψ)
      (Finset.univ.filter fun z => decode z = some w)) : 0 < QueryCount C := by
  by_contra ht
  have hz : QueryCount C = 0 := Nat.eq_zero_of_not_pos ht
  let a : Fin n := ⟨0,by omega⟩
  let b : Fin n := ⟨1,by omega⟩
  have hab : a ≠ b := by intro h; have hh := congrArg Fin.val h; simp [a,b] at hh
  let E (w : Fin n) := Finset.univ.filter fun z => decode z = some w
  let φ := Run (1 : Matrix ((Fin n × Bool) × W) ((Fin n × Bool) × W) ℂ) C ψ
  have hφ : Normalized φ := hC.normalized_run (Submonoid.one_mem _) hψ
  have hmass (w : Fin n) : (2/3 : ℝ) ≤ MeasureProb φ (E w) := by
    have hw := hs w
    rw [run_eq_of_queryCount_eq_zero _ 1 C hz ψ] at hw
    exact hw
  have hd : Disjoint (E a) (E b) := by
    apply Finset.disjoint_left.mpr
    intro z ha hb
    exact hab (Option.some.inj ((Finset.mem_filter.mp ha).2.symm.trans
      (Finset.mem_filter.mp hb).2))
  have hsum : MeasureProb φ (E a) + MeasureProb φ (E b) ≤ 1 := by
    rw [← measureProb_union φ hd]
    exact (measureProb_mono φ (Finset.subset_univ _)).trans (measureProb_univ hφ).le
  linarith [hmass a,hmass b]

/-- For at least two addresses, decoded singleton search with success at least 2/3 for every
target satisfies n ≤ 64 times the squared circuit query count. -/
theorem groverDecodedSearch_sharp_all_nontrivial {n : ℕ} {W : Type}
    [Fintype W] [DecidableEq W] (C : Circuit ((Fin n × Bool) × W))
    (ψ : QState ((Fin n × Bool) × W))
    (decode : ((Fin n × Bool) × W) → Option (Fin n))
    (hn : 2 ≤ n) (hC : IsUnitaryCircuit C) (hψ : Normalized ψ)
    (hs : ∀ w : Fin n, (2/3 : ℝ) ≤ MeasureProb
      (Run (workspaceBitOracle (W := W) (fun z => decide (z=w))) C ψ)
      (Finset.univ.filter fun z => decode z = some w)) :
    (n : ℝ) ≤ 64 * (QueryCount C : ℝ)^2 := by
  by_cases hlarge : 6 ≤ n
  · simpa only [Fintype.card_fin] using
      workspace_search_query_lower_bound C ψ decode hC hψ (by simpa using hlarge) hs
  · have hpos := groverDecodedSearch_query_positive C ψ decode hn hC hψ hs
    have hT : (1 : ℝ) ≤ QueryCount C := by exact_mod_cast hpos
    have hn' : (n : ℝ) ≤ 5 := by exact_mod_cast (by omega : n ≤ 5)
    nlinarith

end Qatlib.Concepts.SearchStopping.KnownCount
