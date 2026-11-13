/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryCoreDefs
import Qatlib.Concepts.GraphQuery.EdgeQuery.GraphCollision
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Query-cost vocabulary for the learning-graph paper

Source: A. Belovs, *Learning-Graph-Based Quantum Algorithm for k-distinctness*,
fixed preprint arXiv:1205.1534v2 (`arXiv:1205.1534v2 [quant-ph] 9 Aug 2012`).
Paper block `MainResults`; this module carries the paper-local vocabulary shared
by the Theorem 7, Theorem 8 and Lemma 9 contracts.

* `BoundedErrorQueryCostAtMost f T` is the paper's phrase *"can be solved in
  `T` queries with bounded error"*.  It is phrased over the house counted-query
  circuit model (`Circuit`, `Run`, `QueryCount` of
  `Qatlib.Foundations.QueryWordCore.Circuit`) with the house
  bounded-error run predicate
  `Qatlib.Concepts.AdversaryBounds.AdvDuality.IsBoundedErrorRun`
  (unitary circuit word, normalized initial state, POVM readout, success
  probability `≥ 1 − ε` with `ε ≤ 1/2` on every input).  `T` bounds the
  worst-case query ledger `QueryCount C`.
* `graphCollisionWord` is Theorem 7's Boolean input encoding: the queried word
  is the vertex labelling `x : Fin n → Fin 2`, and the known graph `G` is fixed
  and never queried.  The decision function itself is the house
  `Qatlib.Concepts.GraphQuery.EdgeQuery.graphCollision` read on
  that labelling.
* `kDistinctness` is Theorem 8's decision function, paper §1:
  `f(x) = 1` iff some `k` positions carry one common value.

These are definitions only; no source claim is asserted in this module.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GraphQuery.EdgeQuery

namespace Qatlib.Papers.LearnGraphDis12.MainResults.QueryCost

/-- `BoundedErrorQueryCostAtMost f T`: the Boolean function `f` on `q`-ary
`n`-letter words has a bounded-error query run (workspace `Fin m`, one unitary
circuit word with its normalized initial state and POVM readout, error
`ε ≤ 1/2` on every input) whose worst-case query ledger is at most `T`.

`T` is a real number so that a paper bound such as `c·√n·α^{1/6}` can be
compared directly; `QueryCount C` is the machine-counted number of query steps
of the run. -/
def BoundedErrorQueryCostAtMost {n q : ℕ} [NeZero q]
    (f : (Fin n → Fin q) → Bool) (T : ℝ) : Prop :=
  ∃ (m : ℕ) (C : Circuit ((Fin n × Fin q) × Fin m))
    (psi : QState ((Fin n × Fin q) × Fin m))
    (out : Bool → Matrix ((Fin n × Fin q) × Fin m) ((Fin n × Fin q) × Fin m) ℂ)
    (eps : ℝ),
    IsBoundedErrorRun (fun x : Fin n → Fin q => x) f C psi out eps ∧
      (QueryCount C : ℝ) ≤ T

/-- A cost bound is monotone in the budget. -/
theorem BoundedErrorQueryCostAtMost.mono {n q : ℕ} [NeZero q]
    {f : (Fin n → Fin q) → Bool} {T T' : ℝ}
    (h : BoundedErrorQueryCostAtMost f T) (hle : T ≤ T') :
    BoundedErrorQueryCostAtMost f T' := by
  obtain ⟨m, C, psi, out, eps, hrun, hq⟩ := h
  exact ⟨m, C, psi, out, eps, hrun, le_trans hq hle⟩

/-- Theorem 7's input word: the Boolean vertex labelling `x : Fin n → Fin 2`
read as the marking `x i = 1`.  The known graph `G` is a fixed parameter of the
problem and is not part of the queried word; the decision function is the house
`graphCollision` applied to the adjacency of `G`. -/
def graphCollisionWord {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Fin 2) : Bool :=
  graphCollision (fun u v => G.Adj u v) (fun i => decide (x i = 1))

/-- Theorem 8's `k`-distinctness decision function on `n` letters over the
alphabet `Fin q`, paper §1: `f(x) = 1` iff there are `k` positions carrying one
common value (`a₁,…,a_k` pairwise distinct with `x_{a_i}` all equal). -/
def kDistinctness (k n q : ℕ) (x : Fin n → Fin q) : Bool :=
  decide (∃ S : Finset (Fin n), S.card = k ∧ ∃ a : Fin q, ∀ i ∈ S, x i = a)

/-- Sanity check of the encoding: with fewer than `k` positions no `k`-subset
exists, so the function is `0`. -/
theorem kDistinctness_eq_false_of_lt {k n q : ℕ} (h : n < k) (x : Fin n → Fin q) :
    kDistinctness k n q x = false := by
  simp only [kDistinctness, decide_eq_false_iff_not]
  rintro ⟨S, hS, a, _⟩
  have hcard : S.card ≤ n := by
    simpa using Finset.card_le_univ S
  omega

/-- On a `k`-fold repeated value the k-distinctness function evaluates to `1`
(when `k ≤ n`), so the encoding is not constantly zero. -/
theorem kDistinctness_repeat {k n q : ℕ} [NeZero q] (hk : k ≤ n) :
    ∃ x : Fin n → Fin q, kDistinctness k n q x = true := by
  obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
    (by simpa using hk)
  refine ⟨fun _ => 0, ?_⟩
  simp only [kDistinctness, decide_eq_true_eq]
  exact ⟨S, hS, 0, fun i _ => rfl⟩

end Qatlib.Papers.LearnGraphDis12.MainResults.QueryCost
