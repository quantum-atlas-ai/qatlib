/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Tactic.NormNum
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound

set_option backward.isDefEq.respectTransparency false

/-!
# LowerBounds — Lemma 3 (query lower bounds in the adjacency-array model)

Cade--Montanaro--Belovs, fixed source arXiv:1610.00581v1 (3 October 2016),
§7.5, Lemma 3, p. 18.

Both bipartiteness testing and cycle detection require `Ω(n)` queries to the
adjacency array, even when the graph is promised to have at most `n` edges.

Paper proof key steps (pp. 18--19): both properties are preserved by the same
"edge-counting" reduction of §7.5; the input is a graph formed by `n` disjoint
"gadget" components, each encoding one bit of an `n`-bit string; a cycle exists
iff the parity of the string is odd (respectively the graph is non-bipartite iff
the parity is odd); therefore any bounded-error algorithm distinguishing the two
cases decides parity of `n` bits, and the parity lower bound (Beals et al.,
Lemma 6.3 / Proposition 6.4: `n/2` queries) applies.

In this development the parity lower bound is available in the pinned Frozen
release and is reused verbatim (see `parity_query_lower_bound_bridge`); the
reduction from cycle detection / bipartiteness to parity is formalized only at
the level of the query-complexity interface here.

Boundary: the statements record the lower bound on the number of adjacency-array
queries of a bounded-error solver; the gadget construction is not formalized.
-/

set_option autoImplicit false

namespace Qatlib.Papers.TimeSpaceDet16.MainResults.LowerBounds

open SimpleGraph
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery

/-- `G` contains no cycle (closed-walk formulation). -/
def CycleFree {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (u : V) (p : G.Walk u u), p.length = 0

/-- `G` contains a cycle. -/
def HasCycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (u : V) (p : G.Walk u u), 0 < p.length

/-- `G` is bipartite, given by an explicit two-colouring. -/
def Bipartite {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ col : V → Bool, ∀ u v : V, G.Adj u v → col u ≠ col v

/-- A bounded-error solver in the adjacency-array model: success probability and
number of queries to the adjacency array. -/
structure ArrayModelSolver (n : ℕ) where
  /-- Acceptance probability on input `G`. -/
  acceptProb : SimpleGraph (Fin n) → ℝ
  acceptProb_nonneg : ∀ G, 0 ≤ acceptProb G
  acceptProb_le_one : ∀ G, acceptProb G ≤ 1
  /-- Number of queries to the adjacency array. -/
  queryCount : ℕ

/-- The solver decides cycle detection with two-sided error at most `1/3`. -/
def SolvesCycleDetection {n : ℕ} (Q : ArrayModelSolver n) : Prop :=
  (∀ G : SimpleGraph (Fin n), HasCycle G → 2 / 3 ≤ Q.acceptProb G) ∧
    (∀ G : SimpleGraph (Fin n), CycleFree G → 2 / 3 ≤ 1 - Q.acceptProb G)

/-- The solver decides bipartiteness with two-sided error at most `1/3`. -/
def SolvesBipartiteness {n : ℕ} (Q : ArrayModelSolver n) : Prop :=
  (∀ G : SimpleGraph (Fin n), Bipartite G → 2 / 3 ≤ Q.acceptProb G) ∧
    (∀ G : SimpleGraph (Fin n), ¬Bipartite G → 2 / 3 ≤ 1 - Q.acceptProb G)

/-- A non-trivial closed walk witnesses non-cyclessness failure. -/
theorem not_cycleFree_of_nontrivial_closed_walk {V : Type*} {G : SimpleGraph V} {u : V}
    {p : G.Walk u u} (hp : 0 < p.length) : ¬ CycleFree G := by
  intro h
  have h0 := h u p
  omega

/-- The missing gadget reduction of Lemma 3, recorded as an explicit
hypothesis: `C` is a bounded-error parity decider on `I`-bit strings with
`|I| = n`, and its query count fits in the graph solver's budget.

Constructing `C` from a cycle-detection solver `Q` (the `n`-gadget family of
§7.5) and proving `QueryCount C ≤ Q.queryCount` is the documented gap; this
predicate states exactly what the construction has to provide. -/
def ParityReduction {n : ℕ} (Q : ArrayModelSolver n)
    (I W : Type) [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace I W)) (ψ : QState (PolynomialWorkspace I W))
    (E : Finset (PolynomialWorkspace I W)) : Prop :=
  Fintype.card I = n ∧ IsUnitaryCircuit C ∧ Normalized ψ ∧
    QueryCount C ≤ Q.queryCount ∧
    ∀ f : I → Bool,
      |MeasureProb (Run (TensorGate (BitOracleOn f) (1 : Matrix W W ℂ)) C ψ) E
        - (if (Finset.univ.filter (fun i => f i = true)).card % 2 = 1 then (1 : ℝ) else 0)|
        ≤ 1 / 3

/-- **Reused parity lower bound** (Beals--Buhrman--Cleve--Mosca--de Wolf, Lemma 6.3,
formalized in Frozen as
`QuantumAlgorithm.Concepts.QueryComplexity.DegreeMethod.parity_actual_bounded_error_query_lower_bound`).

Any circuit deciding parity of an `I`-bit string on the standard bit oracle with
error at most `1/3` makes at least `|I| / 2` queries.  This is the engine behind
Lemma 3 of the paper; it is restated in the paper-layer namespace so that the
paper's lower bounds point at a verifiable dependency. -/
theorem parity_query_lower_bound_bridge {I W : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace I W)) (ψ : QState (PolynomialWorkspace I W))
    (E : Finset (PolynomialWorkspace I W)) (hU : IsUnitaryCircuit C) (hN : Normalized ψ)
    (hyp : ∀ f : I → Bool,
      |MeasureProb (Run (TensorGate (BitOracleOn f) (1 : Matrix W W ℂ)) C ψ) E
        - (if (Finset.univ.filter (fun i => f i = true)).card % 2 = 1 then (1 : ℝ) else 0)|
        ≤ 1 / 3) :
    Fintype.card I ≤ 2 * QueryCount C :=
  Qatlib.Concepts.QueryComplexity.DegreeMethod.parity_actual_bounded_error_query_lower_bound
    C ψ E hU hN hyp

/-- **Lemma 3, cycle-detection half, conditional form**
(arXiv:1610.00581v1, §7.5, Lemma 3, p. 18).

If `Q` solves cycle detection with two-sided error at most `1/3` and the
Lemma 3 gadget reduction provides a bounded-error `n`-bit parity decider whose
circuit fits in `Q`'s query budget, then `Q` makes at least `n/2` queries:
`n ≤ 2 · Q.queryCount`.

The gadget family and the adjacency-array-to-bit-oracle simulation are not
formalized; `ParityReduction` is their explicit interface. -/
theorem lemma3_cycle_detection_query_lower_bound (n : ℕ) (Q : ArrayModelSolver n)
    (_hQ : SolvesCycleDetection Q)
    {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace I W)) (ψ : QState (PolynomialWorkspace I W))
    (E : Finset (PolynomialWorkspace I W)) (hred : ParityReduction Q I W C ψ E) :
    n ≤ 2 * Q.queryCount := by
  obtain ⟨hcard, hU, hN, hQq, hyp⟩ := hred
  have h := parity_query_lower_bound_bridge C ψ E hU hN hyp
  rw [hcard] at h
  omega

/-- **Lemma 3, bipartiteness half, conditional form**
(arXiv:1610.00581v1, §7.5, Lemma 3, p. 18).

Same conditional statement as the cycle-detection half: a bipartiteness solver
with two-sided error at most `1/3`, together with the parity reduction of
Lemma 3, needs at least `n/2` adjacency-array queries. -/
theorem lemma3_bipartiteness_query_lower_bound (n : ℕ) (Q : ArrayModelSolver n)
    (_hQ : SolvesBipartiteness Q)
    {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace I W)) (ψ : QState (PolynomialWorkspace I W))
    (E : Finset (PolynomialWorkspace I W)) (hred : ParityReduction Q I W C ψ E) :
    n ≤ 2 * Q.queryCount := by
  obtain ⟨hcard, hU, hN, hQq, hyp⟩ := hred
  have h := parity_query_lower_bound_bridge C ψ E hU hN hyp
  rw [hcard] at h
  omega

/-- **Lemma 3** (arXiv:1610.00581v1, §7.5, Lemma 3, p. 18), combined
conditional form. -/
theorem lemma3_query_lower_bounds (n : ℕ) (Q : ArrayModelSolver n)
    {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (C : Circuit (PolynomialWorkspace I W)) (ψ : QState (PolynomialWorkspace I W))
    (E : Finset (PolynomialWorkspace I W)) (hred : ParityReduction Q I W C ψ E) :
    (SolvesCycleDetection Q → n ≤ 2 * Q.queryCount) ∧
      (SolvesBipartiteness Q → n ≤ 2 * Q.queryCount) :=
  ⟨fun h => lemma3_cycle_detection_query_lower_bound n Q h C ψ E hred,
    fun h => lemma3_bipartiteness_query_lower_bound n Q h C ψ E hred⟩

end Qatlib.Papers.TimeSpaceDet16.MainResults.LowerBounds
