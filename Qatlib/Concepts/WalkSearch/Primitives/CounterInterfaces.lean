/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.SearchPreflight

/-!
# Interruptible edge-search interfaces

Defines charged execution prefixes for edge-based triangle search and a reservation from upper
bounds on pair and graph-edge counts. `InterruptibleEdgeTriSearch` requires prefixes to respect
their budget, completed prefixes to agree with the base search, and fitting base executions to
complete; see [Ambainis2005] for search background.

## Main statements

* `InterruptibleEdgeTriSearch`: An edge-triangle search equipped with budgeted prefixes that
  respect query budgets, agree with the base output and cost on completion, and complete
  whenever the base cost fits the budget.
* `edgeSearch_cost_le_reservation`: If `eBound` bounds the candidate-pair count and `mBound`
  bounds the graph edges among those pairs, the edge-search cost is at most
  `edgeSearchReservation ets n eBound mBound`.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical

/-- An interrupted or completed search prefix, recording a query count and, on completion, an
optional output. -/
inductive EdgeSearchPrefix (α : Type) where
  | stopped : ℕ → EdgeSearchPrefix α
  | finished : Option α → ℕ → EdgeSearchPrefix α

/-- The query count recorded by an interrupted or completed edge-search prefix. -/
def EdgeSearchPrefix.queries {α : Type} : EdgeSearchPrefix α → ℕ
  | .stopped q=>q
  | .finished _ q=>q

/-- An edge-triangle search equipped with budgeted prefixes that respect query budgets, agree
with the base output and cost on completion, and complete whenever the base cost fits the
budget. -/
structure InterruptibleEdgeTriSearch where
  base : EdgeTriSearch
  runPrefix : {n : ℕ} → (G : UGraph n) → (E : Finset (Fin n×Fin n)) → (floor budget : ℕ) →
    base.seed → EdgeSearchPrefix (Fin n×Fin n×Fin n)
  prefix_charges : ∀ {n} (G : UGraph n) (E : Finset (Fin n×Fin n)) (floor budget : ℕ) (ρ : base.seed),
    (runPrefix G E floor budget ρ).queries≤ budget
  completed_agrees : ∀ {n} (G : UGraph n) (E : Finset (Fin n×Fin n)) (floor budget : ℕ) (ρ : base.seed)
    (out : Option (Fin n×Fin n×Fin n)) (q : ℕ), runPrefix G E floor budget ρ=.finished out q →
      base.run G E floor ρ=out ∧ base.cost G E floor ρ=q
  fitting_completes : ∀ {n} (G : UGraph n) (E : Finset (Fin n×Fin n)) (floor budget : ℕ) (ρ : base.seed),
    base.cost G E floor ρ≤ budget → runPrefix G E floor budget ρ=.finished (base.run G E floor ρ) (base.cost G E floor ρ)

/-- The edge-search query reservation obtained from the supplied pair-count and graph-edge-count
upper bounds using the search primitive's logarithmic and square-root cost expression. -/
def edgeSearchReservation (ets : EdgeTriSearch) (n eBound mBound : ℕ) : ℕ :=
  ets.κ*(Nat.log 2 (eBound+n*mBound+1)+2)*(Nat.sqrt eBound+Nat.sqrt (n*mBound)+1)

/-- A completed interruptible search returning `(a, b, c)` yields three distinct vertices with
all triangle edges in `G.edges` and base pair `(a, b)` in `E`. -/
theorem interruptibleEdgeSearch_sound (ets : InterruptibleEdgeTriSearch) {n : ℕ} (G : UGraph n)
    (E : Finset (Fin n×Fin n)) (floor budget : ℕ) (ρ : ets.base.seed) (a b c : Fin n) (q : ℕ)
    (h : ets.runPrefix G E floor budget ρ=.finished (some (a,b,c)) q) :
    a≠b ∧ b≠c ∧ a≠c ∧ (a,b)∈E ∧ (a,b)∈G.edges ∧ (a,c)∈G.edges ∧ (b,c)∈G.edges :=
  ets.base.sound G E floor ρ (ets.completed_agrees G E floor budget ρ _ q h).1

/-- If `eBound` bounds the candidate-pair count and `mBound` bounds the graph edges among those
pairs, the edge-search cost is at most `edgeSearchReservation ets n eBound mBound`. -/
theorem edgeSearch_cost_le_reservation (ets : EdgeTriSearch) {n : ℕ} (G : UGraph n)
    (E : Finset (Fin n×Fin n)) (floor : ℕ) (ρ : ets.seed) (eBound mBound : ℕ)
    (he : E.card≤ eBound) (hm : (E∩G.edges).card≤ mBound) :
    ets.cost G E floor ρ≤ edgeSearchReservation ets n eBound mBound := by
  apply (ets.charges G E floor ρ).trans
  unfold edgeSearchReservation
  gcongr
end Qatlib.Concepts.WalkSearch.Primitives
