/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdiabNoSign20.MainResults.SourceModel
public import Mathlib.Data.Fintype.Card

@[expose] public section

/-!
# AdiabNoSign20 — reach-hardness over genuine query traces

Source: M. B. Hastings, *The Power of Adiabatic Quantum Computation with No
Sign Problem*, arXiv:2005.03791v1, Section 6 (p. 16).

Section 6 defines `(p, q)`-hardness to reach a vertex set `S` from a start
vertex as follows: no classical algorithm, starting from the start vertex,
can reach `S` with at most `q` queries with probability greater than `p`,
where "reach" means that at some point the algorithm queries a vertex in `S`.

The legacy predicate `Qatlib.Papers.AdiabNoSign20.MainResults.SourceModel.ReachHard`
records the probability as an unconstrained field `reachProb` of
`Qatlib.Papers.AdiabNoSign20.MainResults.SourceModel.GraphQueryAlgorithm`, so
it is refuted for every parameter by a record choosing `reachProb` above the
bound (`reachHard_never`).  This module replaces the free field by a query
trace:

* `IsQueryTrace` — the paper's exploration discipline: the first query is the
  start vertex and every later query is a vertex that is the start vertex or a
  neighbour of a vertex queried earlier;
* `GenuineGraphAlgorithm` — a deterministic algorithm indexed by a finite set
  of random seeds, whose trace on each graph and start vertex is a query trace
  and whose length is bounded by its query count;
* `reachProbability` — the fraction of seeds whose trace queries a vertex of
  `S`, a genuine probability computed from the trace;
* `ReachHardGenuine` — the `(p, q)`-hardness statement of Section 6 over this
  model.

`reachHard_genuine` is the restatement of the legacy contract, and
`reachHardGenuine_zero_queryCount` / `not_reachHardGenuine_of_mem` show that
the repaired predicate is satisfiable and has the expected truth value at the
start vertex, so the repair is not vacuous.  The reach probabilities of
Lemma 6 are not formalised here, so Lemma 5, Lemma 6 and Lemma 7 remain
separate obligations of this paper.
-/

set_option autoImplicit false

namespace Qatlib.Papers.AdiabNoSign20.MainResults.GenuineReachHardness

open Qatlib.Papers.AdiabNoSign20.MainResults.SourceModel

/-- The exploration discipline of the modified query model (Section 6, p. 16):
the algorithm starts from the start vertex, and after querying a vertex it may
next query only the start vertex or a neighbour of a vertex queried earlier.
The list records the queried vertices in order. -/
def IsQueryTrace {V : Type} (G : SimpleGraph V) (start : V) (l : List V) : Prop :=
  ∀ i : Fin l.length,
    l.get i = start ∨ ∃ j : Fin l.length, j < i ∧ G.Adj (l.get j) (l.get i)

/-- A classical algorithm in the modified query model of Section 6, presented
by its query traces.  `R` is the finite set of random seeds; for a seed `r`, a
graph `G` and a start vertex `start`, `trace r G start` is the list of vertices
queried in order.  The trace is subject to the exploration discipline
`IsQueryTrace` and its length is bounded by `queryCount`. -/
structure GenuineGraphAlgorithm (V : Type) where
  /-- the finite set of random seeds -/
  R : Type
  /-- finiteness of the seed set -/
  [fintypeR : Fintype R]
  /-- nonemptiness of the seed set -/
  [nonemptyR : Nonempty R]
  /-- number of queries made by the algorithm -/
  queryCount : ℕ
  /-- the vertices queried on seed `r` in graph `G` from `start`, in order -/
  trace : R → SimpleGraph V → V → List V
  /-- the trace never exceeds the query budget -/
  length_trace_le : ∀ (r : R) (G : SimpleGraph V) (start : V),
    (trace r G start).length ≤ queryCount
  /-- the trace follows the exploration discipline of the modified query
  model, starting from the start vertex -/
  valid_trace : ∀ (r : R) (G : SimpleGraph V) (start : V),
    IsQueryTrace G start (trace r G start)

namespace GenuineGraphAlgorithm

variable {V : Type} (alg : GenuineGraphAlgorithm V)

/-- The probability, over the algorithm's random seeds, that the query trace
on `G` from `start` queries at least one vertex of `S`.  This is the paper's
notion of "reaching" `S` (Section 6, p. 16), computed from the trace rather
than taken as a free parameter. -/
noncomputable def reachProbability (G : SimpleGraph V) (start : V) (S : Set V) : ℝ := by
  classical
  letI := alg.fintypeR
  exact ((Finset.univ.filter
      (fun r : alg.R => ∃ v ∈ alg.trace r G start, v ∈ S)).card : ℝ) /
    (Fintype.card alg.R : ℝ)

/-- The reach probability is nonnegative. -/
theorem reachProbability_nonneg (G : SimpleGraph V) (start : V) (S : Set V) :
    0 ≤ alg.reachProbability G start S := by
  classical
  let := alg.fintypeR
  let := alg.nonemptyR
  have hcard : (0 : ℝ) < (Fintype.card alg.R : ℝ) := by
    exact_mod_cast Fintype.card_pos
  exact div_nonneg (Nat.cast_nonneg _) hcard.le

/-- The reach probability is at most one. -/
theorem reachProbability_le_one (G : SimpleGraph V) (start : V) (S : Set V) :
    alg.reachProbability G start S ≤ 1 := by
  classical
  let := alg.fintypeR
  let := alg.nonemptyR
  have hcard : (0 : ℝ) < (Fintype.card alg.R : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hle : ((Finset.univ.filter
        (fun r : alg.R => ∃ v ∈ alg.trace r G start, v ∈ S)).card : ℝ) ≤
      (Fintype.card alg.R : ℝ) := by
    exact_mod_cast Finset.card_filter_le _ _
  exact div_le_one_of_le₀ hle hcard.le

/-- An algorithm with no queries never reaches any vertex set: its trace is
empty on every graph. -/
theorem reachProbability_eq_zero_of_queryCount_eq_zero
    (h : alg.queryCount = 0) (G : SimpleGraph V) (start : V) (S : Set V) :
    alg.reachProbability G start S = 0 := by
  classical
  let := alg.fintypeR
  have hnil : ∀ r : alg.R, alg.trace r G start = [] := by
    intro r
    have hlen := alg.length_trace_le r G start
    rw [h] at hlen
    exact List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
  have hempty : (Finset.univ.filter
      (fun r : alg.R => ∃ v ∈ alg.trace r G start, v ∈ S)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro r _
    simp [hnil r]
  rw [reachProbability, hempty]
  simp

/-- If every random seed reaches `S`, the reach probability is one. -/
theorem reachProbability_eq_one_of_forall_reaches
    (G : SimpleGraph V) (start : V) (S : Set V)
    (h : ∀ r : alg.R, ∃ v ∈ alg.trace r G start, v ∈ S) :
    alg.reachProbability G start S = 1 := by
  classical
  let := alg.fintypeR
  let := alg.nonemptyR
  have hfilter : (Finset.univ.filter
      (fun r : alg.R => ∃ v ∈ alg.trace r G start, v ∈ S)) = Finset.univ :=
    Finset.filter_true_of_mem fun r _ => h r
  rw [reachProbability, hfilter, Finset.card_univ]
  have hcard : (Fintype.card alg.R : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  exact div_self hcard

end GenuineGraphAlgorithm

/-- **(p, q)-hardness to reach a vertex set** (Section 6, p. 16) over genuine
query traces: every algorithm with at most `q` queries reaches `S` from
`start` in `G` with probability at most `p`. -/
def ReachHardGenuine {V : Type} (G : SimpleGraph V) (start : V) (S : Set V)
    (p : ℝ) (q : ℕ) : Prop :=
  ∀ alg : GenuineGraphAlgorithm V, alg.queryCount ≤ q →
    alg.reachProbability G start S ≤ p

/-- **Restatement of the Section 6 hardness contract over genuine traces.**
If every genuine algorithm with at most `q` queries has reach probability at
most `p`, then the graph is `(p, q)`-hard to reach.  This is the repaired form
of the legacy `ReachHard`, whose probability field was unconstrained. -/
theorem reachHard_genuine {V : Type} [Fintype V] (G : SimpleGraph V) (start : V)
    (Δ : Set V) (p : ℝ) (q : ℕ)
    (h : ∀ alg : GenuineGraphAlgorithm V, alg.queryCount ≤ q →
      alg.reachProbability G start Δ ≤ p) :
    ReachHardGenuine G start Δ p q :=
  h

/-- `(p, q)`-hardness for a larger query budget implies it for a smaller one:
a larger budget makes the statement stronger. -/
theorem reachHardGenuine_mono_query {V : Type} {G : SimpleGraph V} {start : V}
    {S : Set V} {p : ℝ} {q q' : ℕ} (hq : q ≤ q')
    (h : ReachHardGenuine G start S p q') : ReachHardGenuine G start S p q :=
  fun alg hle => h alg (le_trans hle hq)

/-- `(p, q)`-hardness is monotone in the probability bound. -/
theorem reachHardGenuine_mono_bound {V : Type} {G : SimpleGraph V} {start : V}
    {S : Set V} {p p' : ℝ} {q : ℕ} (hp : p ≤ p')
    (h : ReachHardGenuine G start S p q) : ReachHardGenuine G start S p' q :=
  fun alg hle => le_trans (h alg hle) hp

/-- With a zero query budget no vertex can be reached, so the graph is
`(0, 0)`-hard to reach every vertex set.  In particular the repaired predicate
is satisfiable, unlike the legacy `ReachHard`. -/
theorem reachHardGenuine_zero_queryCount {V : Type} (G : SimpleGraph V) (start : V)
    (S : Set V) : ReachHardGenuine G start S 0 0 := by
  intro alg hq
  rw [alg.reachProbability_eq_zero_of_queryCount_eq_zero (Nat.le_zero.mp hq) G start S]

/-- The algorithm that queries only its start vertex and then stops. -/
def queryStartAlgorithm (V : Type) : GenuineGraphAlgorithm V where
  R := PUnit
  fintypeR := inferInstanceAs (Fintype PUnit)
  nonemptyR := inferInstanceAs (Nonempty PUnit)
  queryCount := 1
  trace := fun _ _ start => [start]
  length_trace_le := by
    intro r G start
    simp
  valid_trace := by
    intro r G start i
    left
    fin_cases i
    simp

/-- The start-querying algorithm makes exactly one query. -/
@[simp] theorem queryStartAlgorithm_queryCount (V : Type) :
    (queryStartAlgorithm V).queryCount = 1 := rfl

/-- The start-querying algorithm reaches the start vertex with probability
one. -/
theorem queryStartAlgorithm_reachProbability {V : Type} (G : SimpleGraph V)
    (start : V) {S : Set V} (hS : start ∈ S) :
    (queryStartAlgorithm V).reachProbability G start S = 1 := by
  refine GenuineGraphAlgorithm.reachProbability_eq_one_of_forall_reaches
    (alg := queryStartAlgorithm V) G start S ?_
  intro _
  exact ⟨start, by simp [queryStartAlgorithm], hS⟩

/-- If the start vertex belongs to `S`, then `(0, q)`-hardness fails for every
positive query budget: the algorithm that queries the start vertex reaches `S`
with probability one.  This is the sanity check that the repaired predicate
does not hold vacuously for the wrong reason. -/
theorem not_reachHardGenuine_of_mem {V : Type} {G : SimpleGraph V} {start : V}
    {S : Set V} (hS : start ∈ S) {q : ℕ} (hq : 1 ≤ q) :
    ¬ ReachHardGenuine G start S 0 q := by
  intro h
  have hq' : (queryStartAlgorithm V).queryCount ≤ q := by
    rw [queryStartAlgorithm_queryCount V]
    exact hq
  have hle := h (queryStartAlgorithm V) hq'
  rw [queryStartAlgorithm_reachProbability (V := V) G start hS] at hle
  norm_num at hle

end Qatlib.Papers.AdiabNoSign20.MainResults.GenuineReachHardness
