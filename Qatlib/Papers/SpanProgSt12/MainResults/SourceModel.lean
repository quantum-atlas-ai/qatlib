/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.Complexity
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Data.Real.Sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# SpanProgSt12 — shared paper vocabulary

Fixed paper: Belovs & Reichardt, *Span programs and quantum algorithms for
st-connectivity and claw detection*, arXiv:1203.2603v1 (12 Mar 2012),
PDF at `assets/1203.2603.pdf`.

This file fixes the graph vocabulary and the query-algorithm interfaces used by
every active Claim of the paper.  The model reuse is deliberate:

* `SimpleGraph (Fin n)` is the finite simple graph of the paper;
* `QuantumAlgorithm.Concepts.QueryComplexity.DegreeMethod.FixedSpaceQueryUpperBound`
  is the paper's bounded-error, fixed-space quantum query algorithm (Theorem 2's
  consumer side), with the addressed adjacency-matrix oracle built here;
* `BoolQueryTree` is the finite randomized query tree model used for the
  randomized lower bound of Proposition 4;
* `Circuit.GateCount`/`QueryCount` are the sequential-model time/query ledger used
  to state Theorem 9.

Boundary: this file only fixes definitions and elementary lemmas.  The paper's
algorithmic theorems live in the sibling directories, one claim per file.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Foundations.QueryWordCore.Circuit
open scoped Classical
open Qatlib.Foundations.PureStateMath
open Matrix
open scoped BigOperators ENNReal

namespace Qatlib.Papers.SpanProgSt12.MainResults.SourceModel

/-! ## Addressed adjacency-matrix query -/

/-- Register of the adjacency-matrix oracle: oriented edge `(u,v)`, the data
bit holding the adjacency entry, and the algorithm's output bit. -/
abbrev EdgeReg (n : ℕ) : Type := Fin n × Fin n × Bool × Bool

/-- The register flip implemented by one query to the adjacency matrix:
the data bit is XORed with `G.Adj u v`; everything else is untouched. -/
def edgeQueryFlip {n : ℕ} (G : SimpleGraph (Fin n)) (p : EdgeReg n) : EdgeReg n := by
  classical
  exact (p.1, p.2.1, (if G.Adj p.1 p.2.1 then !p.2.2.1 else p.2.2.1), p.2.2.2)

/-- The adjacency-matrix query unitary as a permutation matrix. -/
def edgeQueryOracle {n : ℕ} (G : SimpleGraph (Fin n)) :
    Matrix (EdgeReg n) (EdgeReg n) ℂ :=
  fun p q => if q = edgeQueryFlip G p then 1 else 0

/-- The edge query is an involution: querying the same entry twice restores it. -/
theorem edgeQueryFlip_involutive {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∀ p : EdgeReg n, edgeQueryFlip G (edgeQueryFlip G p) = p := by
  intro p
  by_cases h : G.Adj p.1 p.2.1 <;> simp [edgeQueryFlip, h, Bool.not_not]

/-- A permutation matrix induced by an involution is unitary. -/
theorem involutivePermutation_mem_unitary {I : Type} [Fintype I] [DecidableEq I]
    (σ : I → I) (hσ : ∀ x, σ (σ x) = x) :
    (Matrix.of fun i j => if j = σ i then (1 : ℂ) else 0) ∈
      Matrix.unitaryGroup I ℂ := by
  have hinj : Function.Injective σ := by
    intro a b hab
    have h := congrArg σ hab
    rwa [hσ a, hσ b] at h
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  ext i j
  rw [Matrix.mul_apply]
  have happ : ∀ a b : I,
      (Matrix.of fun i j => if j = σ i then (1 : ℂ) else 0) a b =
        if b = σ a then (1 : ℂ) else 0 := fun a b => rfl
  have hconj : ∀ a b : I,
      ((Matrix.of fun i j => if j = σ i then (1 : ℂ) else 0)ᴴ) a b =
        if a = σ b then (1 : ℂ) else 0 := by
    intro a b
    rw [Matrix.conjTranspose_apply, happ]
    split <;> simp
  simp only [happ, hconj]
  rw [Finset.sum_eq_single (σ i)]
  · simp only [if_true, one_mul]
    rw [Matrix.one_apply]
    by_cases h : i = j
    · subst h; simp
    · have hne : ¬ (σ i = σ j) := fun hh => h (hinj hh)
      simp [h, hne]
  · intro k _ hk
    simp [hk]
  · intro h
    simp at h

/-- The addressed adjacency-matrix query is a unitary. -/
theorem edgeQueryOracle_mem_unitary {n : ℕ} (G : SimpleGraph (Fin n)) :
    edgeQueryOracle G ∈ Matrix.unitaryGroup (EdgeReg n) ℂ := by
  have h := involutivePermutation_mem_unitary (edgeQueryFlip G) (edgeQueryFlip_involutive G)
  exact h

/-- The accepting measurement: output bit `b`. -/
def acceptFinset {n : ℕ} (b : Bool) : Finset (EdgeReg n) :=
  Finset.univ.filter (fun p => p.2.2.2 = b)

/-- Measurement family induced by a decision predicate: the accepted set is the
states whose output bit reads `true` on yes-instances and `false` otherwise. -/
def acceptByProp {n : ℕ} {F : Type} (Ω : F → Prop) : F → Finset (EdgeReg n) := by
  classical
  exact fun f => acceptFinset (if Ω f then true else false)

/-- A decision problem on `n`-vertex graphs, given by addressed adjacency-matrix
query access, is decided with `k` queries and error `ε`. -/
def GraphQuerySolvable {n : ℕ} (F : Type) (toGraph : F → SimpleGraph (Fin n))
    (Ω : F → Prop) (ε : ℝ) (k : ℕ) : Prop :=
  FixedSpaceQueryUpperBound (fun f => edgeQueryOracle (toGraph f)) (acceptByProp Ω) ε k

/-! ## Time/space ledger (Theorem 9) -/

/-- `O ⊗ 1_W`: the oracle extended by an untouched workspace register. -/
def liftOracle {I W : Type} [DecidableEq W] (O : Matrix I I ℂ) :
    Matrix (I × W) (I × W) ℂ := by
  classical
  exact fun p q => if p.2 = q.2 then O p.1 q.1 else 0

/-- A time- and space-bounded decision algorithm for a graph problem: the same
bounded-error semantics, plus an explicit workspace register and a fixed-gate
count budget.  This is the paper's Õ-time/O(log n)-space ledger, with the
sequential `GateCount` used as the time proxy as documented in
`Foundations/ReferenceError/MixturePaths/Circuit`. -/
def TimedSpaceGraphAlgorithm {n : ℕ} (F : Type) (toGraph : F → SimpleGraph (Fin n))
    (Ω : F → Prop) (ε : ℝ) (space time : ℝ) (qk : ℕ) : Prop :=
  (0 ≤ ε ∧ ε < 1) ∧
    (∀ f, edgeQueryOracle (toGraph f) ∈ Matrix.unitaryGroup (EdgeReg n) ℂ) ∧
    ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W),
      Fintype.card W ≤ 2 ^ ⌈space⌉₊ ∧
      ∃ (C : Circuit (EdgeReg n × W)) (ψ₀ : QState (EdgeReg n × W)),
        IsUnitaryCircuit C ∧ Normalized ψ₀ ∧ QueryCount C ≤ qk ∧
          GateCount C ≤ ⌈time⌉₊ ∧
          ∀ f, 1 - ε ≤
            MeasureProb (Run (liftOracle (edgeQueryOracle (toGraph f))) C ψ₀)
              ((acceptByProp Ω f).product Finset.univ)

/-! ## Randomized query model (Proposition 4) -/

/-- The adjacency word of a graph, queried entry by entry. -/
def adjacencyWord {n : ℕ} (G : SimpleGraph (Fin n)) : Fin n × Fin n → Bool := by
  classical
  exact fun p => decide (G.Adj p.1 p.2)

/-- A randomized finite tree solves the decision problem with error `ε`. -/
def RandomizedSolves {F Query : Type} (O : F → Query → Bool) (Ω : F → Prop)
    (program : PMF (BoolQueryTree Query Bool)) (ε : ℝ≥0∞) : Prop := by
  classical
  exact ∀ f, 1 - ε ≤
    BoolQueryTree.SuccessProb program (O f) (fun b => if Ω f then b = true else b = false)

/-- Randomized query lower bound: every finite randomized tree with worst-case
budget `k` fails to solve the problem with error `ε`. -/
def RandomizedQueryLowerBound {F Query : Type} (O : F → Query → Bool) (Ω : F → Prop)
    (ε : ℝ≥0∞) (k : ℕ) : Prop :=
  ∀ program : PMF (BoolQueryTree Query Bool),
    BoolQueryTree.BoundedQueries program k → ¬ RandomizedSolves O Ω program ε

/-! ## Graph containment (subgraph / minor) -/

/-- `G` contains a copy of `T` as a subgraph. -/
def ContainsAsSubgraph {n k : ℕ} (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin k)) : Prop :=
  ∃ φ : Fin k → Fin n, Function.Injective φ ∧ ∀ u v, T.Adj u v → G.Adj (φ u) (φ v)

/-- A minor model: nonempty, pairwise disjoint, connected branch sets realizing
every edge of `T` by a `G`-edge across the corresponding branch sets. -/
def IsMinorModel {n k : ℕ} (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin k))
    (br : Fin k → Set (Fin n)) : Prop :=
  (∀ i, (br i).Nonempty) ∧
    (∀ i j, i ≠ j → Disjoint (br i) (br j)) ∧
    (∀ i, (G.induce (br i)).Preconnected) ∧
    (∀ i j, T.Adj i j → ∃ u ∈ br i, ∃ v ∈ br j, G.Adj u v)

/-- `G` contains a copy of `T` as a minor, via a minor model. -/
def ContainsAsMinor {n k : ℕ} (G : SimpleGraph (Fin n)) (T : SimpleGraph (Fin k)) : Prop :=
  ∃ br : Fin k → Set (Fin n), IsMinorModel G T br

/-- A subgraph copy is a minor model with singleton branch sets. -/
theorem containsAsSubgraph_toMinor {n k : ℕ} {G : SimpleGraph (Fin n)}
    {T : SimpleGraph (Fin k)} (h : ContainsAsSubgraph G T) : ContainsAsMinor G T := by
  obtain ⟨φ, hφ, hadj⟩ := h
  refine ⟨fun i => {φ i}, ?_, ?_, ?_, ?_⟩
  · intro i; exact ⟨φ i, rfl⟩
  · intro i j hij
    rw [Set.disjoint_singleton_left, Set.mem_singleton_iff]
    intro h
    exact hij (hφ h)
  · intro i u v
    have hu : u.1 = φ i := Set.mem_singleton_iff.mp u.2
    have hv : v.1 = φ i := Set.mem_singleton_iff.mp v.2
    have huv : u = v := Subtype.ext (hu.trans hv.symm)
    subst huv
    exact ⟨SimpleGraph.Walk.nil⟩
  · intro i j hij
    exact ⟨φ i, rfl, φ j, rfl, hadj i j hij⟩

/-- The triangle `K₃`. -/
def TriangleGraph : SimpleGraph (Fin 3) := ⊤

/-- `G` contains a triangle as a subgraph. -/
def ContainsTriangle {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ContainsAsSubgraph G TriangleGraph

/-- A triangle subgraph is three pairwise adjacent distinct vertices. -/
theorem containsTriangle_iff {n : ℕ} (G : SimpleGraph (Fin n)) :
    ContainsTriangle G ↔
      ∃ a b c : Fin n, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj a c := by
  have hT01 : TriangleGraph.Adj (0 : Fin 3) 1 := by
    show (0 : Fin 3) ≠ 1
    decide
  have hT12 : TriangleGraph.Adj (1 : Fin 3) 2 := by
    show (1 : Fin 3) ≠ 2
    decide
  have hT02 : TriangleGraph.Adj (0 : Fin 3) 2 := by
    show (0 : Fin 3) ≠ 2
    decide
  constructor
  · rintro ⟨φ, hφ, hadj⟩
    exact ⟨φ 0, φ 1, φ 2, hφ.ne (by decide), hφ.ne (by decide), hφ.ne (by decide),
      hadj 0 1 hT01, hadj 1 2 hT12, hadj 0 2 hT02⟩
  · rintro ⟨a, b, c, hab, hbc, hac, eab, ebc, eac⟩
    let φ : Fin 3 → Fin n := fun i => if (i : ℕ) = 0 then a else if (i : ℕ) = 1 then b else c
    have hφ0 : φ 0 = a := by simp [φ]
    have hφ1 : φ 1 = b := by simp [φ]
    have hφ2 : φ 2 = c := by simp [φ]
    refine ⟨φ, ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · intro i j hadj
      fin_cases i <;> fin_cases j <;>
        simp_all [TriangleGraph, eab.symm, ebc.symm, eac.symm]

/-- Instance family of the subgraph/not-a-minor promise problem for a fixed `T`:
`G` contains `T` as a subgraph or does not contain `T` as a minor (Section 4). -/
abbrev SubgraphNotMinorInstance (n k : ℕ) (T : SimpleGraph (Fin k)) : Type :=
  {G : SimpleGraph (Fin n) // ContainsAsSubgraph G T ∨ ¬ ContainsAsMinor G T}

/-- Instance family of the triangle promise problem of Theorem 8. -/
abbrev TriangleNotMinorInstance (n : ℕ) : Type :=
  {G : SimpleGraph (Fin n) // ContainsTriangle G ∨ ¬ ContainsAsMinor G TriangleGraph}

/-! ## Structural predicates for the forbidden graphs `T` -/

/-- `T` is a subdivision of a star: a tree with at most one vertex of degree > 2. -/
def IsSubdividedStar {k : ℕ} (T : SimpleGraph (Fin k)) : Prop :=
  T.IsTree ∧ ∃ r : Fin k, ∀ v : Fin k, v ≠ r → T.degree v ≤ 2

/-- `T` is a path (isomorphic to `pathGraph m`). -/
def IsPathGraph {k : ℕ} (T : SimpleGraph (Fin k)) : Prop :=
  ∃ m : ℕ, Nonempty (T ≃g SimpleGraph.pathGraph m)

/-- `T` is a subdivision of a claw: a tree with exactly one degree-3 vertex and
all other degrees at most two. -/
def IsSubdividedClaw {k : ℕ} (T : SimpleGraph (Fin k)) : Prop :=
  T.IsTree ∧ ∃ r : Fin k, T.degree r = 3 ∧ ∀ v : Fin k, v ≠ r → T.degree v ≤ 2

/-- The graph `T` of Corollary 6: a path or a subdivision of a claw. -/
def IsPathOrSubdividedClaw {k : ℕ} (T : SimpleGraph (Fin k)) : Prop :=
  IsPathGraph T ∨ IsSubdividedClaw T

/-- The vertex support of `T`'s edges. -/
def StarSupport {k : ℕ} (T : SimpleGraph (Fin k)) : Set (Fin k) :=
  {v | ∃ w, T.Adj v w}

/-- A vertex-disjoint collection of subdivided stars (Theorem 7). -/
def IsDisjointStarCollection {k : ℕ} {ι : Type} (T : ι → SimpleGraph (Fin k)) : Prop :=
  (∀ i, IsSubdividedStar (T i)) ∧
    (∀ i j, i ≠ j → Disjoint (StarSupport (T i)) (StarSupport (T j)))

/-- A copy of a vertex-disjoint collection as a subgraph: embeddings on the
components with pairwise disjoint images. -/
def ContainsCollectionAsSubgraph {n k : ℕ} {ι : Type}
    (G : SimpleGraph (Fin n)) (T : ι → SimpleGraph (Fin k)) : Prop :=
  ∃ φ : ι → Fin k → Fin n,
    (∀ i, Function.Injective (φ i)) ∧
      (∀ i j, i ≠ j → Disjoint (Set.range (φ i)) (Set.range (φ j))) ∧
      (∀ i u v, (T i).Adj u v → G.Adj (φ i u) (φ i v))

/-- A copy of a vertex-disjoint collection as a minor: component-wise minor
models with pairwise disjoint branch-set unions. -/
def ContainsCollectionAsMinor {n k : ℕ} {ι : Type}
    (G : SimpleGraph (Fin n)) (T : ι → SimpleGraph (Fin k)) : Prop :=
  ∃ br : ι → Fin k → Set (Fin n),
    (∀ i, IsMinorModel G (T i) (br i)) ∧
      (∀ i j, i ≠ j → Disjoint (⋃ α, br i α) (⋃ α, br j α))

/-- A star with two subdivided legs: a tree with a hub of degree at least three,
all other degrees at most two, and exactly two non-leaf neighbours of the hub
(the two subdivided legs of Theorem 14; the remaining hub neighbours are the
unsubdivided legs). -/
def IsStarWithTwoSubdividedLegs {k : ℕ} (T : SimpleGraph (Fin k)) : Prop := by
  classical
  exact
    T.IsTree ∧ ∃ r : Fin k,
      3 ≤ T.degree r ∧
        (∀ v : Fin k, v ≠ r → T.degree v ≤ 2) ∧
        (Finset.univ.filter (fun v => T.Adj r v ∧ 2 ≤ T.degree v)).card = 2

/-- Instance family of Theorem 14: all `n`-vertex graphs, no promise. -/
abbrev TwoLegStarInstance (n : ℕ) : Type := SimpleGraph (Fin n)

/-! ## st-connectivity vocabulary (Theorem 3) -/

/-- The paper's promise: if `s` and `t` are connected, they are connected by a
path of length at most `d`. -/
def StConnPromise {n : ℕ} (d : ℕ) (G : SimpleGraph (Fin n)) (s t : Fin n) : Prop :=
  G.Reachable s t → ∃ w : G.Walk s t, w.length ≤ d

/-- The yes-instances of st-connectivity. -/
def StConnYes {n : ℕ} (s t : Fin n) (G : SimpleGraph (Fin n)) : Prop :=
  G.Reachable s t

/-- Instance family of st-connectivity under the path-length promise. -/
abbrev StConnInstance (n d : ℕ) (s t : Fin n) : Type :=
  {G : SimpleGraph (Fin n) // StConnPromise d G s t}

end Qatlib.Papers.SpanProgSt12.MainResults.SourceModel
