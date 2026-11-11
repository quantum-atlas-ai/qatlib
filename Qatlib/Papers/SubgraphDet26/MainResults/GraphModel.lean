/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude
import Qatlib.Foundations.QueryWordCore.Circuit
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Paper-local model for Gilani–Zhou, *Superlinear Quantum Query Lower Bounds for
Subgraph Detection*, fixed arXiv:2609.40263v1.

This file introduces the definitions used by the paper-layer statements only; it adds
nothing to the shared Foundations/Concepts layers.  It fixes:

* concrete finite simple graphs `FinGraph V` (adjacency matrix as a `Bool`-valued
  symmetric, loopless function), cliques, partite graphs, colourings, chromatic
  number, connectivity, graph homomorphisms, induced subgraphs and clique minors;
* the adjacency-matrix input `EdgeIndex n → Bool` and the detection/search functions
  `SubHFunction`, `CliqueFunction` (paper §2.2, Eq. (7) for graph collision);
* the bounded-error quantum query model on an arbitrary finite workspace, using the
  frozen `Circuit`, `QueryCount`, `Run`, `workspaceBitOracle`, `MeasureProb`;
* the certificate-search model of §2.3 / §3 (families of certificates and the
  success probability averaged over the Bernoulli product measure `µ_p`);
* the exponent sequences `γ`, `β`, `λ` and the matching-number quantities
  `m(K_r,h)`, `m(K_{r,r},h)` of Eq. (6) and Eq. (67).

No mathematical claim of the paper is asserted here.
-/

set_option autoImplicit false
noncomputable section
open Classical

namespace Qatlib.Papers.SubgraphDet26.MainResults

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Matrix

/-! ## Finite simple graphs and basic graph predicates -/

/-- A finite simple undirected graph presented by its adjacency `Bool` function.  The
type of vertices is an explicit parameter; finiteness is supplied by the caller's
`[Fintype V]` hypothesis when needed. -/
structure FinGraph (V : Type*) where
  adj : V → V → Bool
  symm : ∀ a b, adj a b = adj b a
  loopless : ∀ a, adj a a = false

/-- The complete graph `K_r` on `Fin r`. -/
def completeGraphOn (r : ℕ) : FinGraph (Fin r) where
  adj a b := if a = b then false else true
  symm a b := by by_cases h : a = b <;> simp [h, eq_comm]
  loopless a := by simp

/-- `s` is a clique of `G`: every two distinct vertices of `s` are adjacent. -/
def IsCliqueSet {V : Type*} (G : FinGraph V) (s : Finset V) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, a ≠ b → G.adj a b = true

/-- Number of `r`-cliques (vertex sets) of a graph on `Fin n`. -/
def cliqueCount {n : ℕ} (G : FinGraph (Fin n)) (r : ℕ) : ℕ :=
  (Finset.univ.filter (fun s : Finset (Fin n) => s.card = r ∧ IsCliqueSet G s)).card

/-- `G` contains a copy of `K_r`. -/
def ContainsCliqueOn {n : ℕ} (G : FinGraph (Fin n)) (r : ℕ) : Prop :=
  ∃ s : Finset (Fin n), s.card = r ∧ IsCliqueSet G s

/-- `G` is `r`-partite: it admits a proper colouring with `r` colours. -/
def IsPartite {V : Type*} (G : FinGraph V) (r : ℕ) : Prop :=
  ∃ col : V → Fin r, ∀ a b, G.adj a b = true → col a ≠ col b

/-- `G` is `c`-colourable. -/
def Colorable {V : Type*} [Fintype V] [DecidableEq V] (G : FinGraph V) (c : ℕ) : Prop :=
  ∃ col : V → Fin c, ∀ a b, G.adj a b = true → col a ≠ col b

/-- The chromatic number `χ(G)` (least number of colours; `0` only for the empty
graph). -/
def chromaticNumber {V : Type*} [Fintype V] [DecidableEq V] (G : FinGraph V) : ℕ :=
  sInf {c : ℕ | Colorable G c}

/-- `G` is connected: every two vertices are joined by a walk of edges. -/
def Connected {V : Type*} (G : FinGraph V) : Prop :=
  ∀ a b : V, Relation.ReflTransGen (fun x y => G.adj x y = true) a b

/-- `f` is a graph homomorphism `H → C` (edges map to edges; injectivity is not
required). -/
def IsHom {V W : Type*} (H : FinGraph V) (C : FinGraph W) (f : V → W) : Prop :=
  ∀ a b, H.adj a b = true → C.adj (f a) (f b) = true

/-- `C` is an induced subgraph copy of `H` through the injection `ι`. -/
def IsInducedSubgraph {V W : Type*} (C : FinGraph W) (H : FinGraph V) (ι : W → V) : Prop :=
  Function.Injective ι ∧ ∀ a b, C.adj a b = true ↔ H.adj (ι a) (ι b) = true

/-- `G` contains `K_r` as a minor: there are `r` pairwise disjoint nonempty connected
branch sets with at least one edge between every two of them. -/
def HasCliqueMinor {V : Type*} [Fintype V] [DecidableEq V] (G : FinGraph V) (r : ℕ) : Prop :=
  ∃ B : Fin r → Finset V,
    (∀ i, (B i).Nonempty) ∧
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
    (∀ i, ∀ a ∈ B i, ∀ b ∈ B i,
      Relation.ReflTransGen (fun x y => G.adj x y = true ∧ x ∈ B i ∧ y ∈ B i) a b) ∧
    (∀ i j, i ≠ j → ∃ a ∈ B i, ∃ b ∈ B j, G.adj a b = true)

/-- Unique `K_ℓ`-extension property: every copy of `K_ℓ` in `G` lies in at most one
copy of `K_r`. -/
def UniqueExtension {n : ℕ} (G : FinGraph (Fin n)) (ℓ r : ℕ) : Prop :=
  ∀ s : Finset (Fin n), s.card = ℓ → IsCliqueSet G s →
    ∀ t : Finset (Fin n), t.card = r → IsCliqueSet G t → s ⊆ t →
    ∀ t' : Finset (Fin n), t'.card = r → IsCliqueSet G t' → s ⊆ t' → t' = t

/-! ## Adjacency-matrix inputs, detection and graph collision (paper §2.2) -/

/-- The coordinate set of the adjacency matrix of a graph on `n` vertices: ordered
pairs `u < v`, one coordinate per undirected edge. -/
abbrev EdgeIndex (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- Adjacency read off an edge-bit string; `false` on loops `u = v`. -/
def hasEdgeFromBits {n : ℕ} (x : EdgeIndex n → Bool) (u v : Fin n) : Bool :=
  if h : u < v then x ⟨(u, v), h⟩ else if h' : v < u then x ⟨(v, u), h'⟩ else false

/-- `x` contains a copy of the labelled pattern `H` (non-induced embedding). -/
def ContainsCopy {m n : ℕ} (x : EdgeIndex n → Bool) (H : FinGraph (Fin m)) : Prop :=
  ∃ f : Fin m → Fin n, Function.Injective f ∧
    ∀ a b, H.adj a b = true → hasEdgeFromBits x (f a) (f b) = true

/-- The subgraph-detection decision function `Sub_H(x) = 1{H ⊆ G_x}` (paper §2.2). -/
def SubHFunction {m : ℕ} (H : FinGraph (Fin m)) (n : ℕ) :
    (EdgeIndex n → Bool) → Bool :=
  fun x => if ContainsCopy x H then true else false

/-- `Clique_r(x) = Sub_{K_r}(x)`. -/
def CliqueFunction (r n : ℕ) : (EdgeIndex n → Bool) → Bool :=
  SubHFunction (completeGraphOn r) n

/-- Graph collision `GCK_r` (paper Eq. (7)): the marked vertices `supp(x)` of the
known graph `G` contain a copy of `K_r`. -/
def markedContainsClique {n : ℕ} (G : FinGraph (Fin n)) (r : ℕ) (x : Fin n → Bool) : Prop :=
  ∃ s : Finset (Fin n), s.card = r ∧ IsCliqueSet G s ∧ ∀ v ∈ s, x v = true

/-- The decision function `GCK_{r,G}`: input is the vertex marking string. -/
def graphCollisionFunction {n : ℕ} (G : FinGraph (Fin n)) (r : ℕ) :
    (Fin n → Bool) → Bool :=
  fun x => if markedContainsClique G r x then true else false

/-! ## Certificate data -/

/-- The set of edges (as `EdgeIndex` coordinates) both of whose endpoints lie in `s`. -/
def edgeSetOf {n : ℕ} (s : Finset (Fin n)) : Finset (EdgeIndex n) :=
  Finset.univ.filter fun e : EdgeIndex n => e.val.1 ∈ s ∧ e.val.2 ∈ s

/-- Edge-set certificates of the `K_r` copies of the complete graph on `n` vertices. -/
def cliqueCertificateFamily (r n : ℕ) : Finset (Finset (EdgeIndex n)) :=
  (Finset.univ.filter (fun s : Finset (Fin n) => s.card = r)).image edgeSetOf

/-- Vertex-set certificates of the `K_r` copies of a fixed graph `G`. -/
def cliqueVertexFamily {n : ℕ} (G : FinGraph (Fin n)) (r : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun s : Finset (Fin n) => s.card = r ∧ IsCliqueSet G s)

/-- Edge-set certificates of the `K_r` copies of a fixed graph `G`. -/
def cliqueEdgeFamily {n : ℕ} (G : FinGraph (Fin n)) (r : ℕ) : Finset (Finset (EdgeIndex n)) :=
  (cliqueVertexFamily G r).image edgeSetOf

/-! ## Bounded-error quantum query model

The paper writes `Q(f)` for the minimum worst-case number of queries of an algorithm
that decides `f` with probability at least `2/3` on every input (probability at most
`1/3` on negative inputs).  We express lower bounds `Q(f) ≥ T` as the refusal of every
bounded-error circuit with fewer than `T` queries.  The oracle is the standard bit
oracle, lifted to an arbitrary finite workspace `W` by `workspaceBitOracle`; acceptance
is the event that the target qubit reads `1`.  The initial state is any normalized
state independent of the input (fixed gates are free in the paper's model, so this
covers every `U₀|0⟩`). -/

/-- The acceptance event: the target qubit reads `1`. -/
def acceptEvent {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W] :
    Finset ((I × Bool) × W) :=
  Finset.univ.filter fun p : (I × Bool) × W => p.1.2 = true

/-- Acceptance probability of a circuit on the fixed input `x`. -/
def acceptMass {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (f : (I → Bool) → Bool) (C : Circuit ((I × Bool) × W))
    (init : QState ((I × Bool) × W)) (x : I → Bool) : ℝ :=
  MeasureProb (Run (workspaceBitOracle x) C init) acceptEvent

/-- A bounded-error decision circuit for `f`: correct with probability `≥ 2/3` on
positive inputs and `≤ 1/3` on negative inputs, simultaneously for every `x`. -/
def Decides {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (f : (I → Bool) → Bool) (C : Circuit ((I × Bool) × W))
    (init : QState ((I × Bool) × W)) : Prop :=
  IsUnitaryCircuit C ∧ Normalized init ∧
    ∀ x : I → Bool,
      (f x = true → acceptMass f C init x ≥ 2 / 3) ∧
      (f x = false → acceptMass f C init x ≤ 1 / 3)

/-- `Q(f) ≥ T`: no bounded-error circuit with fewer than `T` queries decides `f`. -/
def QueryLowerBound {I : Type} [Fintype I] [DecidableEq I]
    (f : (I → Bool) → Bool) (T : ℕ) : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W]
    (C : Circuit ((I × Bool) × W)) (init : QState ((I × Bool) × W)),
    Decides f C init → T ≤ QueryCount C

/-- The search problem attached to a certificate family `F`: the input `x` is positive
when some `C ∈ F` has all coordinates set to `true`. -/
def presentIn {I : Type} (F : Finset (Finset I)) (x : I → Bool) : Prop :=
  ∃ C ∈ F, ∀ j ∈ C, x j = true

/-- Success probability of a search algorithm with decoding map `dec`, on input `x`,
averaged over the computational-basis measurement. -/
def searchSuccessMass {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (F : Finset (Finset I)) (C : Circuit ((I × Bool) × W))
    (init : QState ((I × Bool) × W)) (dec : ((I × Bool) × W) → Finset I)
    (x : I → Bool) : ℝ :=
  MeasureProb (Run (workspaceBitOracle x) C init)
    (Finset.univ.filter fun p : (I × Bool) × W =>
      dec p ∈ F ∧ ∀ j ∈ dec p, x j = true)

/-- A bounded-error search algorithm for the family `F`: on every positive input it
outputs, with probability `≥ 2/3`, a certificate of `F` contained in the support. -/
def SolvesSearch {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (F : Finset (Finset I)) (C : Circuit ((I × Bool) × W))
    (init : QState ((I × Bool) × W)) (dec : ((I × Bool) × W) → Finset I) : Prop :=
  IsUnitaryCircuit C ∧ Normalized init ∧
    ∀ x : I → Bool, presentIn F x → searchSuccessMass F C init dec x ≥ 2 / 3

/-- `Q_search(F) ≥ T`: no bounded-error search algorithm with fewer than `T` queries. -/
def SearchLowerBound {I : Type} [Fintype I] [DecidableEq I]
    (F : Finset (Finset I)) (T : ℕ) : Prop :=
  ∀ (W : Type) [Fintype W] [DecidableEq W]
    (C : Circuit ((I × Bool) × W)) (init : QState ((I × Bool) × W))
    (dec : ((I × Bool) × W) → Finset I),
    SolvesSearch F C init dec → T ≤ QueryCount C

/-! ## Asymptotic lower bounds `n^{e - o(1)}` -/

/-- `Q(f_n) ≥ n^{e-o(1)}`: for every `ε > 0`, eventually `Q(f_n) ≥ n^{e-ε}`. -/
def AsymptoticEdgeLowerBound (f : (n : ℕ) → (EdgeIndex n → Bool) → Bool) (e : ℝ) : Prop :=
  ∀ ε > 0, ∃ n0 : ℕ, ∀ n ≥ n0,
    QueryLowerBound (f n) (Nat.floor ((n : ℝ) ^ (e - ε)))

/-- Mark-based version (graph collision: input `Fin n → Bool`). -/
def AsymptoticMarkLowerBound (f : (n : ℕ) → (Fin n → Bool) → Bool) (e : ℝ) : Prop :=
  ∀ ε > 0, ∃ n0 : ℕ, ∀ n ≥ n0,
    QueryLowerBound (f n) (Nat.floor ((n : ℝ) ^ (e - ε)))

/-- Search version on edge certificates. -/
def AsymptoticEdgeSearchLowerBound
    (F : (n : ℕ) → Finset (Finset (EdgeIndex n))) (e : ℝ) : Prop :=
  ∀ ε > 0, ∃ n0 : ℕ, ∀ n ≥ n0,
    SearchLowerBound (F n) (Nat.floor ((n : ℝ) ^ (e - ε)))

/-- Search version on vertex-mark certificates. -/
def AsymptoticMarkSearchLowerBound
    (F : (n : ℕ) → Finset (Finset (Fin n))) (e : ℝ) : Prop :=
  ∀ ε > 0, ∃ n0 : ℕ, ∀ n ≥ n0,
    SearchLowerBound (F n) (Nat.floor ((n : ℝ) ^ (e - ε)))

/-! ## Exponent sequences and matching-number quantities -/

/-- The exponent `γ_{r,ℓ}` of Eq. (54) from Corollary 4.6. -/
def gamma (r ℓ : ℕ) : ℝ :=
  (1 : ℝ) / 2 + (ℓ : ℝ) * (2 * (r : ℝ) - (ℓ : ℝ) - 1) /
    (2 * ((r : ℝ) - 1) * ((ℓ : ℝ) + 1))

/-- Two edges of `K_r` (as `EdgeIndex r`) are disjoint when they share no endpoint. -/
def DisjointEdges {r : ℕ} (e1 e2 : EdgeIndex r) : Prop :=
  e1.val.1 ≠ e2.val.1 ∧ e1.val.1 ≠ e2.val.2 ∧
    e1.val.2 ≠ e2.val.1 ∧ e1.val.2 ≠ e2.val.2

/-- `A` is a matching (pairwise disjoint edges) inside `K_r`. -/
def IsMatchingEdgeSet {r : ℕ} (A : Finset (EdgeIndex r)) : Prop :=
  ∀ e1 ∈ A, ∀ e2 ∈ A, e1 ≠ e2 → DisjointEdges e1 e2

/-- `A` contains a matching of size `k`. -/
def HasMatchingOfSize {r : ℕ} (A : Finset (EdgeIndex r)) (k : ℕ) : Prop :=
  ∃ M ⊆ A, M.card = k ∧ IsMatchingEdgeSet M

/-- `m(K_r, h)`, Eq. (6): the maximum number of edges in a subgraph of `K_r` with
matching number less than `h`. -/
def mKr (r h : ℕ) : ℕ :=
  (Finset.univ.filter
    (fun A : Finset (EdgeIndex r) => ¬ HasMatchingOfSize A h)).sup Finset.card

/-- The exponent `β_{r,h}` of Eq. (52) / §4.5, expressed through `m(K_r,h)`. -/
def beta (r h : ℕ) : ℝ :=
  (2 * (h : ℝ) / ((h : ℝ) + 1)) *
    (1 - ((mKr r h : ℝ) - ((h : ℝ) - 1) / 2) / (Nat.choose r 2 : ℝ))

/-- A strictly increasing clique-exponent sequence `λ_r`, `r ≥ 4`, as in Theorem 1.1. -/
def IsCliqueExponentSequence (lam : ℕ → ℝ) : Prop :=
  lam 4 = 19 / 18 ∧ (∀ r, 4 ≤ r → lam r < 2) ∧
    (∀ a b, 4 ≤ a → a < b → lam a < lam b)

/-- A strictly increasing complete-bipartite exponent sequence `β_r`, `r ≥ 10`, as in
Theorem 1.4. -/
def IsBipartiteExponentSequence (β : ℕ → ℝ) : Prop :=
  β 10 = 181 / 180 ∧ (∀ r, 10 ≤ r → β r < 2) ∧
    (∀ a b, 10 ≤ a → a < b → β a < β b)

/-- Edges of `K_{r,r}` are pairs `(left, right)`. -/
abbrev BipEdge (r : ℕ) := Fin r × Fin r

/-- A matching in `K_{r,r}`: no two edges share a left or a right endpoint. -/
def IsMatchingBip {r : ℕ} (A : Finset (BipEdge r)) : Prop :=
  ∀ e1 ∈ A, ∀ e2 ∈ A, e1 ≠ e2 → e1.1 ≠ e2.1 ∧ e1.2 ≠ e2.2

/-- `A` contains a bipartite matching of size `k`. -/
def HasMatchingBipOfSize {r : ℕ} (A : Finset (BipEdge r)) (k : ℕ) : Prop :=
  ∃ M ⊆ A, M.card = k ∧ IsMatchingBip M

/-- `m(K_{r,r}, h)`, Eq. (67): the maximum number of edges in a subgraph of `K_{r,r}`
with matching number less than `h`. -/
def mKrr (r h : ℕ) : ℕ :=
  (Finset.univ.filter
    (fun A : Finset (BipEdge r) => ¬ HasMatchingBipOfSize A h)).sup Finset.card

/-- The sequence `β_r` of Eq. (68): the maximum over integer thresholds `2 ≤ h < r`. -/
def betaSeq (r : ℕ) : ℝ :=
  if hr : (Finset.Ico 2 r).Nonempty then
    (Finset.Ico 2 r).sup' hr fun h =>
      (2 * (h : ℝ) * (r : ℝ) / (((h : ℝ) + 1) * ((r : ℝ) + (h : ℝ)))) *
        (1 - ((h : ℝ) - 1) / (r : ℝ) + ((h : ℝ) - 1) / (2 * (r : ℝ) ^ 2))
  else 0

/-- The Bernoulli product weight `µ_p(x) = ∏_j (x_j ? p : 1−p)`. -/
def bernoulliWeight {I : Type} [Fintype I] (p : ℝ) (x : I → Bool) : ℝ :=
  ∏ j, if x j then p else 1 - p

/-- Average search success probability over `x ∼ µ_p`. -/
def averageSearchSuccess {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
    (F : Finset (Finset I)) (C : Circuit ((I × Bool) × W))
    (init : QState ((I × Bool) × W)) (dec : ((I × Bool) × W) → Finset I)
    (p : ℝ) : ℝ :=
  ∑ x : I → Bool, bernoulliWeight p x * searchSuccessMass F C init dec x

end Qatlib.Papers.SubgraphDet26.MainResults
