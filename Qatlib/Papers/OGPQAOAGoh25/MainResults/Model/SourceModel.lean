/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

set_option backward.isDefEq.respectTransparency false

/-!
# Source model for Goh, *The Overlap Gap Property limits limit swapping in the QAOA*

Fixed source: arXiv:2404.06087v6 (Mark Goh, QIC 25, 329–343, 2025-08-02).

This module fixes the semantic vocabulary shared by the paper-layer claims
(`c001`–`c009`) and nothing beyond it:

* `q`-uniform hypergraphs on `Fin n`, vertex degree, `d`-regularity, and the
  radius-`p` ball used to speak about locality (§2.1);
* Max-`q`-XORSAT instances (hypergraph together with `±1` coupling signs),
  the cost `H^q_XOR` of eq. (4), its energy density, and the optimal value;
* the QAOA state of eq. (10) as an explicit matrix-vector product
  (cost phase, Pauli-`X` mixer, uniform superposition) and the objective
  `⟨γ,β|C|γ,β⟩` as the diagonal expectation, together with the normalised
  performance `⟨C⟩/|E|` of eqs. (13) and (19);
* deterministic `p`-local algorithms and the local view on which they depend,
  plus the overlap (eq. (8)) and the overlap gap property of Definition 2.1;
* the paper's probabilistic convention: "with high probability as `n → ∞`"
  is `∀ ε > 0, ∀ᶠ n in atTop, mass μ (event) ≥ 1 - ε`, where the random
  hypergraph law is represented by a finite distribution `FinDist` over
  instances, and an Erdős–Rényi resp. `d`-regular law is a finite distribution
  supported on instances whose graph has `m` edges resp. is `d`-regular.

The probability layer is deliberately elementary (finite sums over `FinDist`,
as in the reused `QuantumAlgorithm.Concepts.MonteCarloMean.FinDistBounds`
API): it records the exact finite-probability statements that the paper's
left-hand sides refer to, without importing a measure-theoretic model of the
random hypergraph ensembles. The distributional laws of `G^q_ER(n,m)` and
`R^q(n,d)` are therefore *not* constructed here; theorems that need them take
the law as an explicit supported finite distribution.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OGPQAOAGoh25.MainResults.Model

open scoped BigOperators Matrix
open Filter Topology
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-! ## Hypergraphs (§2.1) -/

/-- The `±1` spin value of a bit. -/
def spinVal (b : Bool) : ℝ := if b then 1 else -1

/-- A `q`-uniform hyperedge on the vertex set `Fin n`. -/
abbrev Hyperedge (n q : ℕ) := {e : Finset (Fin n) // e.card = q}

/-- A `q`-uniform hypergraph on `n` vertices. -/
structure Hypergraph (n q : ℕ) where
  /-- The set of hyperedges. -/
  edges : Finset (Hyperedge n q)
  deriving DecidableEq, Fintype

namespace Hypergraph

variable {n q : ℕ}

/-- The vertex degree, i.e. the number of incident hyperedges. -/
def vertexDegree (G : Hypergraph n q) (v : Fin n) : ℕ :=
  (G.edges.filter (fun e => v ∈ e.1)).card

/-- `d`-regularity: every vertex has degree `d`. -/
def IsRegular (G : Hypergraph n q) (d : ℕ) : Prop := ∀ v, G.vertexDegree v = d

/-- The number of hyperedges. -/
def edgeCount (G : Hypergraph n q) : ℕ := G.edges.card

/-- The vertices sharing a hyperedge with `u`. -/
def neighbors (G : Hypergraph n q) (u : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun w => ∃ e ∈ G.edges, u ∈ e.1 ∧ w ∈ e.1)

/-- The radius-`p` hypergraph ball around `v` (§2.4: the local neighbourhood
explored by a depth-`p` local algorithm). -/
def ball (G : Hypergraph n q) (v : Fin n) : ℕ → Finset (Fin n)
  | 0 => {v}
  | p + 1 => ball G v p ∪ (ball G v p).biUnion (fun u => neighbors G u)

/-- The radius-`0` ball is the singleton `{v}`. -/
@[simp] theorem ball_zero (G : Hypergraph n q) (v : Fin n) :
    G.ball v 0 = {v} := rfl

/-- The radius-`(p+1)` ball is the radius-`p` ball together with all neighbours
of its vertices. -/
theorem ball_succ (G : Hypergraph n q) (v : Fin n) (p : ℕ) :
    G.ball v (p + 1) = G.ball v p ∪ (G.ball v p).biUnion (fun u => G.neighbors u) := rfl

/-- Every vertex belongs to its own radius-`p` ball. -/
theorem self_mem_ball (G : Hypergraph n q) (v : Fin n) (p : ℕ) :
    v ∈ G.ball v p := by
  induction p with
  | zero => simp
  | succ p ih => exact Finset.mem_union_left _ ih

/-- Balls are monotone in the radius. -/
theorem ball_mono (G : Hypergraph n q) (v : Fin n) :
    ∀ p : ℕ, G.ball v p ⊆ G.ball v (p + 1) := by
  intro p
  rw [ball_succ]
  exact Finset.subset_union_left

/-- Every radius-`p` ball is nonempty. -/
theorem ball_card_pos (G : Hypergraph n q) (v : Fin n) (p : ℕ) :
    0 < (G.ball v p).card :=
  Finset.card_pos.mpr ⟨v, self_mem_ball G v p⟩

end Hypergraph

/-! ## Max-`q`-XORSAT instances and the optimal value (§2.2) -/

/-- A signed `q`-uniform hypergraph: the underlying graph together with the
`±1` couplings `J_{i₁…i_q}` of eq. (4). -/
structure Instance (n q : ℕ) where
  /-- The underlying `q`-uniform hypergraph. -/
  graph : Hypergraph n q
  /-- The coupling sign of each hyperedge. -/
  sign : Hyperedge n q → Bool
  deriving DecidableEq, Fintype

namespace Instance

variable {n q : ℕ}

/-- The contribution `(1 + J_e ∏_{i∈e} z_i)/2` of a single clause. -/
def edgeTerm (I : Instance n q) (z : Fin n → Bool) (e : Hyperedge n q) : ℝ :=
  (1 + (if I.sign e then 1 else -1) * ∏ i ∈ e.1, spinVal (z i)) / 2

/-- The Max-`q`-XORSAT cost `H^q_XOR(z)` of eq. (4). -/
def cost (I : Instance n q) (z : Fin n → Bool) : ℝ :=
  ∑ e ∈ I.graph.edges, I.edgeTerm z e

/-- The normalised energy density `H^q_XOR(z)/|E|` (the quantity bounded in
eq. (5) and Theorem 4.2). -/
def density (I : Instance n q) (z : Fin n → Bool) : ℝ :=
  I.cost z / (I.graph.edgeCount : ℝ)

/-- The optimal value of the instance. -/
def optimalValue (I : Instance n q) : ℝ := sSup (Set.range I.cost)

/-- `z` is `ε`-optimal in the sense of Definition 2.1, eq. (6). -/
def NearOptimal (I : Instance n q) (ε : ℝ) (z : Fin n → Bool) : Prop :=
  I.optimalValue - ε ≤ I.cost z

end Instance

/-! ## The QAOA state and objective (§2.4, eq. (10)) -/

variable {n q : ℕ}

/-- The cost operator `Ĉ`, diagonal in the computational basis. -/
def costOperator (I : Instance n q) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  Matrix.diagonal (fun z => (I.cost z : ℂ))

/-- The phase operator `e^{-iγĈ}`. -/
def costPhase (I : Instance n q) (γ : ℝ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  Matrix.diagonal (fun z => Complex.exp (-Complex.I * (γ : ℂ) * (I.cost z : ℂ)))

/-- The mixer `e^{-iβB̂}` with `B̂ = Σ_j X̂_j`, written in the computational
basis: `⟨z|e^{-iβB̂}|w⟩ = ∏_j (z_j = w_j ? cos β : -i sin β)`. -/
def mixerMatrix (n : ℕ) (β : ℝ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  Matrix.of fun z w =>
    ∏ j : Fin n,
      if z j = w j then (Real.cos β : ℂ) else -Complex.I * (Real.sin β : ℂ)

/-- The amplitude `2^{-n/2}` of the uniform superposition `|+⟩^n`. -/
def uniformAmplitude (n : ℕ) : ℂ := ((Real.sqrt (2 ^ n) : ℝ)⁻¹ : ℂ)

/-- The QAOA state `|γ,β⟩` of eq. (10), built layer by layer. -/
def qaoaState (I : Instance n q) :
    (p : ℕ) → (Fin p → ℝ) → (Fin p → ℝ) → ((Fin n → Bool) → ℂ)
  | 0, _, _ => fun _ => uniformAmplitude n
  | p + 1, γ, β =>
      mixerMatrix n (β ⟨p, Nat.lt_succ_self p⟩) *ᵥ
        (costPhase I (γ ⟨p, Nat.lt_succ_self p⟩) *ᵥ
          qaoaState I p (fun i => γ i.castSucc) (fun i => β i.castSucc))

/-- The expectation `⟨ψ|Ĉ|ψ⟩` for a diagonal `Ĉ`, i.e. `Σ_z |ψ_z|² C(z)`. -/
def stateExpectation (C : (Fin n → Bool) → ℝ) (ψ : (Fin n → Bool) → ℂ) : ℝ :=
  ∑ z : Fin n → Bool, Complex.normSq (ψ z) * C z

/-- The QAOA objective `⟨γ,β|Ĉ|γ,β⟩`. -/
def qaoaExpectation (I : Instance n q) (p : ℕ) (γ β : Fin p → ℝ) : ℝ :=
  stateExpectation I.cost (qaoaState I p γ β)

/-- The normalised QAOA performance `⟨γ,β|Ĉ|γ,β⟩/|E|` of eqs. (13) and (19). -/
def qaoaPerformance (I : Instance n q) (p : ℕ) (γ β : Fin p → ℝ) : ℝ :=
  qaoaExpectation I p γ β / (I.graph.edgeCount : ℝ)

/-! ## Local algorithms (§2.4, §4.1) -/

/-- The signed hypergraph seen inside a vertex set `S`. -/
def Instance.localGraph (I : Instance n q) (S : Finset (Fin n)) : Hypergraph n q :=
  ⟨I.graph.edges.filter (fun e => e.1 ⊆ S)⟩

/-- The couplings seen inside a vertex set `S` (off-`S` values are irrelevant). -/
def Instance.localSign (I : Instance n q) (S : Finset (Fin n)) : Hyperedge n q → Bool :=
  fun e => if e.1 ⊆ S then I.sign e else false

/-- Two instances have the same `p`-local view at `v`: equal signed induced
subgraph on the radius-`p` ball around `v`. -/
def SameLocalView (I I' : Instance n q) (v : Fin n) (p : ℕ) : Prop :=
  I.localGraph (I.graph.ball v p) = I'.localGraph (I'.graph.ball v p) ∧
    I.localSign (I.graph.ball v p) = I'.localSign (I'.graph.ball v p)

/-- A deterministic `p`-local algorithm: the bit output at `v` depends only on
the `p`-local view at `v`. -/
structure LocalAlgorithm (n q p : ℕ) where
  /-- The output assignment produced on an instance. -/
  output : Instance n q → Fin n → Bool
  /-- Locality: equal `p`-local views give equal outputs. -/
  local_view : ∀ (I I' : Instance n q) (v : Fin n),
    SameLocalView I I' v p → output I v = output I' v

/-- The energy density of a local algorithm's output on an instance. -/
def LocalAlgorithm.density {n q p : ℕ} (A : LocalAlgorithm n q p) (I : Instance n q) : ℝ :=
  I.density (A.output I)

/-- The algorithm's output stays below the threshold `η` on `I`. -/
def LocalAlgorithm.Below {n q p : ℕ} (A : LocalAlgorithm n q p) (I : Instance n q) (η : ℝ) :
    Prop :=
  A.density I < η

/-! ## Overlap gap property (Definition 2.1, eqs. (6)–(8)) -/

/-- The normalised pairwise overlap `R_{1,2}` of eq. (8). -/
def overlap (z₁ z₂ : Fin n → Bool) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i : Fin n, spinVal (z₁ i) * spinVal (z₂ i)

/-- The OGP of Definition 2.1: every pair of `ε`-optimal solutions has overlap
in `[0, μ₁] ∪ [μ₂, 1]`. -/
def Instance.HasOGP (I : Instance n q) (ε μ₁ μ₂ : ℝ) : Prop :=
  0 ≤ μ₁ ∧ μ₁ < μ₂ ∧ μ₂ ≤ 1 ∧
    ∀ z₁ z₂ : Fin n → Bool, I.NearOptimal ε z₁ → I.NearOptimal ε z₂ →
      overlap z₁ z₂ ∈ Set.Icc (0 : ℝ) μ₁ ∪ Set.Icc μ₂ 1

/-! ## Tree-likeness of local neighbourhoods (Lemmas 4.5–4.7) -/

/-- The hyperedges entirely contained in a vertex set. -/
def Instance.inducedEdges (I : Instance n q) (S : Finset (Fin n)) : Finset (Hyperedge n q) :=
  I.graph.edges.filter (fun e => e.1 ⊆ S)

/-- The radius-`l` neighbourhood of `v` is tree-like when its induced `q`-uniform
hypergraph has the Euler characteristic of a tree, `|V| = (q - 1)|E| + 1`
(§4.1, the "treelike" notion of Lemmas 4.5–4.7). -/
@[reducible] def Instance.IsTreelike (I : Instance n q) (v : Fin n) (l : ℕ) : Prop :=
  (I.inducedEdges (I.graph.ball v l)).card * (q - 1) + 1 = (I.graph.ball v l).card

/-- The number of vertices whose radius-`l` neighbourhood is tree-like. -/
def Instance.treelikeCount (I : Instance n q) (l : ℕ) : ℕ :=
  (Finset.univ.filter (fun v => I.IsTreelike v l)).card

/-- The number of vertices whose radius-`l` neighbourhood is not tree-like. -/
def Instance.badCount (I : Instance n q) (l : ℕ) : ℕ :=
  (Finset.univ.filter (fun v => ¬ I.IsTreelike v l)).card

/-- The fraction of vertices whose radius-`l` neighbourhood is tree-like. -/
def Instance.treelikeFraction (I : Instance n q) (l : ℕ) : ℝ :=
  (I.treelikeCount l : ℝ) / (n : ℝ)

/-- Counting lemma: if at most a `δ`-fraction of the `n` vertices are bad, then
at least a `1 - δ` fraction are good. -/
theorem fraction_ge_of_bad_le {n : ℕ} (k bad : ℕ) (hn : 0 < n)
    (hsum : k + bad = n) {δ : ℝ} (h : (bad : ℝ) ≤ δ * (n : ℝ)) :
    1 - δ ≤ (k : ℝ) / (n : ℝ) := by
  have hbaden : bad ≤ n := by omega
  have hk : k = n - bad := by omega
  rw [hk, Nat.cast_sub hbaden, sub_div, div_self (by exact_mod_cast ne_of_gt hn)]
  have hdn : (bad : ℝ) / (n : ℝ) ≤ δ :=
    (div_le_iff₀ (by exact_mod_cast hn)).mpr h
  linarith

/-- If at most a `δ`-fraction of vertices have a non-tree-like neighbourhood then
at least a `1 - δ` fraction have a tree-like one. -/
theorem Instance.treelikeFraction_ge (I : Instance n q) (l : ℕ) (hn : 0 < n) {δ : ℝ}
    (h : (I.badCount l : ℝ) ≤ δ * (n : ℝ)) :
    1 - δ ≤ I.treelikeFraction l := by
  unfold treelikeFraction
  refine fraction_ge_of_bad_le _ _ hn ?_ h
  unfold treelikeCount badCount
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (p := fun v => I.IsTreelike v l)
  simpa using h

/-! ## Finite probability layer -/

/-- The probability mass of an event under a finite distribution. -/
def mass {X : Type*} [Fintype X] [DecidableEq X]
    (μ : FinDist X) (P : X → Prop) [DecidablePred P] : ℝ :=
  ∑ x ∈ Finset.univ.filter P, μ.prob x

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The mass of the universal event is one. -/
@[simp] theorem mass_true (μ : FinDist X) : mass μ (fun _ => True) = 1 := by
  simp [mass, μ.sum_one]

/-- The mass of the empty event is zero. -/
@[simp] theorem mass_false (μ : FinDist X) : mass μ (fun _ => False) = 0 := by
  simp [mass]

/-- Probability masses are nonnegative. -/
theorem mass_nonneg (μ : FinDist X) (P : X → Prop) [DecidablePred P] :
    0 ≤ mass μ P :=
  Finset.sum_nonneg fun x _ => μ.nonneg x

/-- Every event has mass at most one. -/
theorem mass_le_one (μ : FinDist X) (P : X → Prop) [DecidablePred P] :
    mass μ P ≤ 1 := by
  unfold mass
  rw [Finset.sum_filter]
  calc ∑ x : X, (if P x then μ.prob x else 0) ≤ ∑ x : X, μ.prob x := by
        refine Finset.sum_le_sum fun x _ => ?_
        by_cases h : P x
        · simp [h]
        · simp [h]; exact μ.nonneg x
    _ = 1 := μ.sum_one

/-- The mass of the complement is one minus the mass of the event. -/
theorem mass_compl (μ : FinDist X) (P : X → Prop) [DecidablePred P] :
    mass μ (fun x => ¬ P x) = 1 - mass μ P := by
  have h : mass μ P + mass μ (fun x => ¬ P x) = 1 := by
    unfold mass
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib, ← μ.sum_one]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : P x <;> simp [h]
  linarith

/-- Mass is monotone with respect to event inclusion. -/
theorem mass_mono (μ : FinDist X) {P Q : X → Prop} [DecidablePred P] [DecidablePred Q]
    (h : ∀ x, P x → Q x) : mass μ P ≤ mass μ Q := by
  unfold mass
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases hP : P x
  · have hQ : Q x := h x hP
    simp [hP, hQ]
  · simp only [hP, if_false]
    by_cases hQ : Q x <;> simp [hQ, μ.nonneg x]

/-- The union bound for two events. -/
theorem mass_or_le (μ : FinDist X) (P Q : X → Prop) [DecidablePred P]
    [DecidablePred Q] [DecidablePred (fun x => P x ∨ Q x)] :
    mass μ (fun x => P x ∨ Q x) ≤ mass μ P + mass μ Q := by
  unfold mass
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases hP : P x <;> by_cases hQ : Q x <;> simp [hP, hQ, μ.nonneg x]

/-- The intersection lower bound `P(A) + P(B) - 1 ≤ P(A ∩ B)`. -/
theorem mass_and_ge (μ : FinDist X) (P Q : X → Prop) [DecidablePred P]
    [DecidablePred Q] [DecidablePred (fun x => P x ∧ Q x)] :
    mass μ P + mass μ Q - 1 ≤ mass μ (fun x => P x ∧ Q x) := by
  have h1 : mass μ (fun x => ¬ (P x ∧ Q x)) ≤
      mass μ (fun x => ¬ P x) + mass μ (fun x => ¬ Q x) :=
    (mass_mono μ (fun x hx => not_and_or.mp hx)).trans (mass_or_le _ _ _)
  rw [mass_compl, mass_compl, mass_compl] at h1
  linarith

/-- Markov/Chebyshev deviation bound for a single draw: the mass of the event
`ε < |f - E f|` is at most `Var f / ε²`. This is the exact finite-sum form of
the moment bounds used in Lemma 4.4, eqs. (23)–(27). -/
theorem mass_abs_dev_le (μ : FinDist X) (f : X → ℝ) (ε : ℝ) (hε : 0 < ε) :
    mass μ (fun x => ε < |f x - μ.expect f|) ≤ μ.variance f / ε ^ 2 := by
  have hstep : mass μ (fun x => ε < |f x - μ.expect f|) ≤
      mass μ (fun x => 1 ≤ (f x - μ.expect f) ^ 2 / ε ^ 2) := by
    refine mass_mono μ ?_
    intro x hx
    have hsq : ε ^ 2 ≤ (f x - μ.expect f) ^ 2 := by
      nlinarith [abs_nonneg (f x - μ.expect f), sq_abs (f x - μ.expect f)]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)]
    simpa using hsq
  have hcalc : mass μ (fun x => 1 ≤ (f x - μ.expect f) ^ 2 / ε ^ 2) ≤
      μ.variance f / ε ^ 2 := by
    unfold mass
    rw [Finset.sum_filter]
    have hterm : ∀ x : X,
        (if 1 ≤ (f x - μ.expect f) ^ 2 / ε ^ 2 then μ.prob x else 0) ≤
          μ.prob x * ((f x - μ.expect f) ^ 2 / ε ^ 2) := by
      intro x
      by_cases h : 1 ≤ (f x - μ.expect f) ^ 2 / ε ^ 2
      · simp only [h, if_true]
        calc μ.prob x = μ.prob x * 1 := by ring
          _ ≤ μ.prob x * ((f x - μ.expect f) ^ 2 / ε ^ 2) :=
              mul_le_mul_of_nonneg_left h (μ.nonneg x)
      · simp only [h, if_false]
        exact mul_nonneg (μ.nonneg x) (by positivity)
    calc ∑ x : X, (if 1 ≤ (f x - μ.expect f) ^ 2 / ε ^ 2 then μ.prob x else 0)
        ≤ ∑ x : X, μ.prob x * ((f x - μ.expect f) ^ 2 / ε ^ 2) :=
          Finset.sum_le_sum fun x _ => hterm x
      _ = (∑ x : X, μ.prob x * (f x - μ.expect f) ^ 2) / ε ^ 2 := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun x _ => by ring
      _ = μ.variance f / ε ^ 2 := by
          unfold FinDist.variance FinDist.expect
          rfl
  linarith

/-! ### Random-instance laws -/

/-- An Erdős–Rényi law: supported on instances with exactly `m` hyperedges
(the `G^q_ER(n,m)` model of §2.1). -/
def IsERLaw (μ : FinDist (Instance n q)) (m : ℕ) : Prop :=
  ∀ I : Instance n q, 0 < μ.prob I → I.graph.edgeCount = m

/-- A random-regular law: supported on `d`-regular instances (the `R^q(n,d)`
model of §2.1). -/
def IsRegularLaw (μ : FinDist (Instance n q)) (d : ℕ) : Prop :=
  ∀ I : Instance n q, 0 < μ.prob I → I.graph.IsRegular d

/-- First marginal of a joint law over instance pairs (used for the coupling
argument in the proof of Theorem 4.1). -/
def marginalFst (ν : FinDist (Instance n q × Instance n q)) :
    FinDist (Instance n q) where
  prob I := ∑ J : Instance n q, ν.prob (I, J)
  nonneg I := Finset.sum_nonneg fun J _ => ν.nonneg (I, J)
  sum_one := by
    rw [← Fintype.sum_prod_type (f := fun x : Instance n q × Instance n q => ν.prob x)]
    exact ν.sum_one

/-- Second marginal of a joint law over instance pairs. -/
def marginalSnd (ν : FinDist (Instance n q × Instance n q)) :
    FinDist (Instance n q) where
  prob J := ∑ I : Instance n q, ν.prob (I, J)
  nonneg J := Finset.sum_nonneg fun I _ => ν.nonneg (I, J)
  sum_one := by
    rw [Finset.sum_comm]
    rw [← Fintype.sum_prod_type (f := fun x : Instance n q × Instance n q => ν.prob x)]
    exact ν.sum_one

/-- The mass of an event depending only on the second coordinate equals its
mass under the second marginal. -/
theorem mass_marginalSnd (ν : FinDist (Instance n q × Instance n q))
    (P : Instance n q → Prop) [DecidablePred P] :
    mass (marginalSnd ν) P = mass ν (fun ω => P ω.2) := by
  have hlhs : mass (marginalSnd ν) P =
      ∑ J : Instance n q, ∑ I : Instance n q, (if P J then ν.prob (I, J) else 0) := by
    unfold mass marginalSnd
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun J _ => ?_
    by_cases h : P J <;> simp [h]
  rw [hlhs, Finset.sum_comm]
  have hrhs : mass ν (fun ω => P ω.2) =
      ∑ I : Instance n q, ∑ J : Instance n q, (if P J then ν.prob (I, J) else 0) := by
    unfold mass
    rw [Finset.sum_filter]
    exact Fintype.sum_prod_type (f := fun x : Instance n q × Instance n q =>
      (if P x.2 then ν.prob x else 0))
  rw [hrhs]

/-- The mass of an event depending only on the first coordinate equals its
mass under the first marginal. -/
theorem mass_marginalFst (ν : FinDist (Instance n q × Instance n q))
    (P : Instance n q → Prop) [DecidablePred P] :
    mass (marginalFst ν) P = mass ν (fun ω => P ω.1) := by
  have hlhs : mass (marginalFst ν) P =
      ∑ I : Instance n q, ∑ J : Instance n q, (if P I then ν.prob (I, J) else 0) := by
    unfold mass marginalFst
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun I _ => ?_
    by_cases h : P I <;> simp [h]
  have hrhs : mass ν (fun ω => P ω.1) =
      ∑ I : Instance n q, ∑ J : Instance n q, (if P I then ν.prob (I, J) else 0) := by
    unfold mass
    rw [Finset.sum_filter]
    exact Fintype.sum_prod_type (f := fun x : Instance n q × Instance n q =>
      (if P x.1 then ν.prob x else 0))
  rw [hlhs, hrhs]

/-! ### The abstract transfer step of Theorem 4.1 -/

/-- **Transfer lemma (proof core of Theorem 4.1).** Suppose a joint law `ν` of an
Erdős–Rényi instance and a regular instance is such that (i) with mass at least
`1 - δ` the two instances have algorithm-output densities within `γ`, and
(ii) on the Erdős–Rényi side the algorithm's density is below `η` with mass at
least `1 - δ'`. Then the regular side is below `η + γ` with mass at least
`1 - (δ + δ')`. This is the contradiction/union-bound step of §4.1. -/
theorem limited_transfer
    (ν : FinDist (Instance n q × Instance n q))
    {p : ℕ} (A : LocalAlgorithm n q p) (η γ : ℝ) (δ δ' : ℝ)
    (hclose : 1 - δ ≤ mass ν (fun ω =>
      |ω.1.density (A.output ω.1) - ω.2.density (A.output ω.2)| ≤ γ))
    (hER : 1 - δ' ≤ mass (marginalFst ν) (fun I => I.density (A.output I) < η)) :
    1 - (δ + δ') ≤ mass (marginalSnd ν) (fun I => I.density (A.output I) < η + γ) := by
  have hER' : 1 - δ' ≤ mass ν (fun ω => ω.1.density (A.output ω.1) < η) := by
    rw [← mass_marginalFst ν (fun I => I.density (A.output I) < η)]
    exact hER
  have hnot1 : mass ν (fun ω : Instance n q × Instance n q =>
      ¬ (ω.1.density (A.output ω.1) < η)) ≤ δ' := by
    have hc := mass_compl ν (fun ω : Instance n q × Instance n q =>
      ω.1.density (A.output ω.1) < η)
    linarith
  have hnot2 : mass ν (fun ω : Instance n q × Instance n q =>
      ¬ (|ω.1.density (A.output ω.1) - ω.2.density (A.output ω.2)| ≤ γ)) ≤ δ := by
    have hc := mass_compl ν (fun ω : Instance n q × Instance n q =>
      |ω.1.density (A.output ω.1) - ω.2.density (A.output ω.2)| ≤ γ)
    linarith
  have hbad_mass : mass (marginalSnd ν)
      (fun I => ¬ I.density (A.output I) < η + γ) ≤ δ + δ' := by
    rw [mass_marginalSnd]
    have hsub : mass ν (fun ω : Instance n q × Instance n q =>
        ¬ ω.2.density (A.output ω.2) < η + γ) ≤
        mass ν (fun ω : Instance n q × Instance n q =>
          ¬ (ω.1.density (A.output ω.1) < η) ∨
          ¬ (|ω.1.density (A.output ω.1) - ω.2.density (A.output ω.2)| ≤ γ)) := by
      refine mass_mono ν ?_
      intro ω hω
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2⟩ := hcon
      have hbd := abs_le.mp h2
      have hle : ω.2.density (A.output ω.2) < η + γ := by linarith [h1, hbd.1]
      exact hω hle
    have hor := mass_or_le ν (fun ω : Instance n q × Instance n q =>
        ¬ (ω.1.density (A.output ω.1) < η))
      (fun ω => ¬ (|ω.1.density (A.output ω.1) - ω.2.density (A.output ω.2)| ≤ γ))
    linarith
  have hgood : mass (marginalSnd ν) (fun I => I.density (A.output I) < η + γ)
      = 1 - mass (marginalSnd ν) (fun I => ¬ I.density (A.output I) < η + γ) := by
    rw [mass_compl]; ring
  rw [hgood]
  linarith

end Qatlib.Papers.OGPQAOAGoh25.MainResults.Model
