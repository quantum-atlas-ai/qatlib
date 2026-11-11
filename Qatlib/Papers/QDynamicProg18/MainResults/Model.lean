/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Finset.Powerset
import Mathlib.Logic.Relation
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm

set_option backward.isDefEq.respectTransparency false

/-!
# QDynamicProg18 — the model layer of Section 2 and the problem catalogue

This module fixes the objects the paper reasons about, so that every claim of
the paper can be stated against named definitions instead of prose:

* the four decision/optimisation problems of Section 2 (pp. 3–4): Hypercube
  Path, Bandwidth, Travelling Salesman and Minimum Set Cover, plus the
  Directed Feedback Arc Set of Section 5.2;
* the vertex-ordering problem class of Eq. (3) (p. 6);
* the costed, bounded-error quantum algorithm interface used by every
  running-time claim of the paper;
* the binary entropy (in bits) of Theorem 3 and the minimum set-cover size of
  Proposition 11.

The paper works in the QRAM model (Section 2, p. 4).  The shared library does
not expose a complete QRAM cost backend in this paper layer, so the
quantum-realisation obligation is carried as the field `isQuantum` of
`BoundedErrorQuantumAlgorithm` and is documented — but not discharged — here.
Running-time claims are stated as existence of such an algorithm with the
paper's `O*` bound.
-/

namespace Qatlib.Papers.QDynamicProg18.MainResults

open Classical

set_option autoImplicit false

noncomputable section

/-! ## §1 Binary entropy in bits (Theorem 3, p. 4) -/

/-- The binary entropy of `p`, in bits: the paper's
`H(ε) = −ε log₂ ε − (1−ε) log₂(1−ε)` (Theorem 3, p. 4).  It is Mathlib's
natural-logarithm `Real.binEntropy` rescaled by `log 2`. -/
noncomputable def binEntropyBits (p : ℝ) : ℝ := Real.binEntropy p / Real.log 2

/-- `0 · log 0 = 0` is Mathlib's convention, and the bits rescaling of the
binary entropy is exactly the paper's `H`. -/
theorem binEntropyBits_eq (p : ℝ) :
    binEntropyBits p =
      -(p * (Real.log p / Real.log 2) + (1 - p) * (Real.log (1 - p) / Real.log 2)) := by
  unfold binEntropyBits Real.binEntropy
  rw [Real.log_inv, Real.log_inv]
  ring

/-! ## §2 Decision and optimisation problem interfaces -/

/-- A decision problem: instances, the acceptance predicate, a polynomial
size `polySize` and the exponent-carrying size `n` appearing in `O*(c^n)`. -/
structure DecisionProblem where
  /-- the instances of the problem -/
  Instance : Type
  /-- the acceptance predicate -/
  accepts : Instance → Prop
  /-- the parameter of the polynomial factor (`n` or `m + n`) -/
  polySize : Instance → ℕ
  /-- the dimension `n` in the exponent `c ^ n` -/
  exponent : Instance → ℕ

/-- An optimisation problem: instances, the integer optimum, and the two size
parameters. -/
structure FunctionProblem where
  /-- the instances of the problem -/
  Instance : Type
  /-- the optimal value the algorithm must return -/
  value : Instance → ℕ
  /-- the parameter of the polynomial factor -/
  polySize : Instance → ℕ
  /-- the dimension `n` in the exponent `c ^ n` -/
  exponent : Instance → ℕ

/-! ## §3 Bounded-error algorithms and `O*` cost bounds -/

/-- A costed procedure: its output on every input, its failure probability
(at most `1/3`, i.e. a bounded-error algorithm) and its worst-case runtime. -/
structure CostedAlgorithm (Instance : Type) (Output : Type) where
  /-- the output produced on each instance -/
  output : Instance → Output
  /-- the probability that the output is wrong -/
  failure : ℝ
  /-- bounded error: the failure probability is at most `1/3` -/
  failure_le : failure ≤ 1 / 3
  /-- the worst-case cost on each instance -/
  runtime : Instance → ℝ

/-- A bounded-error algorithm together with the obligation that it is realised
by a quantum algorithm in the QRAM model of Section 2 (p. 4).  The predicate
`isQuantum` is the modelling interface: this paper layer does not reconstruct
the shared QRAM cost backend, so none of the statements below discharges it;
each running-time claim is stated as an existence statement that includes it. -/
structure BoundedErrorQuantumAlgorithm (Instance : Type) (Output : Type)
    extends CostedAlgorithm Instance Output where
  /-- the quantum-realisation obligation (QRAM model, Section 2) -/
  isQuantum : Prop

/-- The `O*(c ^ n)` cost bound of the paper: there is a constant `C > 0` and a
polynomial degree `d` with `runtime x ≤ C · (polySize x + 1)^d · c ^ (exponent x)`
on every instance. -/
def IsExpTimeBound {Instance : Type} {Output : Type}
    (A : CostedAlgorithm Instance Output)
    (polySize : Instance → ℕ) (exponent : Instance → ℕ) (c : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ x : Instance,
    A.runtime x ≤ C * ((polySize x : ℝ) + 1) ^ d * c ^ (exponent x)

/-- The `O*(c ^ n · factor)` cost bound: the paper's TSP bound carries an
additional `log L` factor (Theorem 8, p. 12). -/
def IsExpTimeBoundWithFactor {Instance : Type} {Output : Type}
    (A : CostedAlgorithm Instance Output)
    (polySize : Instance → ℕ) (exponent : Instance → ℕ) (factor : Instance → ℝ)
    (c : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ x : Instance,
    A.runtime x ≤ C * ((polySize x : ℝ) + 1) ^ d * factor x * c ^ (exponent x)

/-- A decision problem is solved in `O*(c^n)` by a bounded-error quantum
algorithm when some such algorithm answers every instance correctly and its
runtime obeys the bound. -/
def SolvesDecisionInTime (P : DecisionProblem) (c : ℝ) : Prop :=
  ∃ A : BoundedErrorQuantumAlgorithm P.Instance Bool,
    A.isQuantum ∧ (∀ x, (A.output x = true ↔ P.accepts x)) ∧
    IsExpTimeBound A.toCostedAlgorithm P.polySize P.exponent c

/-- An optimisation problem is solved in `O*(c^n)` by a bounded-error quantum
algorithm when some such algorithm returns the optimum on every instance and
its runtime obeys the bound. -/
def SolvesValueInTime (P : FunctionProblem) (c : ℝ) : Prop :=
  ∃ A : BoundedErrorQuantumAlgorithm P.Instance ℕ,
    A.isQuantum ∧ (∀ x, A.output x = P.value x) ∧
    IsExpTimeBound A.toCostedAlgorithm P.polySize P.exponent c

/-- Variant of `SolvesValueInTime` with an instance-dependent multiplicative
factor (used for the `log L` of Theorem 8). -/
def SolvesValueInTimeWithFactor (P : FunctionProblem) (factor : P.Instance → ℝ)
    (c : ℝ) : Prop :=
  ∃ A : BoundedErrorQuantumAlgorithm P.Instance ℕ,
    A.isQuantum ∧ (∀ x, A.output x = P.value x) ∧
    IsExpTimeBoundWithFactor A.toCostedAlgorithm P.polySize P.exponent factor c

/-! ## §4 Hypercube Path (Section 2, p. 3 and Section 3) -/

/-- The directed hypercube edge `x → y`: `y` is obtained from `x` by changing
one `0` bit to `1` (Section 2, p. 3). -/
def HypercubeEdge {n : ℕ} (x y : Fin n → Bool) : Prop :=
  ∃ i : Fin n, x i = false ∧ y i = true ∧ ∀ j : Fin n, j ≠ i → x j = y j

/-- The all-zero word `0ⁿ`. -/
def zeroWord (n : ℕ) : Fin n → Bool := fun _ => false

/-- The all-one word `1ⁿ`. -/
def oneWord (n : ℕ) : Fin n → Bool := fun _ => true

/-- A subgraph of `Qₙ` given by query access: `G x y = true` iff the hypercube
edge `x → y` is present in `G`. -/
abbrev HypercubeInstance (n : ℕ) := (Fin n → Bool) → (Fin n → Bool) → Bool

/-- `HypercubePath` accepts `G` iff there is a directed path from `0ⁿ` to `1ⁿ`
in the queried subgraph (Section 2, p. 3, Definition of Hypercube Path). -/
def HypercubePathAccepts {n : ℕ} (G : HypercubeInstance n) : Prop :=
  Relation.ReflTransGen (fun x y => HypercubeEdge x y ∧ G x y = true)
    (zeroWord n) (oneWord n)

/-- The Hypercube Path decision problem of dimension `n`. -/
def hypercubePathProblem (n : ℕ) : DecisionProblem where
  Instance := HypercubeInstance n
  accepts := HypercubePathAccepts
  polySize := fun _ => n
  exponent := fun _ => n

/-! ## §5 Graph ordering objectives and the class of Eq. (3) -/

/-- A finite graph on `n` labelled vertices, given by query access to its
adjacency matrix. -/
abbrev GraphInstance (n : ℕ) := Fin n → Fin n → Bool

/-- The prefix set `π_{<v} = {u | π u < π v}` of an ordering `π`, as a Boolean
word (Section 3.2, p. 6). -/
def orderingPrefix {n : ℕ} (π : Equiv.Perm (Fin n)) (v : Fin n) : Fin n → Bool :=
  fun u => decide (π u < π v)

/-- The per-ordering objective of the vertex-ordering problem class of
Eq. (3) (p. 6): the pointwise maximum (first form) or the sum (second form)
of the per-vertex cost `f` over the prefix sets of `π`. -/
def orderingObjective {n : ℕ} (cost : (Fin n → Bool) → Fin n → ℕ)
    (minmax : Bool) (π : Equiv.Perm (Fin n)) : ℕ :=
  if minmax then
    Finset.univ.sup (fun v : Fin n => cost (orderingPrefix π v) v)
  else
    ∑ v : Fin n, cost (orderingPrefix π v) v

/-- The optimal value of the vertex-ordering objective over all `n!`
orderings — the `min` of the two forms of Eq. (3) (p. 6). -/
def vertexOrderingValue {n : ℕ} (cost : (Fin n → Bool) → Fin n → ℕ)
    (minmax : Bool) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun π : Equiv.Perm (Fin n) =>
    orderingObjective cost minmax π)

/-- A decision problem belongs to the vertex-ordering class of Eq. (3)
(p. 6) when it carries a vertex count, a polynomial-time per-vertex cost and
a form flag, such that every instance is accepted exactly when its min-max or
min-sum ordering value equals the instance's target. -/
def InVertexOrderingClass (P : DecisionProblem) : Prop :=
  ∃ (vertexCount : P.Instance → ℕ)
    (cost : (x : P.Instance) → (Fin (vertexCount x) → Bool) → Fin (vertexCount x) → ℕ)
    (minmax : P.Instance → Bool) (target : P.Instance → ℕ),
    ∀ x : P.Instance,
      (P.accepts x ↔ vertexOrderingValue (cost x) (minmax x) = target x)

/-! ## §6 Bandwidth (Section 2, p. 3 and Section 4) -/

/-- The width of an ordering `π` of a graph with adjacency `G`: the largest
edge length `|πu − πv|` over present edges (Section 2, p. 3). -/
def orderingWidth {n : ℕ} (G : GraphInstance n) (π : Equiv.Perm (Fin n)) : ℕ :=
  Finset.univ.sup (fun p : Fin n × Fin n =>
    if G p.1 p.2 = true then Int.natAbs ((π p.1 : ℤ) - (π p.2 : ℤ)) else 0)

/-- The bandwidth of a graph: the minimum width over all orderings
(Section 2, p. 3). -/
def bandwidthValue {n : ℕ} (G : GraphInstance n) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun π : Equiv.Perm (Fin n) =>
    orderingWidth G π)

/-- The Bandwidth optimisation problem on `n` vertices. -/
def bandwidthProblem (n : ℕ) : FunctionProblem where
  Instance := GraphInstance n
  value := bandwidthValue
  polySize := fun _ => n
  exponent := fun _ => n

/-! ## §7 Travelling Salesman (Section 2, p. 3 and Section 5) -/

/-- The cyclic successor `i + 1 mod n` on `Fin n`, for `n > 0`. -/
def cyclicSucc {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩

/-- The length of the Hamiltonian cycle that follows the ordering `π` on the
weighted graph `w` (Section 5, p. 12). -/
def tspTourLength {n : ℕ} (hn : 0 < n) (w : Fin n → Fin n → ℕ)
    (π : Equiv.Perm (Fin n)) : ℕ :=
  ∑ i : Fin n, w (π i) (π (cyclicSucc hn i))

/-- The length of the shortest Hamiltonian cycle — the TSP optimum
(Section 2, p. 3). -/
def tspValue {n : ℕ} (hn : 0 < n) (w : Fin n → Fin n → ℕ) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun π : Equiv.Perm (Fin n) =>
    tspTourLength hn w π)

/-- The largest edge weight `L` of the weighted graph `w` (Section 5, p. 12),
read as a real number for the logarithmic factor. -/
def tspMaxWeight {n : ℕ} (w : Fin n → Fin n → ℕ) : ℝ :=
  ((Finset.univ.sup (fun p : Fin n × Fin n => w p.1 p.2) : ℕ) : ℝ)

/-- The `log L` factor of the TSP running time (Theorem 8, p. 12). -/
def tspLogWeight {n : ℕ} (w : Fin n → Fin n → ℕ) : ℝ := Real.log (tspMaxWeight w)

/-- The Travelling Salesman optimisation problem on `n` vertices. -/
def tspProblem (n : ℕ) (hn : 0 < n) : FunctionProblem where
  Instance := Fin n → Fin n → ℕ
  value := tspValue hn
  polySize := fun _ => n
  exponent := fun _ => n

/-! ## §8 Directed Feedback Arc Set (Section 5.2, p. 13) -/

/-- A digraph edge relation is acyclic when it admits a topological ranking. -/
def IsAcyclic {n : ℕ} (E : Fin n → Fin n → Prop) : Prop :=
  ∃ rank : Fin n → ℕ, ∀ u v : Fin n, E u v → rank u < rank v

/-- The minimum feedback arc set of a digraph: the least number of present
edges whose removal makes the digraph acyclic (Section 5.2, p. 13). -/
def feedbackArcSetSize {n : ℕ} (E : Fin n → Fin n → Bool) : ℕ :=
  Finset.univ.inf' Finset.univ_nonempty (fun F : Finset (Fin n × Fin n) =>
    if IsAcyclic (fun u v => E u v = true ∧ (u, v) ∉ F) then F.card else n * n + 1)

/-- The Directed Feedback Arc Set optimisation problem on `n` vertices. -/
def feedbackArcSetProblem (n : ℕ) : FunctionProblem where
  Instance := Fin n → Fin n → Bool
  value := feedbackArcSetSize
  polySize := fun _ => n
  exponent := fun _ => n

/-! ## §9 Minimum Set Cover (Section 2, p. 4 and Section 6, p. 13) -/

/-- `C` is a set cover of the universe `U`: every element of `U` lies in some
set of the family `C` (Section 2, p. 4). -/
def Covers {α : Type} [DecidableEq α] (U : Finset α) (C : Finset (Finset α)) : Prop :=
  ∀ x ∈ U, ∃ S ∈ C, x ∈ S

/-- The set of cardinalities of subfamilies of `S` that cover `U`. -/
def coverCardSet {α : Type} [DecidableEq α] (U : Finset α)
    (S : Finset (Finset α)) : Finset ℕ :=
  (S.powerset.filter (fun C => Covers U C)).image Finset.card

/-- The minimum set-cover size `f(U, S)` of Section 6 (p. 13): the smallest
cardinality of a subfamily of `S` covering `U`, and `0` when no subfamily
covers `U` (the paper always works with coverable universes). -/
def minCoverSize {α : Type} [DecidableEq α] (U : Finset α)
    (S : Finset (Finset α)) : ℕ :=
  if h : (coverCardSet U S).Nonempty then (coverCardSet U S).min' h else 0

/-- A Minimum Set Cover instance: a finite universe and a collection of
subsets (Section 2, p. 4). -/
structure SetCoverInstance (α : Type) [DecidableEq α] where
  /-- the element universe `U` -/
  U : Finset α
  /-- the collection `S ⊆ 2^U` -/
  S : Finset (Finset α)

/-- The Minimum Set Cover optimisation problem (Section 6, p. 13). -/
def setCoverProblem (α : Type) [DecidableEq α] : FunctionProblem where
  Instance := SetCoverInstance α
  value := fun inst => minCoverSize inst.U inst.S
  polySize := fun inst => inst.U.card + inst.S.card
  exponent := fun inst => inst.U.card

end

end Qatlib.Papers.QDynamicProg18.MainResults
