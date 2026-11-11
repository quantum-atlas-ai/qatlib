/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# KDistinctness11 — source model

Belovs–Lee, *Quantum Algorithm for k-distinctness with Prior Knowledge on the Input*,
arXiv:1108.3022v1 (15 Aug 2011).

This file gives the paper-local vocabulary needed to state the fifteen active claims.
Nothing here is a mathematical result; it is a faithful reading of the paper's own
definitions:

* `Input n m` is `[m]^n` (§2).
* `IsSubtuple` is the paper's Eq. (1) (a `t`-subtuple with respect to `J`).
* `HasKD` is the k-distinctness function (§1).
* `Specification`, `tupleCount`, `HasSpecification` and `TypeMatrix` are the
  specification `(b_t)` and the type `β̃(S)` of §4.3.
* `Arc`, `LearningGraph`, `Flow`, `negativeCost`, `positiveCost`, `complexity`
  are Definitions 6 and 7 of §3.1.
* `AdvFeasible` / `adversaryBound` are Eq. (2)–(3) of §2.1 (the dual general
  adversary bound `Adv±`).
* `AlmostSymmetric` is Definition 14 / Eq. (8) of §4.4, with the hidden constants
  of the `Θ` written out explicitly.
* `loadSpec` / `algorithmLoads` is the specification update of Algorithm 1
  (lines 5–12) and the global step schedule of §5.2.

All definitions are paper-local: the repository has no shared learning-graph
library, so the model is introduced here rather than bound to a nonexistent
Foundations unit.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.KDistinctness11.MainResults

open Finset BigOperators
open scoped BigOperators ENNReal

/-! ## Inputs, tuples, specifications (§2, §4.3) -/

/-- An input to the `[m]^n` query problem: a value in `Fin m` at every index. -/
abbrev Input (n m : ℕ) := Fin n → Fin m

/-- The k-distinctness function (§1): true iff some `k` indices carry equal values. -/
def HasKD {n m : ℕ} (k : ℕ) (x : Input n m) : Prop :=
  ∃ I : Finset (Fin n), I.card = k ∧ ∀ i ∈ I, ∀ j ∈ I, x i = x j

/-- Eq. (1): `I` is a `t`-subtuple with respect to `J` when all elements of `I` are
equal, every element of `J \ I` differs from them, and `|I| = t`. -/
def IsSubtuple {n m : ℕ} (x : Input n m) (J I : Finset (Fin n)) (t : ℕ) : Prop :=
  (∀ i ∈ I, ∀ j ∈ I, x i = x j) ∧
  (∀ i ∈ I, ∀ j ∈ J, j ∉ I → x i ≠ x j) ∧
  I.card = t

/-- The `t`-tuples (§1): subtuples with respect to the full index set `[n]`. -/
def IsTuple {n m : ℕ} (x : Input n m) (I : Finset (Fin n)) (t : ℕ) : Prop :=
  IsSubtuple x univ I t

/-- Number of `t`-subtuples (with respect to `S`) contained in `S`. -/
def tupleCount {n m : ℕ} (x : Input n m) (S : Finset (Fin n)) (t : ℕ) : ℕ := by
  classical
  exact (S.powerset.filter (fun I => IsSubtuple x S I t)).card

/-- A specification `(b_1, …, b_{k-1})` (§4.3). -/
abbrev Specification (k : ℕ) := Fin (k - 1) → ℕ

/-- `b` is the specification of `S` for input `x`: exactly `b t` many `(t+1)`-subtuples. -/
def HasSpecification {n m : ℕ} (k : ℕ) (x : Input n m) (S : Finset (Fin n))
    (b : Specification k) : Prop :=
  ∀ t : Fin (k - 1), tupleCount x S (t.val + 1) = b t

/-- The type `β̃(S)` of §4.3: entry `(t,s)` counts `(t+1)`-subtuples of `S`
contained in the selected tuple-set `A s` (`A : Fin k → Finset (Fin n)`, the
last index standing for the marked set `M`). -/
def TypeMatrix {n m : ℕ} (k : ℕ) (x : Input n m) (S : Finset (Fin n))
    (A : Fin k → Finset (Fin n)) : Matrix (Fin (k - 1)) (Fin k) ℕ := by
  classical
  exact fun t s => (S.powerset.filter
    (fun I => IsSubtuple x S I (t.val + 1) ∧ I ⊆ A s)).card

/-- A vertex set `S` is accepting for input `x` if it contains a `k`-element set
of equal values, i.e. a 1-certificate of k-distinctness (§3.1). -/
def Accepting {n m : ℕ} (k : ℕ) (x : Input n m) (S : Finset (Fin n)) : Prop :=
  ∃ I : Finset (Fin n), I ⊆ S ∧ I.card = k ∧ ∀ i ∈ I, ∀ j ∈ I, x i = x j

/-! ## Learning graphs (§3.1, Definitions 6 and 7) -/

/-- An arc of a learning graph: source set `S` and loaded index `j`.  The
well-formedness condition `j ∉ S` is a separate predicate (`Arc.Valid`), so that
the arc type is finite and decidable. -/
structure Arc (n : ℕ) where
  source : Finset (Fin n)
  load : Fin n
deriving DecidableEq, Fintype

/-- Target set `S ∪ {j}` of an arc. -/
def Arc.target {n : ℕ} (e : Arc n) : Finset (Fin n) := insert e.load e.source

/-- The arity condition of Definition 6. -/
def Arc.Valid {n : ℕ} (e : Arc n) : Prop := e.load ∉ e.source

/-- Definition 6: a learning graph over `[n]` with alphabet `[m]`.  `arcs` is the
set of present arcs, and `weight e α` is the weight of arc `e` evaluated at the
partial assignment `α : source → [m]` (weights may depend on the values learned
so far). -/
structure LearningGraph (n m : ℕ) where
  arcs : Finset (Arc n)
  valid_only : ∀ e ∈ arcs, e.load ∉ e.source
  weight : (e : Arc n) → (e.source → Fin m) → ℝ≥0∞

/-- The weight of an arc on input `x` (zero for a missing arc, as in the paper's
"weight 0 means the arc is missing"). -/
def LearningGraph.arcWeight {n m : ℕ} (G : LearningGraph n m) (x : Input n m)
    (e : Arc n) : ℝ≥0∞ :=
  if e ∈ G.arcs then G.weight e (fun i => x i.1) else 0

/-- The vertex set of a learning graph: all sources and targets of present arcs. -/
def LearningGraph.vertices {n m : ℕ} (G : LearningGraph n m) : Finset (Finset (Fin n)) :=
  G.arcs.image Arc.source ∪ G.arcs.image Arc.target

/-- `G` computes `f` if every positive input admits an accepting vertex (§3.1). -/
def LearningGraph.Computes {n m : ℕ} (G : LearningGraph n m) (k : ℕ)
    (f : Input n m → Bool) : Prop :=
  ∀ x, f x = true → ∃ S ∈ G.vertices, Accepting k x S

/-- Definition 7: a flow on `G(x)`, after interning weight-zero arcs as absent.
`root` is the unit source condition and `conservation` is flow conservation at
every non-root non-accepting vertex. -/
structure Flow {n m : ℕ} (G : LearningGraph n m) (k : ℕ) (x : Input n m) where
  val : Arc n → ℝ≥0∞
  root : (∑ e ∈ G.arcs.filter (fun e => e.source = ∅), val e) = 1
  conservation : ∀ S : Finset (Fin n), S ≠ ∅ → ¬ Accepting k x S →
    (∑ e ∈ G.arcs.filter (fun e => e.target = S), val e) =
      (∑ e ∈ G.arcs.filter (fun e => e.source = S), val e)

/-- Negative complexity `N(G(y)) = Σ_e w_e(y)` of §3.1. -/
def negativeCost {n m : ℕ} (G : LearningGraph n m) (y : Input n m) : ℝ≥0∞ :=
  ∑ e ∈ G.arcs, G.weight e (fun i => y i.1)

/-- Flow complexity `Σ_e p_e² / w_e` with the paper's `0/0 = 0` convention
(`ENNReal` division has `0 / 0 = 0`). -/
def flowCost {n m : ℕ} {k : ℕ} (G : LearningGraph n m) (x : Input n m)
    (p : Flow G k x) : ℝ≥0∞ :=
  ∑ e ∈ G.arcs, p.val e ^ 2 / G.weight e (fun i => x i.1)

/-- Positive complexity `P(G(x))`: the smallest flow complexity (§3.1). -/
def positiveCost {n m : ℕ} (G : LearningGraph n m) (k : ℕ) (x : Input n m) : ℝ≥0∞ :=
  ⨅ p : Flow G k x, flowCost G x p

/-- Negative complexity of the learning graph: maximum over negative inputs. -/
def negComplexity {n m : ℕ} (G : LearningGraph n m) (f : Input n m → Bool) : ℝ≥0∞ :=
  (univ.filter (fun y : Input n m => f y = false)).sup (fun y => negativeCost G y)

/-- Positive complexity of the learning graph: maximum over positive inputs. -/
def posComplexity {n m : ℕ} (G : LearningGraph n m) (k : ℕ)
    (f : Input n m → Bool) : ℝ≥0∞ :=
  (univ.filter (fun x : Input n m => f x = true)).sup (fun x => positiveCost G k x)

/-- The complexity of a learning graph: geometric mean of the positive and
negative complexities (§3.1). -/
def complexity {n m : ℕ} (G : LearningGraph n m) (k : ℕ)
    (f : Input n m → Bool) : ℝ≥0∞ :=
  ENNReal.rpow (negComplexity G f) (1 / 2) * ENNReal.rpow (posComplexity G k f) (1 / 2)

/-! ## The dual general adversary bound (§2.1, Eqs. (2)–(3)) -/

/-- Feasibility of Eq. (3): `Σ_{j : x_j ≠ y_j} ⟨u_{x,j} | u_{y,j}⟩ = 1` whenever
`f x ≠ f y`. -/
def AdvFeasible {n m : ℕ} (f : Input n m → Bool) {k : ℕ}
    (u : Input n m → Fin n → EuclideanSpace ℂ (Fin k)) : Prop :=
  ∀ x y, f x ≠ f y →
    (∑ j ∈ (univ.filter (fun j : Fin n => x j ≠ y j)), inner ℂ (u x j) (u y j)) = 1

/-- The objective of Eq. (3): the geometric mean of the largest positive and
negative squared norms. -/
def advValue {n m : ℕ} {k : ℕ}
    (u : Input n m → Fin n → EuclideanSpace ℂ (Fin k)) : ℝ≥0∞ :=
  ENNReal.rpow (⨆ x, ∑ j, ENNReal.rpow (‖u x j‖₊ : ℝ≥0∞) 2) (1 / 2) *
    ENNReal.rpow (⨆ y, ∑ j, ENNReal.rpow (‖u y j‖₊ : ℝ≥0∞) 2) (1 / 2)

/-- The dual general adversary bound `Adv±(f)` of Eq. (3). -/
def adversaryBound {n m : ℕ} (f : Input n m → Bool) : ℝ≥0∞ := by
  classical
  exact ⨅ (k : ℕ), ⨅ (u : Input n m → Fin n → EuclideanSpace ℂ (Fin k)),
    if AdvFeasible f u then advValue u else ⊤

/-! ## Almost symmetric flows (§4.4, Definition 14, Eq. (8)) -/

/-- The number `|E(y)|` of arcs of class `E` that are present with nonzero weight
on input `y`. -/
def activeCount {n m : ℕ} (G : LearningGraph n m) {ι : Type} [DecidableEq ι]
    (cls : Arc n → ι) (y : Input n m) (E : ι) : ℕ := by
  classical
  exact ((G.arcs.filter (fun e => cls e = E)).filter
    (fun e => G.arcWeight y e ≠ 0)).card

/-- Definition 14 / Eq. (8) with the constants hidden in `Θ` made explicit.
`cls` partitions the arcs into equivalency classes, `π E` is the typical flow of
class `E`, `τ E` its speciality, `p x` the flow on `G(x)` and `typical x E` the
set `G(E,x)` of typical arcs (all with respect to a fixed positive input `x`). -/
structure AlmostSymmetric {n m : ℕ} (G : LearningGraph n m) (k : ℕ)
    (f : Input n m → Bool) {ι : Type} [DecidableEq ι]
    (cls : Arc n → ι) (τ π : ι → ℝ) (p : ∀ x : Input n m, Arc n → ℝ)
    (typical : ∀ x : Input n m, ι → Finset (Arc n)) : Prop where
  τ_pos : ∀ E, 0 < τ E
  π_pos : ∀ E, 0 < π E
  p_nonneg : ∀ x e, 0 ≤ p x e
  typical_mem : ∀ x E, typical x E ⊆ G.arcs.filter (fun e => cls e = E)
  typical_flow_pos : ∀ x E e, e ∈ typical x E → 0 < p x e
  typical_flow_lower : ∀ x E e, e ∈ typical x E → π E ≤ p x e
  typical_flow_upper : ∀ x E e, e ∈ typical x E → p x e ≤ 2 * π E
  flow_mass : ∀ x E,
    (∑ e ∈ G.arcs.filter (fun e => cls e = E), p x e ^ 2) ≤
      2 * ∑ e ∈ typical x E, p x e ^ 2
  neg_count : ∀ y x E, f y = false → f x = true →
    (activeCount G cls y E : ℝ) ≤ 2 * τ E * (typical x E).card

/-- The typical flow `μ(E) = π(E) · max_x |G(E,x)|` of §4.4. -/
def mu {n m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (π : ι → ℝ)
    (typical : ∀ x : Input n m, ι → Finset (Arc n)) (E : ι) : ℝ :=
  π E * ((univ.sup (fun x : Input n m => (typical x E).card) : ℕ) : ℝ)

/-! ## The specification schedule of Algorithm 1 (§5.2) -/

/-- The load-level-`l` specification update of lines 5–11: `b_l` increases by one
and `b_{l-1}` decreases by one (for `l = 1` only the first effect, since there is
no `0`-subtuple). -/
def loadSpec (k : ℕ) (l : ℕ) (b : Specification k) : Specification k :=
  fun t =>
    if t.val + 1 = l then b t + 1
    else if t.val + 2 = l then b t - 1
    else b t

/-- The load pattern of one stage `i`, applied `r i` times: levels `1, …, i`. -/
def stageBlock (i : ℕ) (r : ℕ → ℕ) : List ℕ :=
  (List.replicate (r i) ((List.range i).map (fun t => t + 1))).flatten

/-- The `l`-values of the steps of Algorithm 1 (§5.2): `r 1` unrestricted loads,
then stage `i = 2, …, k-1` consisting of `r i` repetitions of the block
`(1, 2, …, i)`, then the final unrestricted load (level `k`). -/
def algorithmLoads (k : ℕ) (r : ℕ → ℕ) : List ℕ :=
  List.replicate (r 1) 1 ++ (List.range (k - 2)).flatMap (fun d => stageBlock (d + 2) r) ++ [k]

/-- The k-distinctness decision problem as a boolean function (§1). -/
def kDistinctness (k : ℕ) {n m : ℕ} (x : Input n m) : Bool := by
  classical
  exact decide (HasKD k x)

/-! ## A≥1, specification counting and averages (§4.3, §5.2, §5.4) -/

/-- `A` is the set `A_{≥ 1}` of §4.3 for the input `x`: it has exactly `ℓ t` many
`(t+1)`-subtuples for every `t`. -/
def IsAgeqOne {n m : ℕ} (k : ℕ) (x : Input n m) (A : Finset (Fin n))
    (ℓ : Fin (k - 1) → ℕ) : Prop :=
  ∀ t : Fin (k - 1), tupleCount x A (t.val + 1) = ℓ t

/-- Number of subsets of `A` satisfying the specification `b` on input `x`
(the quantity whose ratio Lemma 12 controls). -/
def specCount {n m : ℕ} (k : ℕ) (x : Input n m) (A : Finset (Fin n))
    (b : Specification k) : ℕ := by
  classical
  exact (A.powerset.filter (fun S => HasSpecification k x S b)).card

/-- Average number of `t`-subtuples over the `r`-element subsets of `A`
(Lemma 17's expectation). -/
def meanTupleCount {n m : ℕ} (x : Input n m) (A : Finset (Fin n)) (r t : ℕ) : ℝ := by
  classical
  exact ((A.powerset.filter (fun S => S.card = r)).sum
      (fun S => (tupleCount x S t : ℝ))) /
    ((A.powerset.filter (fun S => S.card = r)).card : ℝ)

/-- Run a list of load levels through the specification update of Algorithm 1. -/
def runLoads (k : ℕ) : Specification k → List ℕ → Specification k
  | b, [] => b
  | b, l :: ls => runLoads k (loadSpec k l b) ls

/-- The loads performed before stage `i` (stage `i` consists of repeated blocks
`(1, …, i)`, so the prefix before it is the first stage plus stages `2, …, i-1`). -/
def stagePrefixLoads (k i : ℕ) (r : ℕ → ℕ) : List ℕ :=
  List.replicate (r 1) 1 ++ (List.range (i - 2)).flatMap (fun d => stageBlock (d + 2) r)

/-- `b` is a valid specification at stage `i`: it is what the specification update
of Algorithm 1 produces from the empty first-stage specification. -/
def IsStageSpec (k i : ℕ) (r : ℕ → ℕ) (b : Specification k) : Prop :=
  b = runLoads k (fun _ => 0) (stagePrefixLoads k i r)

/-- The type `β̃(S)` read as a real matrix. -/
def typeReal {n m : ℕ} (k : ℕ) (x : Input n m) (S : Finset (Fin n))
    (A : Fin k → Finset (Fin n)) : Matrix (Fin (k - 1)) (Fin k) ℝ :=
  fun t s => (TypeMatrix k x S A t s : ℝ)

/-- The sup norm `‖M‖_∞ = max |M_{t,s}|` of a type matrix, valued in `ℝ≥0∞`
(the paper's `‖·‖_∞` of §4.3). -/
def matSupNorm {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) : ℝ≥0∞ :=
  Finset.univ.sup (fun i => Finset.univ.sup (fun j => ENNReal.ofReal |M i j|))

/-- The expectation `ε_β` of §5.4: the average type over the uniform distribution
on the subsets of `A` satisfying `b`. -/
def meanType {n m : ℕ} (k : ℕ) (x : Input n m) (A : Finset (Fin n))
    (b : Specification k) (Acols : Fin k → Finset (Fin n)) :
    Matrix (Fin (k - 1)) (Fin k) ℝ := by
  classical
  let T := A.powerset.filter (fun S => HasSpecification k x S b)
  exact fun t s => ((T.sum (fun S => TypeMatrix k x S Acols t s)) : ℝ) / (T.card : ℝ)

/-- A type matrix is typical for the expectation `ε` when it lies in the
`C √r₁`-ball of `ε` (§5.4). -/
def IsTypicalType {n m : ℕ} (k : ℕ) (ε : Matrix (Fin (k - 1)) (Fin k) ℝ)
    (C r1 : ℝ) (M : Matrix (Fin (k - 1)) (Fin k) ℝ) : Prop :=
  ∀ t s, |M t s - ε t s| ≤ C * Real.sqrt r1

/-- A vertex is a key vertex when it carries a specification (§5.3). -/
def IsKeyVertex {n m : ℕ} (k : ℕ) (x : Input n m) (S : Finset (Fin n)) : Prop :=
  ∃ b : Specification k, HasSpecification k x S b

/-- Two vertices have the same specification. -/
def SameSpec {n m : ℕ} (k : ℕ) (x : Input n m) (S S' : Finset (Fin n)) : Prop :=
  ∃ b : Specification k, HasSpecification k x S b ∧ HasSpecification k x S' b

end Qatlib.Papers.KDistinctness11.MainResults
