/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryMagnitude
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceMarkSetHybrid
import Qatlib.Concepts.QueryComplexity.AdversarySearch.WorkspaceQueryLowerBounds
import Qatlib.Concepts.QueryComplexity.DegreeMethod.SensitivityDefinitions
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryDegree
import Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
import Qatlib.Concepts.QueryComplexity.DegreeMethod.SymmetrizationAverageSubgoalBeal
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ApproxPolynomialBlockSensitivityBeal
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.AdaptiveBlockSensitivityQueryBoundBeal
import Qatlib.Concepts.QueryComplexity.Reflections.TwoReflectionQueryAlgorithmRefl
import Qatlib.Concepts.QueryWordCore.QueryMachinery.NegativeAdversary
import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryCoreDefs

set_option backward.isDefEq.respectTransparency false

/-!
# SourceModel — paper-level vocabulary for Hamoudi, "A Brief Introduction to Quantum
Query Complexity", fixed arXiv:2508.08852v1.

This module only fixes names and encodings shared by the claim modules of the paper
block `QQueryIntro25.MainResults`.  It introduces no axioms and states no claim.

The concrete query models are those already frozen in the library:

* deterministic queries: `BoolQueryTree` (Frozen, BBMW section 5);
* randomized queries: `PMF BoolQueryTree` with expected actual queries and success
  probability ≥ 2/3 (`BoolQueryTree.SuccessProb`, `BoolQueryTree.ExpectedQueries`);
* bounded-error quantum queries on total Boolean functions: the frozen workspace
  program minimum `Phase1BooleanQueryMinimumModel.boundedMinimum`;
* bounded-error quantum queries on an arbitrary finite alphabet: the local predicate
  `QuantumQueryComplexityAtMost`, built from the actual frozen `Circuit`,
  `workspaceBitOracle`, `Run`, `QueryCount` and `MeasureProb`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QQueryIntro25.MainResults

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree
open Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
open Qatlib.Concepts.QueryComplexity.AdversarySearch
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.SpectralReadout.PhaseReadout
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.SketchArith.GramAction
open Qatlib.Concepts.AdversaryBounds.AdvDuality

open Matrix
open scoped Classical BigOperators ENNReal Matrix.Norms.L2Operator

/-- Total Boolean functions on `n` bits, the paper's `f : {0,1}^n → {0,1}`. -/
abbrev BitFn (n : ℕ) := (Fin n → Bool) → Bool

/-- Deterministic bounded-free query complexity `D(f)` (Frozen decision-tree model). -/
noncomputable abbrev deterministicComplexity {n : ℕ} (f : BitFn n) : ℕ :=
  deterministicQueryComplexity f

/-- Bounded-error quantum query complexity `Q(f)` (Frozen workspace-program minimum). -/
noncomputable abbrev quantumComplexity {n : ℕ} (f : BitFn n) : ℕ :=
  boundedMinimum f

/-- Exact quantum query complexity (Frozen workspace-program minimum). -/
noncomputable abbrev quantumExactComplexity {n : ℕ} (f : BitFn n) : ℕ :=
  exactMinimum f

/-- Randomized bounded-error query complexity `R(f)`: the least worst-case expected
number of Boolean queries of a finite randomized decision tree that is correct with
probability at least `2/3` on every input.  This is the standard bounded-error
decision-tree model, not bit-operation time. -/
noncomputable def randomizedComplexity {n : ℕ} (f : BitFn n) : ℕ :=
  sInf {T : ℕ | ∃ prog : PMF (BoolQueryTree (Fin n) Bool),
    (∀ x : Fin n → Bool,
      (2 / 3 : ℝ≥0∞) ≤ BoolQueryTree.SuccessProb prog x (fun b => b = f x)) ∧
    (∀ x : Fin n → Bool, BoolQueryTree.ExpectedQueries prog x ≤ (T : ℝ≥0∞))}

/-- The paper's OR function on `n` bits. -/
def ORn (n : ℕ) : BitFn n := fun x => decide (∃ i : Fin n, x i = true)

/-- The all-zero input. -/
def allZero (n : ℕ) : Fin n → Bool := fun _ => false

/-- The `i`-th one-sparse input. -/
def oneSparse {n : ℕ} (i : Fin n) : Fin n → Bool := fun j => decide (j = i)

/-- The parity function on an arbitrary finite coordinate set. -/
def Parity (I : Type) [Fintype I] : (I → Bool) → Bool :=
  fun x => decide ((Finset.univ.filter (fun i => x i = true)).card % 2 = 1)

/-- `Q(f) ≤ T` for a bounded-error quantum algorithm on the finite query alphabet
`Q`: one actual finite unitary circuit over the frozen workspace bit oracle, one
normalized initial state, one accepting register, at most `T` queries and success
probability at least `2/3` on every input. -/
def QuantumQueryComplexityAtMost {Q : Type} [Fintype Q] [DecidableEq Q]
    (f : (Q → Bool) → Bool) (T : ℕ) : Prop :=
  ∃ (W : Type) (instF : Fintype W) (instD : DecidableEq W) (instN : Nonempty W)
    (C : Circuit ((Q × Bool) × W)) (ψ : QState ((Q × Bool) × W))
    (E : Finset ((Q × Bool) × W)),
    letI := instF
    letI := instD
    letI := instN
    IsUnitaryCircuit C ∧ QueryCount C ≤ T ∧ Normalized ψ ∧
      ∀ x : Q → Bool, (2 / 3 : ℝ) ≤
        MeasureProb (Run (workspaceBitOracle (W := W) x) C ψ)
          (if f x then E else Eᶜ)

/-- A balanced AND-OR formula, the paper's AND-OR tree (each internal node has two
children, the levels alternate OR/AND). -/
inductive AndOrFormula where
  | leaf : AndOrFormula
  | node : Bool → AndOrFormula → AndOrFormula → AndOrFormula

namespace AndOrFormula

/-- Evaluate the formula on a leaf assignment, consuming one fresh leaf per `leaf`. -/
def evalFrom (x : ℕ → Bool) : AndOrFormula → ℕ → Bool × ℕ
  | .leaf, k => (x k, k + 1)
  | .node isAnd a b, k =>
      let ra := evalFrom x a k
      let rb := evalFrom x b ra.2
      let v := if isAnd then (ra.1 && rb.1) else (ra.1 || rb.1)
      (v, rb.2)

/-- Number of leaves of the formula. -/
def numLeaves : AndOrFormula → ℕ
  | .leaf => 1
  | .node _ a b => numLeaves a + numLeaves b

/-- The complete depth-`d` alternating AND-OR tree (root level is OR). -/
def balanced : ℕ → AndOrFormula
  | 0 => .leaf
  | d + 1 =>
      let t := balanced d
      if d % 2 = 0 then .node false t t else .node true t t

end AndOrFormula

/-- The Connectivity predicate on `n` vertices, encoded by the ordered-pair adjacency
matrix `x : Fin n × Fin n → Bool` (the paper uses the symmetric `C(n,2)`-bit encoding;
the ordered encoding only changes constants).  Output `true` iff vertex `0` reaches
vertex `1`. -/
def Connectivity (n : ℕ) : (Fin (n + 2) × Fin (n + 2) → Bool) → Bool :=
  fun x => decide (Relation.ReflTransGen (fun u v => x (u, v) = true) 0 1)

/-- The Search problem (Definition 40): on input `x : Fin n → Fin m`, return an index
`i` with `x i = 1` when one exists.  Encoded as a Boolean-predicate on the output. -/
def SearchSuccess {n m : ℕ} (hm : 1 < m) (x : Fin n → Fin m) (out : Option (Fin n)) : Prop :=
  ∃ i : Fin n, out = some i ∧ x i = ⟨1, hm⟩

/-- The Boolean query oracle of the Search problem: querying coordinate `i` asks
whether `x i = 1`. -/
def searchOracle {n m : ℕ} (hm : 1 < m) (x : Fin n → Fin m) : Fin n → Bool :=
  fun i => decide (x i = ⟨1, hm⟩)

/-- The uniform average success probability of a randomized Search program on
`x : Fin n → Fin m`, as an extended nonnegative real. -/
noncomputable def searchUniformSuccess {n m : ℕ} (hm : 1 < m)
    (prog : PMF (BoolQueryTree (Fin n) (Option (Fin n)))) : ℝ≥0∞ :=
  (∑ x : Fin n → Fin m,
      BoolQueryTree.SuccessProb prog (searchOracle hm x) (SearchSuccess hm x)) /
    (Fintype.card (Fin n → Fin m) : ℝ≥0∞)

end Qatlib.Papers.QQueryIntro25.MainResults
