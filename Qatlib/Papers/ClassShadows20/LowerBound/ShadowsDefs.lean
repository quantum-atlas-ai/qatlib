/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowChannel.TensorPauliShadowStatistics
import Qatlib.Papers.ClassShadows20.LowerBound.StatisticsDefs
import Qatlib.Concepts.AmplitudeSearch.Amplification.ExecutionDefs
import Qatlib.Concepts.ShadowModels.ShadowChannel.CliffordBasisShadowNormSubgoalStat
import Qatlib.Papers.ClassShadows20.LowerBound.PovmInformationHidingSubgoalStat
import Qatlib.Concepts.ShadowModels.UStatBackend.OrderedHigherUStatistic

/-!
# Shadow norms and lower bound data

`shadowQuadraticMoment` and `stateSupShadowNormSq` define an ensemble-dependent quadratic moment
and its supremum over density operators; `exactStateSupShadowNormSq` records a separate
closed-form expression. The module also defines finite ensemble and resource records,
bounded-kernel conditions, separated state families, and the scalar demand and allowance used in
the lower bound.

These constructions support the treatment in [HuangKuengPreskill2020].

## Main statements

* `stateSupShadowNormSq`: takes the density-state supremum of the ensemble moment.
* `PackingFamily.Separated`: specifies normalized points with positive separation.
* `theorem5WrapperAllowance`: defines the information allowance per shot.

## References

* [Huang et al., 2020][HuangKuengPreskill2020]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ShadowModels.UStatBackend
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.AmplitudeSearch.Amplification

set_option autoImplicit false

namespace Qatlib.Papers.ClassShadows20.LowerBound

open Matrix Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.ShadowModels.ShadowChannel.HuangKuengPreskill2020
open Qatlib
open scoped Classical BigOperators

/-- The finite ensemble-and-basis sum of measurement weights times the square of the `(d +
1)`-scaled real observable overlap. -/
noncomputable def shadowQuadraticMoment {d : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (μ : FinDist I) (Uf : I → Operator d) (σ O : Operator d) : ℝ :=
  ∑ b : Fin d, ∑ i, (μ.prob i *
      (Matrix.trace (basisProjector b * (Uf i * σ * (Uf i)ᴴ))).re) *
      (((d : ℝ) + 1) *
        (Matrix.trace (O * ((Uf i)ᴴ * basisProjector b * Uf i))).re) ^ 2

/-- The supremum of `shadowQuadraticMoment μ Uf σ O` over density operators `σ`. -/
noncomputable def stateSupShadowNormSq {d : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (μ : FinDist I) (Uf : I → Operator d) (O : Operator d) : ℝ :=
  sSup {x : ℝ | ∃ σ : Operator d, IsDensityOperator σ ∧
    x = shadowQuadraticMoment μ Uf σ O}

/-- The product of `(d+1)/(d+2)` with the sum of the real trace of `O²` and twice the supremum
of the real trace of `σ * O²` over density operators `σ`. -/
noncomputable def exactStateSupShadowNormSq (d : ℕ) (O : Operator d) : ℝ :=
  ((d : ℝ) + 1) / ((d : ℝ) + 2) *
    ((Matrix.trace (O * O)).re +
      2 * sSup {x : ℝ | ∃ σ : Operator d, IsDensityOperator σ ∧
        x = (Matrix.trace (σ * (O * O))).re})

/-- The value `3` raised to the number of nonidentity factors in the Pauli word. -/
noncomputable def pauliShadowNormSq {n : ℕ} (w : Fin n → Option (Fin 3)) : ℝ :=
  (3 : ℝ) ^ tensorPauliWeight w

/-- A finite indexed family of `n`-qubit operators, with its size stored as data. -/
structure CliffordEnsemble (n : ℕ) where

  size : ℕ

  members : Fin size → Operator (2 ^ n)

/-- The condition that every ensemble member is unitary and that the family satisfies
`IsOverlapDesign` at degree three. -/
def CliffordEnsemble.IsGlobalThreeDesign {n : ℕ} (E : CliffordEnsemble n) : Prop :=
  (∀ i : Fin E.size, E.members i ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) ∧
    IsOverlapDesign (2 ^ n) 3 (fun i : Fin E.size => E.members i)

/-- A record containing a finite operator ensemble, a fair-bit count, a finite gate word, and a
wire count. -/
structure FairBitCliffordSampler (n : ℕ) where

  ensemble : CliffordEnsemble n

  fairBits : ℕ

  word : List FiniteGateCode

  wires : ℕ

/-- The condition that the recorded ensemble is a global three-design, the gate word is legal,
and a positive bit count has enough bit strings for the ensemble size. -/
def FairBitCliffordSampler.Correct {n : ℕ} (S : FairBitCliffordSampler n) : Prop :=
  S.ensemble.IsGlobalThreeDesign ∧
    finiteWordLegal S.wires S.word = true ∧
    0 < S.fairBits ∧
    S.ensemble.size ≤ 2 ^ S.fairBits

/-- A sampler family has one polynomial resource bound valid at every input size. -/
def FairBitCliffordSampler.PolyBounded (S : (n : ℕ) → FairBitCliffordSampler n) : Prop :=
  ∃ (c e : ℕ), ∀ n : ℕ,
    (S n).fairBits ≤ c * (n + 1) ^ e ∧
      (S n).word.length ≤ c * (n + 1) ^ e ∧
      (S n).wires ≤ c * (n + 1) ^ e

/-- A record of the sample-record constant, group constant, and confidence parameter. -/
structure SourceConfidenceLedger where

  recordConstant : ℝ

  groupConstant : ℝ

  δ : ℝ

/-- The condition that both ledger constants are positive and its confidence parameter lies
strictly between zero and one. -/
def SourceConfidenceLedger.Correct (L : SourceConfidenceLedger) : Prop :=
  0 < L.recordConstant ∧ 0 < L.groupConstant ∧ 0 < L.δ ∧ L.δ < 1

/-- Data consisting of a sample size, an order, a list kernel, and a real bound parameter. -/
structure NonIIDHigherTransport (X : Type*) [Fintype X] where

  m : ℕ

  r : ℕ

  h : List X → ℝ

  B : ℝ

/-- The condition that the sample size is positive, the order is at most the sample size, and
the kernel is bounded by a nonnegative `B` on lists of that order. -/
def NonIIDHigherTransport.Conservative {X : Type*} [Fintype X]
    (t : NonIIDHigherTransport X) : Prop :=
  0 < t.m ∧ t.r ≤ t.m ∧ 0 ≤ t.B ∧
    (∀ xs : List X, xs.length = t.r → |t.h xs| ≤ t.B)

/-- The mean of the list kernel over the supplied `T` order-`r` tuples, using real division by
`T`. -/
noncomputable def incompleteUValue {X : Type} [Fintype X] (r T : ℕ)
    (h : List X → ℝ) (Ω : Fin T → Fin r → X) : ℝ :=
  (1 / (T : ℝ)) * ∑ t : Fin T, h (List.ofFn (Ω t))

/-- Data consisting of a sample size, an order, a tuple count, a list kernel, and a real bound
parameter. -/
structure IncompleteUBackend (X : Type*) [Fintype X] where

  m : ℕ

  r : ℕ

  T : ℕ

  h : List X → ℝ

  B : ℝ

/-- The condition of positive sample and tuple counts, order at most sample size, and a
nonnegative uniform bound on the kernel for all lists. -/
def IncompleteUBackend.Complete {X : Type*} [Fintype X]
    (b : IncompleteUBackend X) : Prop :=
  0 < b.m ∧ b.r ≤ b.m ∧ 0 < b.T ∧ 0 ≤ b.B ∧
    (∀ xs : List X, |b.h xs| ≤ b.B)

/-- A finite family of states in dimension `d` together with a proposed real separation
parameter. -/
structure PackingFamily (d : ℕ) where

  size : ℕ

  points : Fin size → QState (Fin d)

  sep : ℝ

/-- The condition that the family and separation are positive, every point is normalized, and
distinct points have Euclidean distance at least the separation. -/
def PackingFamily.Separated {d : ℕ} (P : PackingFamily d) : Prop :=
  0 < P.size ∧ 0 < P.sep ∧
    (∀ i : Fin P.size, Normalized (P.points i)) ∧
    (∀ i j : Fin P.size, i ≠ j →
      P.sep ≤ ‖toEuclidean_fromVec (P.points i - P.points j)‖)

/-- The scalar decoding demand `(1 - δ) * log M - 1`, with the natural logarithm. -/
noncomputable def theorem5WrapperDemand (M : ℕ) (δ : ℝ) : ℝ :=
  (1 - δ) * Real.log (M : ℝ) - 1

/-- The scalar per-shot allowance `α² * (d - r) / (r * (d + 1))`. -/
noncomputable def theorem5WrapperAllowance (d r : ℕ) (α : ℝ) : ℝ :=
  α ^ 2 * ((d : ℝ) - (r : ℝ)) / ((r : ℝ) * ((d : ℝ) + 1))

end Qatlib.Papers.ClassShadows20.LowerBound
