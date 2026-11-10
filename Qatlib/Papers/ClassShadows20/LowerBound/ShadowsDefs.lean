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
set_option warningAsError false
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
set_option linter.unusedVariables false

namespace Qatlib.Papers.ClassShadows20.LowerBound

open Matrix Qatlib.Concepts.AmplitudeSearch.Amplification
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.ShadowModels.ShadowChannel.HuangKuengPreskill2020
open Qatlib
open scoped Classical BigOperators

noncomputable def shadowQuadraticMoment {d : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (μ : FinDist I) (Uf : I → Operator d) (σ O : Operator d) : ℝ :=
  ∑ b : Fin d, ∑ i, (μ.prob i *
      (Matrix.trace (basisProjector b * (Uf i * σ * (Uf i)ᴴ))).re) *
      (((d : ℝ) + 1) *
        (Matrix.trace (O * ((Uf i)ᴴ * basisProjector b * Uf i))).re) ^ 2

noncomputable def stateSupShadowNormSq {d : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (μ : FinDist I) (Uf : I → Operator d) (O : Operator d) : ℝ :=
  sSup {x : ℝ | ∃ σ : Operator d, IsDensityOperator σ ∧
    x = shadowQuadraticMoment μ Uf σ O}

noncomputable def exactStateSupShadowNormSq (d : ℕ) (O : Operator d) : ℝ :=
  ((d : ℝ) + 1) / ((d : ℝ) + 2) *
    ((Matrix.trace (O * O)).re +
      2 * sSup {x : ℝ | ∃ σ : Operator d, IsDensityOperator σ ∧
        x = (Matrix.trace (σ * (O * O))).re})

noncomputable def pauliShadowNormSq {n : ℕ} (w : Fin n → Option (Fin 3)) : ℝ :=
  (3 : ℝ) ^ tensorPauliWeight w

structure CliffordEnsemble (n : ℕ) where

  size : ℕ

  members : Fin size → Operator (2 ^ n)

def CliffordEnsemble.IsGlobalThreeDesign {n : ℕ} (E : CliffordEnsemble n) : Prop :=
  (∀ i : Fin E.size, E.members i ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ) ∧
    IsOverlapDesign (2 ^ n) 3 (fun i : Fin E.size => E.members i)

structure FairBitCliffordSampler (n : ℕ) where

  ensemble : CliffordEnsemble n

  fairBits : ℕ

  word : List FiniteGateCode

  wires : ℕ

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

structure SourceConfidenceLedger where

  recordConstant : ℝ

  groupConstant : ℝ

  δ : ℝ

def SourceConfidenceLedger.Correct (L : SourceConfidenceLedger) : Prop :=
  0 < L.recordConstant ∧ 0 < L.groupConstant ∧ 0 < L.δ ∧ L.δ < 1

structure NonIIDHigherTransport (X : Type*) [Fintype X] where

  m : ℕ

  r : ℕ

  h : List X → ℝ

  B : ℝ

def NonIIDHigherTransport.Conservative {X : Type*} [Fintype X]
    (t : NonIIDHigherTransport X) : Prop :=
  0 < t.m ∧ t.r ≤ t.m ∧ 0 ≤ t.B ∧
    (∀ xs : List X, xs.length = t.r → |t.h xs| ≤ t.B)

noncomputable def incompleteUValue {X : Type} [Fintype X] (r T : ℕ)
    (h : List X → ℝ) (Ω : Fin T → Fin r → X) : ℝ :=
  (1 / (T : ℝ)) * ∑ t : Fin T, h (List.ofFn (Ω t))

structure IncompleteUBackend (X : Type*) [Fintype X] where

  m : ℕ

  r : ℕ

  T : ℕ

  h : List X → ℝ

  B : ℝ

def IncompleteUBackend.Complete {X : Type*} [Fintype X]
    (b : IncompleteUBackend X) : Prop :=
  0 < b.m ∧ b.r ≤ b.m ∧ 0 < b.T ∧ 0 ≤ b.B ∧
    (∀ xs : List X, |b.h xs| ≤ b.B)

structure PackingFamily (d : ℕ) where

  size : ℕ

  points : Fin size → QState (Fin d)

  sep : ℝ

def PackingFamily.Separated {d : ℕ} (P : PackingFamily d) : Prop :=
  0 < P.size ∧ 0 < P.sep ∧
    (∀ i : Fin P.size, Normalized (P.points i)) ∧
    (∀ i j : Fin P.size, i ≠ j →
      P.sep ≤ ‖toEuclidean_fromVec (P.points i - P.points j)‖)

noncomputable def theorem5WrapperDemand (M : ℕ) (δ : ℝ) : ℝ :=
  (1 - δ) * Real.log (M : ℝ) - 1

noncomputable def theorem5WrapperAllowance (d r : ℕ) (α : ℝ) : ℝ :=
  α ^ 2 * ((d : ℝ) - (r : ℝ)) / ((r : ℝ) * ((d : ℝ) + 1))

end Qatlib.Papers.ClassShadows20.LowerBound
