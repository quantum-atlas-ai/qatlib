/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.ExecutionDefs
import Qatlib.Concepts.ShadowModels.ShadowChannel.QubitConjugationDesign
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.ShadowModels.UStatBackend.OrderedHigherUStatistic
import Qatlib.Concepts.MonteCarloMean.PilotVariance.UnknownVariancePilot
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedMean

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.PilotVariance
open Qatlib.Concepts.ShadowModels.UStatBackend
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.AmplitudeSearch.Amplification

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.ClassShadows20.LowerBound

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw Qatlib.Concepts.AmplitudeSearch.Amplification
open scoped Classical ENNReal

structure FiniteDesign (d : ℕ) where

  size : ℕ

  members : Fin size → Operator d

  degree : ℕ

def FiniteDesign.Correct {d : ℕ} (D : FiniteDesign d) : Prop :=
  (∀ i : Fin D.size, D.members i ∈ Matrix.unitaryGroup (Fin d) ℂ) ∧
    IsOverlapDesign d D.degree (fun i : Fin D.size => D.members i)

structure PackingCertificate (d : ℕ) where

  M : ℕ

  δ : ℝ

def PackingCertificate.Correct {d : ℕ} (p : PackingCertificate d) : Prop :=
  0 < p.M ∧ 0 < p.δ

structure Theorem5Wrapper (d : ℕ) where

  pack : PackingCertificate d

  shots : ℕ

def Theorem5Wrapper.Correct {d : ℕ} (w : Theorem5Wrapper d) : Prop :=
  PackingCertificate.Correct w.pack ∧ 0 < w.shots

structure SharpConstantLedger where

  C : ℝ

  family : ℕ

def SharpConstantLedger.Correct (L : SharpConstantLedger) : Prop := 0 < L.C

structure ShotBudget where

  δ : ℝ

  shots : ℕ

def ShotBudget.Correct (b : ShotBudget) : Prop :=
  0 < b.δ ∧ b.δ < 1 ∧ 0 < b.shots

def ShotBudget.LogDeltaOptimal (b : ShotBudget) : Prop :=
  b.shots ≥ Nat.ceil (Real.log (1 / b.δ))

structure HigherOrderTransport (X : Type*) [Fintype X] where

  m : ℕ

  r : ℕ

  h : List X → ℝ

def HigherOrderTransport.Correct {X : Type*} [Fintype X]
    (t : HigherOrderTransport X) : Prop :=
  0 < t.m ∧ t.r ≤ t.m

structure PilotBudget (I : Type*) where

  N : ℕ

  h : ℕ

  f : I → ℚ

def PilotBudget.Correct {I : Type*} (p : PilotBudget I) : Prop :=
  0 < p.N ∧ 0 < p.h

structure MixedFeedback where

  k : ℕ

  accept : ℝ

def MixedFeedback.Correct (x : MixedFeedback) : Prop :=
  0 < x.k ∧ 0 ≤ x.accept ∧ x.accept ≤ 1

structure StatResources where

  inputLen : ℕ

  bitTime : ℕ

  peakBits : ℕ

/-- A resource family has one polynomial bound in its input-size index. -/
def StatResources.PolyBounded (R : ℕ → StatResources) : Prop :=
  ∃ c e : ℕ, ∀ n : ℕ,
    (R n).bitTime ≤ c * (n + 1) ^ e ∧ (R n).peakBits ≤ c * (n + 1) ^ e

def nativeRationalNotRealRamSqrt : Prop := ∀ q : ℚ, (q : ℝ) ^ 2 ≠ 2

def macroCountsNotBitComplexity : Prop :=
  ∀ (macros arith : ℕ), ∃ bitTime : ℕ, bitTime ≠ macros ∧ bitTime ≠ arith

def peakSpaceOf (wordLen events : ℕ) (live : ℕ → ℕ) : ℕ :=
  (List.range events).foldr (fun i acc => max (live i) acc) 0 * wordLen

def tableCellsNotPeakSpace : Prop :=
  ∀ (cells : ℕ), ∃ (wordLen events : ℕ) (live : ℕ → ℕ),
    peakSpaceOf wordLen events live ≠ cells

end Qatlib.Papers.ClassShadows20.LowerBound
