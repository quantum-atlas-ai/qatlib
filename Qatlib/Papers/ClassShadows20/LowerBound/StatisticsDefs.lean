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

/-!
# Finite statistics and resource records

This module defines data records for finite designs, packing parameters, shot budgets,
higher-order kernels, pilot sampling, feedback, and statistical resources. Their predicates
specify the stated positivity, parameter, and design conditions. The final definitions express
irrationality of the square root of two and elementary distinctions between arithmetic counts,
bit time, table cells, and peak space.

These constructions support the treatment in [HuangKuengPreskill2020].

## Main statements

* `FiniteDesign.Correct`: requires unitary members and the chosen overlap-design degree.
* `ShotBudget.LogDeltaOptimal`: specifies a logarithmic lower bound on shots.
* `peakSpaceOf`: computes a finite live-word maximum times the word length.

## References

* [Huang et al., 2020][HuangKuengPreskill2020]
-/

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

/-- A finite indexed family of dimension-`d` operators with a specified design degree. -/
structure FiniteDesign (d : ℕ) where

  size : ℕ

  members : Fin size → Operator d

  degree : ℕ

/-- The condition that all members of a finite design are unitary and satisfy `IsOverlapDesign`
at its recorded degree. -/
def FiniteDesign.Correct {d : ℕ} (D : FiniteDesign d) : Prop :=
  (∀ i : Fin D.size, D.members i ∈ Matrix.unitaryGroup (Fin d) ℂ) ∧
    IsOverlapDesign d D.degree (fun i : Fin D.size => D.members i)

/-- A parameter record containing a natural number `M` and a real value `δ`. -/
structure PackingCertificate (d : ℕ) where

  M : ℕ

  δ : ℝ

/-- The condition that the recorded `M` and `δ` are both positive. -/
def PackingCertificate.Correct {d : ℕ} (p : PackingCertificate d) : Prop :=
  0 < p.M ∧ 0 < p.δ

/-- A record pairing packing parameters with a natural-number shot count. -/
structure Theorem5Wrapper (d : ℕ) where

  pack : PackingCertificate d

  shots : ℕ

/-- The condition that the packing parameters satisfy their correctness predicate and the shot
count is positive. -/
def Theorem5Wrapper.Correct {d : ℕ} (w : Theorem5Wrapper d) : Prop :=
  PackingCertificate.Correct w.pack ∧ 0 < w.shots

/-- A record containing a real constant and a natural-number family label. -/
structure SharpConstantLedger where

  C : ℝ

  family : ℕ

/-- The condition that the recorded real constant is positive. -/
def SharpConstantLedger.Correct (L : SharpConstantLedger) : Prop := 0 < L.C

/-- A record containing a real confidence parameter and a natural-number shot count. -/
structure ShotBudget where

  δ : ℝ

  shots : ℕ

/-- The condition that the confidence parameter lies strictly between zero and one and the shot
count is positive. -/
def ShotBudget.Correct (b : ShotBudget) : Prop :=
  0 < b.δ ∧ b.δ < 1 ∧ 0 < b.shots

/-- The condition that the shot count is at least the natural-number ceiling of `log (1 / δ)`. -/
def ShotBudget.LogDeltaOptimal (b : ShotBudget) : Prop :=
  b.shots ≥ Nat.ceil (Real.log (1 / b.δ))

/-- A record containing a sample size, an order, and a real-valued list kernel. -/
structure HigherOrderTransport (X : Type*) [Fintype X] where

  m : ℕ

  r : ℕ

  h : List X → ℝ

/-- The condition that the sample size is positive and the order is at most the sample size. -/
def HigherOrderTransport.Correct {X : Type*} [Fintype X]
    (t : HigherOrderTransport X) : Prop :=
  0 < t.m ∧ t.r ≤ t.m

/-- A record containing a pilot sample count, a natural-number parameter `h`, and a
rational-valued input function. -/
structure PilotBudget (I : Type*) where

  N : ℕ

  h : ℕ

  f : I → ℚ

/-- The condition that the pilot count `N` and the parameter `h` are both positive. -/
def PilotBudget.Correct {I : Type*} (p : PilotBudget I) : Prop :=
  0 < p.N ∧ 0 < p.h

/-- A record containing a natural-number parameter `k` and a real acceptance value. -/
structure MixedFeedback where

  k : ℕ

  accept : ℝ

/-- The condition that `k` is positive and the acceptance value lies between zero and one,
inclusively. -/
def MixedFeedback.Correct (x : MixedFeedback) : Prop :=
  0 < x.k ∧ 0 ≤ x.accept ∧ x.accept ≤ 1

/-- A record of input length, bit time, and peak space in bits. -/
structure StatResources where

  inputLen : ℕ

  bitTime : ℕ

  peakBits : ℕ

/-- A resource family has one polynomial bound in its input-size index. -/
def StatResources.PolyBounded (R : ℕ → StatResources) : Prop :=
  ∃ c e : ℕ, ∀ n : ℕ,
    (R n).bitTime ≤ c * (n + 1) ^ e ∧ (R n).peakBits ≤ c * (n + 1) ^ e

/-- The proposition that no rational number, cast to the reals, has square two. -/
def nativeRationalNotRealRamSqrt : Prop := ∀ q : ℚ, (q : ℝ) ^ 2 ≠ 2

/-- The proposition that for any two natural-number counts there exists a bit-time value unequal
to either count. -/
def macroCountsNotBitComplexity : Prop :=
  ∀ (macros arith : ℕ), ∃ bitTime : ℕ, bitTime ≠ macros ∧ bitTime ≠ arith

/-- The maximum live-word count among the first `events` indices, starting from zero, multiplied
by `wordLen`. -/
def peakSpaceOf (wordLen events : ℕ) (live : ℕ → ℕ) : ℕ :=
  (List.range events).foldr (fun i acc => max (live i) acc) 0 * wordLen

/-- The proposition that for every cell count there exist a word length and finite live-word
profile whose computed peak space differs from that count. -/
def tableCellsNotPeakSpace : Prop :=
  ∀ (cells : ℕ), ∃ (wordLen events : ℕ) (live : ℕ → ℕ),
    peakSpaceOf wordLen events live ≠ cells

end Qatlib.Papers.ClassShadows20.LowerBound
