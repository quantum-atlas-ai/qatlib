/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchArith.SketchBuild.CompactImportanceSketch
import Qatlib.Concepts.SqEstimation.InnerProduct.FiniteSQAccess
import Qatlib.Concepts.SketchSpectral.SketchAnalysis.SketchOperatorConcentration
import Qatlib.Concepts.WalkSearch.Spectral.Approximation
import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.HermitianFunctionStability
import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation
import Qatlib.Concepts.RandCompile.ChannelBudget.SingularValues
import Qatlib.Concepts.SketchSpectral.EvenSVT.TruncatedSketchSecondIsometryStat
import Qatlib.Concepts.SketchSpectral.EvenSVT.ThresholdRankRetentionStat
import Qatlib.Concepts.SketchSpectral.EvenSVT.TruncatedSketchSecondIsometrySamp
import Qatlib.Concepts.SketchSpectral.EvenSVT.ThresholdRankRetentionSamp
import Qatlib.Concepts.SketchSpectral.SketchAnalysis.SketchArithmetic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Matrix-function sample and cost expressions

This module defines sample rates, error budgets, output matrices, and access-cost ledgers for
sampling-based matrix-function constructions. These expressions organize parameters from the
low-rank matrix arithmetic framework of [ChiaEtAl2022]. Real-valued sample expressions are kept
separate from the natural-valued counts in `Lemma49Ledger`.

## Main definitions

* `lemma49SampleRate` and `Lemma49Ledger`: sample rates and their access ledger.
* `lemma414SecondIsometryResidual`: the retained-coordinate isometry residual.
* `classicalOutput`: the lifted matrix-function output.
* `th71RowSamples` and `th72RowSamples`: parameterized row sample expressions.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.SketchSpectral.EvenSVT
open Qatlib.Concepts.SketchSpectral.SketchAnalysis
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.SketchSpectral.EvenSVT.ConstructionStageB.StageBSQNUMERICS.SqBitLedger
open Qatlib.Concepts.SketchSpectral.SketchAnalysis.ConstructionStageB.StageBSQSKETCHARITHMETIC

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace Qatlib.Concepts.SketchSpectral.MatrixFunctions
namespace ConstructionStageB
namespace StageBSQMATRIXFUNCTION

open Matrix
open Qatlib
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The real-valued sample rate φ² log(1 / δ) / ε². -/
def lemma49SampleRate (φ ε δ : ℝ) : ℝ := φ ^ 2 * Real.log (1 / δ) / ε ^ 2

/-- The row sample expression, equal to `lemma49SampleRate`. -/
def lemma49RowSamples (φ ε δ : ℝ) : ℝ := lemma49SampleRate φ ε δ

/-- The column sample expression, equal to `lemma49SampleRate`. -/
def lemma49ColSamples (φ ε δ : ℝ) : ℝ := lemma49SampleRate φ ε δ

/-- The sum of the row and column sample expressions. -/
def lemma49TotalSamples (φ ε δ : ℝ) : ℝ :=
  lemma49RowSamples φ ε δ + lemma49ColSamples φ ε δ

/-- The Frobenius error target ε times the squared Frobenius norm parameter. -/
def lemma49FrobeniusTarget (ε normAF : ℝ) : ℝ := ε * normAF ^ 2

/-- The multiplicative sample budget condition φ² log(1 / δ) ≤ ε²r. -/
def lemma49SampleBudgetMul (φ ε δ : ℝ) (r : ℕ) : Prop :=
  φ ^ 2 * Real.log (1 / δ) ≤ ε ^ 2 * (r : ℝ)

/-- The total row and column sample count multiplied by the cost per sample. -/
def lemma49SketchTime (r c perSample : ℕ) : ℕ := (r + c) * perSample

/-- A ledger recording the row sample count, column sample count, and cost per sample. -/
structure Lemma49Ledger where

  rowSamples : ℕ

  colSamples : ℕ

  perSample : ℕ
  deriving DecidableEq, Repr

/-- The number of sampler reads recorded by the ledger, equal to the total sample count. -/
def Lemma49Ledger.samplerReads (l : Lemma49Ledger) : ℕ := l.rowSamples + l.colSamples

/-- The number of probability reads recorded by the ledger, equal to the total sample count. -/
def Lemma49Ledger.probReads (l : Lemma49Ledger) : ℕ := l.rowSamples + l.colSamples

/-- The sketch runtime calculated from the ledger's sample counts and per-sample cost. -/
def Lemma49Ledger.runtime (l : Lemma49Ledger) : ℕ :=
  lemma49SketchTime l.rowSamples l.colSamples l.perSample

/-- The row sample expression φ² normA² normAF² log(1 / δ) / σk⁴ for the truncated sketch
construction. -/
def lemma414RowSamples (φ normA normAF σk δ : ℝ) : ℝ :=
  φ ^ 2 * normA ^ 2 * normAF ^ 2 / σk ^ 4 * Real.log (1 / δ)

/-- The column sample expression φ² normA² normAF² log(1 / δ) / (σk⁴α²) for the truncated sketch
construction. -/
def lemma414ColSamples (φ normA normAF σk α δ : ℝ) : ℝ :=
  φ ^ 2 * normA ^ 2 * normAF ^ 2 / (σk ^ 4 * α ^ 2) * Real.log (1 / δ)

/-- The combined squared-singular-value error budget 2η₁ + 2η₂. -/
def lemma414CutoffBudget (η₁ η₂ : ℝ) : ℝ := 2 * η₁ + 2 * η₂

/-- The second Gram error divided by the isometry error parameter, η₂ / α. -/
def lemma414IsometryBudget (η₂ α : ℝ) : ℝ := η₂ / α

/-- The square root of the squared singular value parameter minus the cutoff error budget. -/
def lemma414Cutoff (σk η₁ η₂ : ℝ) : ℝ :=
  Real.sqrt (σk ^ 2 - lemma414CutoffBudget η₁ η₂)

/-- The retained singular-coordinate Gram matrix obtained by rescaling `R * Rᴴ` with thresholded
reciprocal singular values of `Cc`, minus the retained-coordinate projector. -/
def lemma414SecondIsometryResidual {C RS CT : Type} [Fintype C] [DecidableEq C]
    [Fintype RS] [DecidableEq RS] [Fintype CT] [DecidableEq CT]
    (R : Matrix RS C ℂ) (Cc : Matrix RS CT ℂ) (τ : ℝ) :
    Matrix (Fin (Fintype.card RS)) (Fin (Fintype.card RS)) ℂ :=
  Matrix.diagonal
      (fun i : Fin (Fintype.card RS) =>
        if τ ≤ matrixSingularValues Cc i
        then ((matrixSingularValues Cc i)⁻¹ : ℂ) else 0) *
    (basisColumns (rightSingularBasis Ccᴴ))ᴴ *
    R * Rᴴ *
    basisColumns (rightSingularBasis Ccᴴ) *
    (Matrix.diagonal
      (fun i : Fin (Fintype.card RS) =>
        if τ ≤ matrixSingularValues Cc i
        then ((matrixSingularValues Cc i)⁻¹ : ℂ) else 0))ᴴ -
    Matrix.diagonal
      (fun i : Fin (Fintype.card RS) =>
        if τ ≤ matrixSingularValues Cc i then (1 : ℂ) else 0)

/-- The column-to-row sample ratio expression 1 / α². -/
def lemma414ColOverRowRatio (α : ℝ) : ℝ := 1 / α ^ 2

/-- The probability mass of the compact first Gram operator error event at threshold `η`. -/
def firstGramBadMass {K C : Type} [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    (p : FinDist K) (r : ℕ) (A : Matrix K C ℂ) (η : ℝ) : ℝ :=
  Qatlib.Concepts.SketchSpectral.SketchAnalysis.compactGramOperatorBadMass p r A η

/-- The first Gram tail scale sqrt(8φ² log(2 / (δ / 2)) / r) times `E`. -/
def firstGramTailScale (φ δ : ℝ) (r : ℕ) (E : ℝ) : ℝ :=
  Real.sqrt (8 * φ ^ 2 * Real.log (2 / (δ / 2)) / (r : ℝ)) * E

/-- The interval length b - a used in the operator perturbation logarithm. -/
def lemma55OperatorRange (a b : ℝ) : ℝ := b - a

/-- The logarithmic factor log(e(b - a) / diff) for the operator perturbation parameters. -/
def lemma55LogFactor (a b diff : ℝ) : ℝ :=
  Real.log (Real.exp 1 * (lemma55OperatorRange a b / diff))

/-- The logarithm of the smaller of the two rank parameters. -/
def lemma56RankLog (rankA rankB : ℕ) : ℝ := Real.log (min rankA rankB)

/-- The logarithm of the minimum of the two ranks and the auxiliary rank parameter `m`. -/
def lemma56RankLogLower (rankA rankB m : ℕ) : ℝ := Real.log (min (min rankA rankB) m)

/-- The matrix RᴴuR plus `f0` times the identity, representing the classical matrix-function
output. -/
def classicalOutput {C RS : Type} [Fintype C] [DecidableEq C]
    [Fintype RS] [DecidableEq RS]
    (f0 : ℂ) (R : Matrix RS C ℂ)
    (u : Matrix RS RS ℂ) : Matrix C C ℂ :=
  Rᴴ * u * R + f0 • (1 : Matrix C C ℂ)

/-- The output sampling and query count r + c. -/
def outputSqQueries (r c : ℕ) : ℕ := r + c

/-- The output RAM operation count nr + r² + cr. -/
def outputRamOps (r c n : ℕ) : ℕ := n * r + r * r + c * r

/-- The output RAM operation count multiplied by the word size `w`. -/
def outputBitTime (r c n w : ℕ) : ℕ := w * (outputRamOps r c n)

/-- The real-valued iteration expression log(1 / ε) for numerical SVD. -/
def numericalSvdIterations (ε : ℝ) : ℝ := Real.log (1 / ε)

/-- The relative error parameter for numerical SVD, defined to be `ε`. -/
def numericalSvdRelativeError (ε : ℝ) : ℝ := ε

/-- The real-valued ratio k / m of the frame parameters. -/
def framePower (k m : ℕ) : ℝ := (k : ℝ) / (m : ℝ)

/-- The phase evaluation cost, equal to `r`. -/
def phaseEvaluationCost (r : ℕ) : ℕ := r

/-- The quadratic function evaluation cost s². -/
def functionEvaluationCost (s : ℕ) : ℕ := s * s

/-- The backend query cost r + c + s². -/
def backendQueryCost (r c s : ℕ) : ℕ := r + c + functionEvaluationCost s

/-- The backend RAM word count r + c + s + n. -/
def backendRamWords (r c s n : ℕ) : ℕ := r + c + s + n

/-- The backend RAM word count multiplied by the word size `w`. -/
def backendBitTime (r c s n w : ℕ) : ℕ := w * (backendRamWords r c s n)

/-- The row sample expression φ²L² normA² normAF⁴ log(1 / δ) / ε². -/
def th71RowSamples (φ L normA normAF ε δ : ℝ) : ℝ :=
  φ ^ 2 * L ^ 2 * normA ^ 2 * normAF ^ 4 / ε ^ 2 * Real.log (1 / δ)

/-- The column sample expression φ²L² normA⁴ normAF² log(1 / δ) / ε². -/
def th71ColSamples (φ L normA normAF ε δ : ℝ) : ℝ :=
  φ ^ 2 * L ^ 2 * normA ^ 4 * normAF ^ 2 / ε ^ 2 * Real.log (1 / δ)

/-- The row sample expression φ² normA⁴ normAF²L⁶ log(1 / δ) / ε⁶. -/
def th72RowSamples (φ L normA normAF ε δ : ℝ) : ℝ :=
  φ ^ 2 * normA ^ 4 * normAF ^ 2 * L ^ 6 / ε ^ 6 * Real.log (1 / δ)

/-- The rank sample expression normAF²L² / ε². -/
def th72RankSamples (L normAF ε : ℝ) : ℝ := normAF ^ 2 * L ^ 2 / ε ^ 2

/-- The Markov-based row sample expression φ² normAF⁴ log(1 / δ) / ε². -/
def markovRowSamples (φ normAF ε δ : ℝ) : ℝ :=
  φ ^ 2 * normAF ^ 4 / ε ^ 2 * Real.log (1 / δ)

/-- The operator-based row sample expression, defined by `lemma414RowSamples`. -/
def opOptimalRowSamples (φ normA normAF σk δ : ℝ) : ℝ :=
  lemma414RowSamples φ normA normAF σk δ

/-- The quantum machine learning application sample expression, defined by `th71RowSamples`. -/
def qmlApplicationSamples (φ L normA normAF ε δ : ℝ) : ℝ :=
  th71RowSamples φ L normA normAF ε δ

/-- The matrix multiplicative weights application sample expression, defined by
`th71ColSamples`. -/
def mmwApplicationSamples (φ L normA normAF ε δ : ℝ) : ℝ :=
  th71ColSamples φ L normA normAF ε δ

/-- The semidefinite programming application sample expression, defined by `th72RowSamples`. -/
def sdpApplicationSamples (φ L normA normAF ε δ : ℝ) : ℝ :=
  th72RowSamples φ L normA normAF ε δ

end StageBSQMATRIXFUNCTION
end ConstructionStageB
end Qatlib.Concepts.SketchSpectral.MatrixFunctions
