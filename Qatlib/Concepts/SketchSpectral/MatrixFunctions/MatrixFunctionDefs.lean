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

def lemma49SampleRate (φ ε δ : ℝ) : ℝ := φ ^ 2 * Real.log (1 / δ) / ε ^ 2

def lemma49RowSamples (φ ε δ : ℝ) : ℝ := lemma49SampleRate φ ε δ

def lemma49ColSamples (φ ε δ : ℝ) : ℝ := lemma49SampleRate φ ε δ

def lemma49TotalSamples (φ ε δ : ℝ) : ℝ :=
  lemma49RowSamples φ ε δ + lemma49ColSamples φ ε δ

def lemma49FrobeniusTarget (ε normAF : ℝ) : ℝ := ε * normAF ^ 2

def lemma49SampleBudgetMul (φ ε δ : ℝ) (r : ℕ) : Prop :=
  φ ^ 2 * Real.log (1 / δ) ≤ ε ^ 2 * (r : ℝ)

def lemma49SketchTime (r c perSample : ℕ) : ℕ := (r + c) * perSample

structure Lemma49Ledger where

  rowSamples : ℕ

  colSamples : ℕ

  perSample : ℕ
  deriving DecidableEq, Repr

def Lemma49Ledger.samplerReads (l : Lemma49Ledger) : ℕ := l.rowSamples + l.colSamples

def Lemma49Ledger.probReads (l : Lemma49Ledger) : ℕ := l.rowSamples + l.colSamples

def Lemma49Ledger.runtime (l : Lemma49Ledger) : ℕ :=
  lemma49SketchTime l.rowSamples l.colSamples l.perSample

def lemma414RowSamples (φ normA normAF σk δ : ℝ) : ℝ :=
  φ ^ 2 * normA ^ 2 * normAF ^ 2 / σk ^ 4 * Real.log (1 / δ)

def lemma414ColSamples (φ normA normAF σk α δ : ℝ) : ℝ :=
  φ ^ 2 * normA ^ 2 * normAF ^ 2 / (σk ^ 4 * α ^ 2) * Real.log (1 / δ)

def lemma414CutoffBudget (η₁ η₂ : ℝ) : ℝ := 2 * η₁ + 2 * η₂

def lemma414IsometryBudget (η₂ α : ℝ) : ℝ := η₂ / α

def lemma414Cutoff (σk η₁ η₂ : ℝ) : ℝ :=
  Real.sqrt (σk ^ 2 - lemma414CutoffBudget η₁ η₂)

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

def lemma414ColOverRowRatio (α : ℝ) : ℝ := 1 / α ^ 2

def firstGramBadMass {K C : Type} [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    (p : FinDist K) (r : ℕ) (A : Matrix K C ℂ) (η : ℝ) : ℝ :=
  Qatlib.Concepts.SketchSpectral.SketchAnalysis.compactGramOperatorBadMass p r A η

def firstGramTailScale (φ δ : ℝ) (r : ℕ) (E : ℝ) : ℝ :=
  Real.sqrt (8 * φ ^ 2 * Real.log (2 / (δ / 2)) / (r : ℝ)) * E

def lemma55OperatorRange (a b : ℝ) : ℝ := b - a

def lemma55LogFactor (a b diff : ℝ) : ℝ :=
  Real.log (Real.exp 1 * (lemma55OperatorRange a b / diff))

def lemma56RankLog (rankA rankB : ℕ) : ℝ := Real.log (min rankA rankB)

def lemma56RankLogLower (rankA rankB m : ℕ) : ℝ := Real.log (min (min rankA rankB) m)

def classicalOutput {C RS : Type} [Fintype C] [DecidableEq C]
    [Fintype RS] [DecidableEq RS]
    (f0 : ℂ) (R : Matrix RS C ℂ)
    (u : Matrix RS RS ℂ) : Matrix C C ℂ :=
  Rᴴ * u * R + f0 • (1 : Matrix C C ℂ)

def outputSqQueries (r c : ℕ) : ℕ := r + c

def outputRamOps (r c n : ℕ) : ℕ := n * r + r * r + c * r

def outputBitTime (r c n w : ℕ) : ℕ := w * (outputRamOps r c n)

def numericalSvdIterations (ε : ℝ) : ℝ := Real.log (1 / ε)

def numericalSvdRelativeError (ε : ℝ) : ℝ := ε

def framePower (k m : ℕ) : ℝ := (k : ℝ) / (m : ℝ)

def phaseEvaluationCost (r : ℕ) : ℕ := r

def functionEvaluationCost (s : ℕ) : ℕ := s * s

def backendQueryCost (r c s : ℕ) : ℕ := r + c + functionEvaluationCost s

def backendRamWords (r c s n : ℕ) : ℕ := r + c + s + n

def backendBitTime (r c s n w : ℕ) : ℕ := w * (backendRamWords r c s n)

def th71RowSamples (φ L normA normAF ε δ : ℝ) : ℝ :=
  φ ^ 2 * L ^ 2 * normA ^ 2 * normAF ^ 4 / ε ^ 2 * Real.log (1 / δ)

def th71ColSamples (φ L normA normAF ε δ : ℝ) : ℝ :=
  φ ^ 2 * L ^ 2 * normA ^ 4 * normAF ^ 2 / ε ^ 2 * Real.log (1 / δ)

def th72RowSamples (φ L normA normAF ε δ : ℝ) : ℝ :=
  φ ^ 2 * normA ^ 4 * normAF ^ 2 * L ^ 6 / ε ^ 6 * Real.log (1 / δ)

def th72RankSamples (L normAF ε : ℝ) : ℝ := normAF ^ 2 * L ^ 2 / ε ^ 2

def markovRowSamples (φ normAF ε δ : ℝ) : ℝ :=
  φ ^ 2 * normAF ^ 4 / ε ^ 2 * Real.log (1 / δ)

def opOptimalRowSamples (φ normA normAF σk δ : ℝ) : ℝ :=
  lemma414RowSamples φ normA normAF σk δ

def qmlApplicationSamples (φ L normA normAF ε δ : ℝ) : ℝ :=
  th71RowSamples φ L normA normAF ε δ

def mmwApplicationSamples (φ L normA normAF ε δ : ℝ) : ℝ :=
  th71ColSamples φ L normA normAF ε δ

def sdpApplicationSamples (φ L normA normAF ε δ : ℝ) : ℝ :=
  th72RowSamples φ L normA normAF ε δ

end StageBSQMATRIXFUNCTION
end ConstructionStageB
end Qatlib.Concepts.SketchSpectral.MatrixFunctions
