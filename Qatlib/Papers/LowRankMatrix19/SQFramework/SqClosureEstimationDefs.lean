/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Field
import Qatlib.Concepts.SketchArith.SketchBuild.CompactImportanceSketch
import Qatlib.Concepts.SketchArith.SketchBuild.SketchFrobeniusConcentration
import Qatlib.Concepts.MonteCarloMean.PilotVariance.UnknownVariancePilot
import Qatlib.Concepts.SqEstimation.RejectionSample.SQRejectionAndNorm
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.SketchSpectral.EvenSVT.Numerics
import Qatlib.Concepts.SketchSpectral.SketchAnalysis.SketchArithmetic
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.SketchSpectral.EvenSVT.ConstructionStageB.StageBSQNUMERICS
open Qatlib.Concepts.SketchSpectral.SketchAnalysis.ConstructionStageB.StageBSQSKETCHARITHMETIC

set_option autoImplicit false
set_option warningAsError false

namespace Qatlib.Papers.LowRankMatrix19.SQFramework
namespace ConstructionStageB
namespace StageBSQCLOSUREESTIMATION

open Matrix
open Qatlib
open scoped Classical BigOperators Matrix.Norms.Frobenius

noncomputable section

def sqPilotEnergy {K C : Type} [Fintype K] [Fintype C] (A : Matrix K C ℂ) (p : FinDist K)
    (r : ℕ) (ω : Fin r → K) : ℝ :=
  sketchSquared (sqRowSketch A p r ω)

def sqPilotScale (φ δ : ℝ) (r : ℕ) : ℝ :=
  Real.sqrt (φ ^ 2 * Real.log (2 / δ) / (2 * (r : ℝ)))

def sqPilotUpperEstimate (ê c : ℝ) : ℝ := ê / (1 - c)

def sqPilotSampleCount (ê c L ε φ δ : ℝ) (rank : ℕ) : ℝ :=
  32 * φ ^ 2 * Real.log (2 / (δ / 3)) * (L * rankLogFactor rank) ^ 2
    * (ê / (1 - c)) ^ 2 / ε ^ 2

def aliasTotal {n : ℕ} (w : Fin n → ℕ) : ℕ := ∑ i, w i

def aliasLaw {n : ℕ} (w : Fin n → ℕ) (W : ℕ) (hW : 0 < W) (h : aliasTotal w = W) :
    FinDist (Fin n) where
  prob := fun i => (w i : ℝ) / W
  nonneg := fun _ => by positivity
  sum_one := by
    have h1 : (∑ i, (w i : ℝ)) = (W : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast h
    have h2 : (∑ i, (w i : ℝ) / W) = (∑ i, (w i : ℝ)) / W := by
      symm
      exact Finset.sum_div _ _ _
    rw [h2, h1]
    have hne : (W : ℝ) ≠ 0 := by
      have hpos : (0 : ℝ) < W := by exact_mod_cast hW
      exact ne_of_gt hpos
    exact div_self hne

def aliasPreprocessCost (n : ℕ) : ℕ := 2 * n + 1

def aliasSpaceCost (n : ℕ) : ℕ := n

def aliasDrawCost : ℕ := 1

def aliasTotalCost (n q : ℕ) : ℕ := aliasPreprocessCost n + q * aliasDrawCost

def sqClosureLedger (n r c q : ℕ) : SqBitLedger := sketchArithmeticLedger n r c q

def sqClosureFairBits (draws : ℕ) : ℕ := draws

def sqClosureFixedPrecision (p : ℕ) : ℕ := p

end

end StageBSQCLOSUREESTIMATION
