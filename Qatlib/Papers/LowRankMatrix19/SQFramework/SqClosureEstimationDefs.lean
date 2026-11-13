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

/-!
# Pilot estimators and sample/query closure cost definitions

This module defines the pilot energy, deviation scale, upper estimate, and sample count used for
sample/query closure. It also defines normalized alias probabilities and separate preprocessing,
space, draw, ledger, and precision parameters for the framework of [ChiaEtAl2022].

## Main statements

* `sqPilotEnergy`: Takes the squared energy of a sampled row sketch.
* `aliasLaw`: Normalizes a natural-weight vector of positive total weight.
* `sqClosureLedger`: Uses the sketch arithmetic ledger for closure accounting.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.SketchSpectral.EvenSVT.ConstructionStageB.StageBSQNUMERICS
open Qatlib.Concepts.SketchSpectral.SketchAnalysis.ConstructionStageB.StageBSQSKETCHARITHMETIC

set_option autoImplicit false

namespace Qatlib.Papers.LowRankMatrix19.SQFramework
namespace ConstructionStageB
namespace StageBSQCLOSUREESTIMATION

open Matrix
open Qatlib
open scoped Classical BigOperators Matrix.Norms.Frobenius

noncomputable section

/-- The squared energy `sketchSquared` of the sampled row sketch `sqRowSketch A p r ω`. -/
def sqPilotEnergy {K C : Type} [Fintype K] [Fintype C] (A : Matrix K C ℂ) (p : FinDist K)
    (r : ℕ) (ω : Fin r → K) : ℝ :=
  sketchSquared (sqRowSketch A p r ω)

/-- The pilot deviation scale `sqrt (φ ^ 2 * log (2 / δ) / (2 * r))`. -/
def sqPilotScale (φ δ : ℝ) (r : ℕ) : ℝ :=
  Real.sqrt (φ ^ 2 * Real.log (2 / δ) / (2 * (r : ℝ)))

/-- The pilot upper-estimate expression `ê / (1 - c)`. -/
def sqPilotUpperEstimate (ê c : ℝ) : ℝ := ê / (1 - c)

/-- The pilot-driven sample-count expression with factor `32 * φ ^ 2 * log (2 / (δ / 3))`,
squared rank-Lipschitz and upper-estimate factors, and denominator `ε ^ 2`. -/
def sqPilotSampleCount (ê c L ε φ δ : ℝ) (rank : ℕ) : ℝ :=
  32 * φ ^ 2 * Real.log (2 / (δ / 3)) * (L * rankLogFactor rank) ^ 2
    * (ê / (1 - c)) ^ 2 / ε ^ 2

/-- The sum of the natural weights over all indices. -/
def aliasTotal {n : ℕ} (w : Fin n → ℕ) : ℕ := ∑ i, w i

/-- The finite probability distribution assigning probability `(w i : ℝ) / W` to each index,
given positive total weight `W`. -/
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

/-- The abstract alias preprocessing cost `2 * n + 1`. -/
def aliasPreprocessCost (n : ℕ) : ℕ := 2 * n + 1

/-- The abstract alias storage cost `n`. -/
def aliasSpaceCost (n : ℕ) : ℕ := n

/-- The unit abstract cost of one alias draw. -/
def aliasDrawCost : ℕ := 1

/-- The abstract total alias cost, equal to preprocessing cost plus the number of draws times
the draw cost. -/
def aliasTotalCost (n q : ℕ) : ℕ := aliasPreprocessCost n + q * aliasDrawCost

/-- The sketch arithmetic bit ledger reused for sample/query closure with parameters `n`, `r`,
`c`, and `q`. -/
def sqClosureLedger (n r c q : ℕ) : SqBitLedger := sketchArithmeticLedger n r c q

/-- The fair-bit accounting parameter equal to the supplied number of draws. -/
def sqClosureFairBits (draws : ℕ) : ℕ := draws

/-- The fixed-precision accounting parameter equal to the supplied precision `p`. -/
def sqClosureFixedPrecision (p : ℕ) : ℕ := p

end

end StageBSQCLOSUREESTIMATION
