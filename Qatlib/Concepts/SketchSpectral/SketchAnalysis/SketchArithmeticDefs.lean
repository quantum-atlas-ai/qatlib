/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Polynomial.Module.AEval
import Qatlib.Concepts.SketchArith.SketchBuild.CompactImportanceSketch
import Qatlib.Concepts.SketchArith.SketchBuild.SketchFrobeniusConcentration
import Qatlib.Concepts.SqEstimation.InnerProduct.FiniteSQAccess
import Qatlib.Concepts.SketchSpectral.EvenSvtLaw.EvenSVTFrobeniusRecordTools
import Qatlib.Concepts.SketchSpectral.EvenSVT.NumericsDefs

/-!
# Definitions for two-stage sketch arithmetic

This module defines the row energy sampling law, compact row sketches, and conditional column
access used in two-stage matrix sampling. The sample and runtime expressions support the
low-rank arithmetic framework of [ChiaEtAl2022]. `SqConditionalAccess` records the domination
condition for the second-stage sampling distributions.

## Main definitions

* `energySamplingLaw` and `sqRowSketch`: energy sampling and its rescaled row sketch.
* `sqUnifiedSampleCount`: the combined row and column sample expression.
* `sqSketchFunction`: Hermitian functional calculus for the sketch analysis.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.SqEstimation.InnerProduct

set_option autoImplicit false

namespace Qatlib.Concepts.SketchSpectral.SketchAnalysis
namespace ConstructionStageB
namespace StageBSQSKETCHARITHMETIC

open Matrix
open Qatlib
open scoped Classical BigOperators Matrix.Norms.Frobenius Matrix.Norms.L2Operator

noncomputable section

/-- The finite row distribution assigning each row its squared energy divided by the positive
total matrix energy. -/
def energySamplingLaw {K C : Type} [Fintype K] [Fintype C] (A : Matrix K C ℂ)
    (hA : 0 < sketchSquared A) : FinDist K where
  prob := fun k => sketchRowSquared A k / sketchSquared A
  nonneg := fun _ => div_nonneg (sketchRowSquared_nonneg A _) (le_of_lt hA)
  sum_one := by
    have h1 : (∑ x, sketchRowSquared A x) = sketchSquared A := rfl
    have h2 : (∑ x, sketchRowSquared A x / sketchSquared A)
        = (∑ x, sketchRowSquared A x) / sketchSquared A := by
      symm
      exact Finset.sum_div _ _ _
    rw [h2, h1]
    exact div_self hA.ne'

/-- The compact rescaled row sketch associated with the sample tuple `ω` and row sampling
distribution `p`. -/
def sqRowSketch {K C : Type} [Fintype K] [Fintype C] (A : Matrix K C ℂ) (p : FinDist K)
    (r : ℕ) (ω : Fin r → K) : Matrix (Fin r) C ℂ :=
  compactSketched (compactSketchData p r ω) A

/-- The unified sample rate φ² log(4 / δ) / ε². -/
def sqUnifiedRate (φ ε δ : ℝ) : ℝ := φ ^ 2 * Real.log (4 / δ) / ε ^ 2

/-- The first-stage sample expression 32 log(2 / (δ / 2)) E² / ε². -/
def sqRowStageSamples (ε δ E : ℝ) : ℝ :=
  32 * Real.log (2 / (δ / 2)) * E ^ 2 / ε ^ 2

/-- The second-stage sample expression 32φ² log(2 / (δ / 2)) E² / ε². -/
def sqColStageSamples (φ ε δ E : ℝ) : ℝ :=
  32 * φ ^ 2 * Real.log (2 / (δ / 2)) * E ^ 2 / ε ^ 2

/-- The sum of the row-stage and column-stage sample expressions. -/
def sqUnifiedSampleCount (φ ε δ E : ℝ) : ℝ :=
  sqRowStageSamples ε δ E + sqColStageSamples φ ε δ E

/-- The first-stage concentration scale sqrt(8 log(2 / (δ / 2)) / r). -/
def sqRowStageScale (δ : ℝ) (r : ℕ) : ℝ :=
  Real.sqrt (8 * Real.log (2 / (δ / 2)) / (r : ℝ))

/-- The second-stage concentration scale sqrt(8φ² log(2 / (δ / 2)) / c). -/
def sqColStageScale (φ δ : ℝ) (c : ℕ) : ℝ :=
  Real.sqrt (8 * φ ^ 2 * Real.log (2 / (δ / 2)) / (c : ℝ))

/-- Conditional column sampling distributions for each row sample tuple, together with
domination of normalized column energies by the oversampling factor `φ`. -/
structure SqConditionalAccess {K C : Type} [Fintype K] [Fintype C]
    (A : Matrix K C ℂ) (p : FinDist K) (r : ℕ) (φ : ℝ) where

  law : (Fin r → K) → FinDist C

  dominates : ∀ v k, sketchRowSquared (sqRowSketch A p r v)ᴴ k
      / (φ * sketchSquared (sqRowSketch A p r v)ᴴ) ≤ (law v).prob k

/-- The total row and column sample count times the cost per sample. -/
def sqSketchRuntime (r c perSample : ℕ) : ℕ := (r + c) * perSample

/-- Hermitian functional calculus used for the sampling and query sketch construction. -/
def sqSketchFunction {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℂ) : Matrix I I ℂ :=
  hermitianFunction A hA f

/-- The row sampling cost nr for dimension `n` and sample count `r`. -/
def sqRowSamplingCost (n r : ℕ) : ℕ := n * r

/-- The row sampling workspace word count, equal to the number `r` of sampled rows. -/
def sqRowSamplingWorkspace (r : ℕ) : ℕ := r

/-- The stored sampling distribution of a finite sampling and query input. -/
def sqInputSamplingLaw {X : Type} [Fintype X] (a : FiniteSQInput X) : FinDist X :=
  a.samples

end

end StageBSQSKETCHARITHMETIC
