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
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.SqEstimation.InnerProduct

set_option autoImplicit false
set_option warningAsError false

namespace Qatlib.Concepts.SketchSpectral.SketchAnalysis
namespace ConstructionStageB
namespace StageBSQSKETCHARITHMETIC

open Matrix
open Qatlib
open scoped Classical BigOperators Matrix.Norms.Frobenius Matrix.Norms.L2Operator

noncomputable section

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

def sqRowSketch {K C : Type} [Fintype K] [Fintype C] (A : Matrix K C ℂ) (p : FinDist K)
    (r : ℕ) (ω : Fin r → K) : Matrix (Fin r) C ℂ :=
  compactSketched (compactSketchData p r ω) A

def sqUnifiedRate (φ ε δ : ℝ) : ℝ := φ ^ 2 * Real.log (4 / δ) / ε ^ 2

def sqRowStageSamples (ε δ E : ℝ) : ℝ :=
  32 * Real.log (2 / (δ / 2)) * E ^ 2 / ε ^ 2

def sqColStageSamples (φ ε δ E : ℝ) : ℝ :=
  32 * φ ^ 2 * Real.log (2 / (δ / 2)) * E ^ 2 / ε ^ 2

def sqUnifiedSampleCount (φ ε δ E : ℝ) : ℝ :=
  sqRowStageSamples ε δ E + sqColStageSamples φ ε δ E

def sqRowStageScale (δ : ℝ) (r : ℕ) : ℝ :=
  Real.sqrt (8 * Real.log (2 / (δ / 2)) / (r : ℝ))

def sqColStageScale (φ δ : ℝ) (c : ℕ) : ℝ :=
  Real.sqrt (8 * φ ^ 2 * Real.log (2 / (δ / 2)) / (c : ℝ))

structure SqConditionalAccess {K C : Type} [Fintype K] [Fintype C]
    (A : Matrix K C ℂ) (p : FinDist K) (r : ℕ) (φ : ℝ) where

  law : (Fin r → K) → FinDist C

  dominates : ∀ v k, sketchRowSquared (sqRowSketch A p r v)ᴴ k
      / (φ * sketchSquared (sqRowSketch A p r v)ᴴ) ≤ (law v).prob k

def sqSketchRuntime (r c perSample : ℕ) : ℕ := (r + c) * perSample

def sqSketchFunction {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℂ}
    (hA : A.IsHermitian) (f : ℝ → ℂ) : Matrix I I ℂ :=
  hermitianFunction A hA f

def sqRowSamplingCost (n r : ℕ) : ℕ := n * r

def sqRowSamplingWorkspace (r : ℕ) : ℕ := r

def sqInputSamplingLaw {X : Type} [Fintype X] (a : FiniteSQInput X) : FinDist X :=
  a.samples

end

end StageBSQSKETCHARITHMETIC
