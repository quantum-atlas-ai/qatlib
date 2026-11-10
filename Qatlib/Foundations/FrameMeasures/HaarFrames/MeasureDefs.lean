/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.BornMetrics.FiniteStats.Defs

set_option autoImplicit false
noncomputable section
open MeasureTheory
open Qatlib.Foundations.BornMetrics.FiniteStats
open scoped BigOperators
namespace Qatlib.Foundations.FrameMeasures.HaarFrames

def normalizeByMass {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α) :
    MeasureTheory.Measure α := (μ Set.univ)⁻¹ • μ

def sphereProb (m : ℕ) :
    MeasureTheory.Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin (2 * m))) 1) :=
  normalizeByMass (MeasureTheory.Measure.toSphere (volume : MeasureTheory.Measure
    (EuclideanSpace ℝ (Fin (2 * m)))))

def simplexProb (N : ℕ) : MeasureTheory.Measure (simplex N) :=
  normalizeByMass (MeasureTheory.Measure.hausdorffMeasure ((N - 1 : ℕ) : ℝ))

end Qatlib.Foundations.FrameMeasures.HaarFrames
