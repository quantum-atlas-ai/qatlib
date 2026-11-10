/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Map

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace Qatlib.Papers.LatentPQCTran26.MainResults

def coupling {X : Type*} [MeasurableSpace X] (μ ν : Measure X) : Set (Measure (X × X)) :=
  {γ | γ.map Prod.fst = μ ∧ γ.map Prod.snd = ν}

def wasserstein1 {X : Type*} [MeasurableSpace X] [MetricSpace X]
    (μ ν : Measure X) : ℝ :=
  sInf {c : ℝ | ∃ γ : Measure (X × X), γ ∈ coupling μ ν ∧
    (∫ p, dist p.1 p.2 ∂γ) ≤ c}

def atomicMeasure {X : Type*} [MeasurableSpace X] {N : ℕ}
    (q : Fin N → NNReal) (ρ : Fin N → X) : Measure X :=
  ∑ i, q i • Measure.dirac (ρ i)

def pushforward {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    (r : Measure Z) (ρ : Z → X) : Measure X :=
  r.map ρ

end Qatlib.Papers.LatentPQCTran26.MainResults
