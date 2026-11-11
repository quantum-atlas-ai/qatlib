/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Map

/-!
# Measures and transport costs for latent circuits

`coupling` specifies measures with given coordinate marginals, and `wasserstein1` takes the real
infimum of upper bounds on their integrated distance costs. The definitions `atomicMeasure` and
`pushforward` provide finite weighted catalogs and the distribution induced by a latent decoder.
See [TranEtAl2026] for the paper context.

## Main statements

* `coupling`: The set of measures on `X × X` whose first and second marginals are `μ` and `ν`.
* `wasserstein1`: The real infimum of upper bounds on integrated distance costs over measures
  coupling `μ` and `ν`.
* `atomicMeasure`: The finite measure sum of Dirac masses at `ρ i` with nonnegative weights `q
  i`.

## References

* [Tran et al., 2026][TranEtAl2026]
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace Qatlib.Papers.LatentPQCTran26.MainResults

/-- The set of measures on `X × X` whose first and second marginals are `μ` and `ν`. -/
def coupling {X : Type*} [MeasurableSpace X] (μ ν : Measure X) : Set (Measure (X × X)) :=
  {γ | γ.map Prod.fst = μ ∧ γ.map Prod.snd = ν}

/-- The real infimum of upper bounds on integrated distance costs over measures coupling `μ` and
`ν`. -/
def wasserstein1 {X : Type*} [MeasurableSpace X] [MetricSpace X]
    (μ ν : Measure X) : ℝ :=
  sInf {c : ℝ | ∃ γ : Measure (X × X), γ ∈ coupling μ ν ∧
    (∫ p, dist p.1 p.2 ∂γ) ≤ c}

/-- The finite measure sum of Dirac masses at `ρ i` with nonnegative weights `q i`. -/
def atomicMeasure {X : Type*} [MeasurableSpace X] {N : ℕ}
    (q : Fin N → NNReal) (ρ : Fin N → X) : Measure X :=
  ∑ i, q i • Measure.dirac (ρ i)

/-- The image measure of a latent measure `r` under a map `ρ`. -/
def pushforward {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    (r : Measure Z) (ρ : Z → X) : Measure X :=
  r.map ρ

end Qatlib.Papers.LatentPQCTran26.MainResults
