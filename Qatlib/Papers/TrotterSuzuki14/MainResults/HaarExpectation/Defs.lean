/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Probability.Moments.Variance
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Overlap variables and uncorrelated moment assumptions

This module defines the finite spectral overlap expression `trotterOverlapExpectation` and its
centered component variables. The proposition `UncorrelatedMoments` records a probability
measure, integrability, zero centered means, specified second moments, and vanishing cross
moments for distinct indices. See [BabbushEtAl2015].

## Main statements

* `trotterOverlapExpectation`: Finite eigenvalue-weighted overlap sum.
* `UncorrelatedMoments`: Explicit probabilistic moment assumptions.

## References

* [Babbush et al., 2015][BabbushEtAl2015]
-/

set_option autoImplicit false

namespace Qatlib.Papers.TrotterSuzuki14.MainResults

open MeasureTheory
open scoped BigOperators

/-- The finite weighted overlap sum `∑ k ∈ s, lam k * w k ω`. -/
noncomputable def trotterOverlapExpectation {Ω : Type*} (lam : ℕ → ℝ) (w : ℕ → Ω → ℝ)
    (s : Finset ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ s, lam k * w k ω

/-- The overlap variable at index `k` centered by subtracting `1 / d`. -/
noncomputable def centeredOverlap {Ω : Type*} (w : ℕ → Ω → ℝ) (d : ℕ) (k : ℕ) (ω : Ω) : ℝ :=
  w k ω - 1 / (d : ℝ)

/-- Probability and integrability assumptions for centered overlaps, with zero means, second
moment `2 / (d * (d + 1)) - 1 / d²`, and zero cross moments at distinct indices. -/
structure UncorrelatedMoments {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (d : ℕ) (w : ℕ → Ω → ℝ) : Prop where
  isProb : IsProbabilityMeasure μ
  int_centered : ∀ k, Integrable (centeredOverlap w d k) μ
  int_centered_mul : ∀ k l,
    Integrable (fun ω => centeredOverlap w d k ω * centeredOverlap w d l ω) μ
  centered_mean : ∀ k, ∫ ω, centeredOverlap w d k ω ∂μ = 0
  centered_second : ∀ k,
    ∫ ω, centeredOverlap w d k ω ^ 2 ∂μ
      = 2 / ((d : ℝ) * ((d : ℝ) + 1)) - 1 / (d : ℝ) ^ 2
  centered_orth : ∀ k l, k ≠ l →
    ∫ ω, centeredOverlap w d k ω * centeredOverlap w d l ω ∂μ = 0

end Qatlib.Papers.TrotterSuzuki14.MainResults
