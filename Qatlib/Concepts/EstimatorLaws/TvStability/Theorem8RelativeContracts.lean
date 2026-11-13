/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.LayeredMean.LayeredQuantumMean
import Qatlib.Concepts.AmplitudeCore.PayoffMedian.SignedCenteredQuantumMean
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.HeterogeneousBlockMedian

/-!
# Pilot-scaled relative estimator laws

Defines the concrete pilot-scaled relative mean estimator used for Theorems 6 and 8 of
[Montanaro2015]. A pilot average sets a scale, a layered quantum estimate evaluates the divided
payoff, and multiplication restores the original scale; independent trial records and their
sorted median provide the amplified factor estimator.

## Main statements

* `theorem6Scale`, `theorem6ScaledPayoff`, and `theorem6Output` define scaling and
  reconstruction.
* `theorem6TrialLaw` combines independent pilot samples with the conditional layered record law.
* `theorem6FactorLaw` and `theorem6FactorMedian` define independent repetition and median
  amplification.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.SketchArith.TransposeAccess.FinDist

set_option autoImplicit false
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.ProbabilityCore.Concentration.FiniteDecisionTree
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.MonteCarloMean.LayeredMean

namespace Qatlib.Concepts.EstimatorLaws.TvStability

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open scoped Classical

/-- The pilot-based scale `2 * sqrt (B + 1)` times the sample average, with an added unit when
that average is zero. -/
noncomputable def theorem6Scale {I : Type} [Fintype I] (f : I → ℝ) (B : ℝ)
    (N : ℕ) (ω : Fin N → I) : ℝ :=
  avg f ω * (2 * Real.sqrt (B + 1)) + (if avg f ω = 0 then (1 : ℝ) else 0)

/-- Shows that the pilot scale is nonnegative for a nonnegative payoff. -/
private theorem theorem6Scale_nonneg {I : Type} [Fintype I] (f : I → ℝ) (B : ℝ)
    (N : ℕ) (ω : Fin N → I) (hf : ∀ i, 0 ≤ f i) : 0 ≤ theorem6Scale f B N ω := by
  have havg : 0 ≤ avg f ω := by
    unfold avg
    apply div_nonneg _ (by exact_mod_cast Nat.zero_le N)
    exact Finset.sum_nonneg fun k _ => hf (ω k)
  have hsqrt : 0 ≤ 2 * Real.sqrt (B + 1) :=
    mul_nonneg (by norm_num) (Real.sqrt_nonneg (B + 1))
  unfold theorem6Scale
  by_cases h : avg f ω = 0
  · have hif : (if avg f ω = 0 then (1 : ℝ) else 0) = 1 := by rw [if_pos h]
    have hz : avg f ω * (2 * Real.sqrt (B + 1)) = 0 := by rw [h, zero_mul]
    rw [hz, hif]
    norm_num
  · have hif : (if avg f ω = 0 then (1 : ℝ) else 0) = 0 := by rw [if_neg h]
    rw [hif]
    exact add_nonneg (mul_nonneg havg hsqrt) le_rfl

/-- The payoff divided by the pilot-based scale. -/
noncomputable def theorem6ScaledPayoff {I : Type} [Fintype I] (f : I → ℝ)
    (B : ℝ) (N : ℕ) (ω : Fin N → I) : I → ℝ :=
  fun i => f i / theorem6Scale f B N ω

/-- Shows that the pilot-scaled payoff is nonnegative when the original payoff is nonnegative. -/
private theorem theorem6ScaledPayoff_nonneg {I : Type} [Fintype I] (f : I → ℝ)
    (B : ℝ) (N : ℕ) (ω : Fin N → I) (hf : ∀ i, 0 ≤ f i) :
    ∀ i, 0 ≤ theorem6ScaledPayoff f B N ω i := fun i =>
  div_nonneg (hf i) (theorem6Scale_nonneg f B N ω hf)

/-- The output obtained by multiplying the layered estimate by the scale computed from the pilot
record. -/
noncomputable def theorem6Output {I : Type} [Fintype I] (f : I → ℝ) (B : ℝ)
    (N k : ℕ) (ξ : (Fin N → I) × LayerRecord k) : ℝ :=
  layerEstimate k ξ.2 * theorem6Scale f B N ξ.1

/-- The joint finite law of independent pilot samples and a conditional layered estimate of the
pilot-scaled payoff, used for the relative-estimation construction of [Montanaro2015]. -/
noncomputable def theorem6TrialLaw {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (f : I → ℝ) (B : ℝ) (N k : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hf : ∀ i, 0 ≤ f i) :
    FinDist ((Fin N → I) × LayerRecord k) where
  prob ξ := (signedMeanSource A j hA).probOf ξ.1 *
    (layerLaw k A j (theorem6ScaledPayoff f B N ξ.1) hA
      (theorem6ScaledPayoff_nonneg f B N ξ.1 hf)).prob ξ.2
  nonneg ξ := mul_nonneg
    (Finset.prod_nonneg fun i _ => (signedMeanSource A j hA).nonneg _)
    ((layerLaw k A j (theorem6ScaledPayoff f B N ξ.1) hA
      (theorem6ScaledPayoff_nonneg f B N ξ.1 hf)).nonneg _)
  sum_one := by
    simp only [Fintype.sum_prod_type]
    have hstep : ∀ ω : Fin N → I,
        ∑ u : LayerRecord k, (layerLaw k A j (theorem6ScaledPayoff f B N ω) hA
          (theorem6ScaledPayoff_nonneg f B N ω hf)).prob u = 1 := fun ω =>
      (layerLaw k A j (theorem6ScaledPayoff f B N ω) hA
        (theorem6ScaledPayoff_nonneg f B N ω hf)).sum_one
    calc
      _ = ∑ ω : Fin N → I, (signedMeanSource A j hA).probOf ω := by
        apply Finset.sum_congr rfl
        intro ω _
        rw [← Finset.mul_sum, hstep ω, mul_one]
      _ = 1 := (signedMeanSource A j hA).sum_probOf N

/-- The product law of `2 * r + 1` independent pilot-scaled relative-estimation trials. -/
noncomputable def theorem6FactorLaw {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (f : I → ℝ) (B : ℝ) (N k r : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ) (hf : ∀ i, 0 ≤ f i) :
    FinDist (Fin (2 * r + 1) → ((Fin N → I) × LayerRecord k)) :=
  independentSampleLaw
    (fun _ : Fin (2 * r + 1) => theorem6TrialLaw A j f B N k hA hf)

/-- The sorted median of the outputs from `2 * r + 1` pilot-scaled trials. -/
noncomputable def theorem6FactorMedian {I : Type} [Fintype I] (f : I → ℝ)
    (B : ℝ) (N k r : ℕ)
    (ξ : Fin (2 * r + 1) → ((Fin N → I) × LayerRecord k)) : ℝ :=
  sortedBlockMedian r (fun z => theorem6Output f B N k (ξ z))

end Qatlib.Concepts.EstimatorLaws.TvStability
