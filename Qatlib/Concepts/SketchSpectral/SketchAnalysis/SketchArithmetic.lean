/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchSpectral.EvenSVT.Numerics
import Qatlib.Concepts.SketchSpectral.SketchAnalysis.SketchArithmeticDefs

/-!
# Arithmetic and sample bounds for two-stage sketches

This module proves unbiasedness, Frobenius concentration bounds, and sample-budget inequalities
for energy-sampled row sketches and conditionally sampled column sketches. These constructions
belong to the sampling-based low-rank arithmetic framework of [ChiaEtAl2022]. It also connects
sampling costs to access ledgers and Hermitian sketch functional calculus to polynomial
evaluation.

## Main statements

* `sqSketch_unbiased`: entrywise unbiasedness of the sampled matrix product.
* `sqUnifiedSampleCount_le_log`: an explicit combined sample bound.
* `sqSketchFunction_stability`: Frobenius stability under a spectral Lipschitz condition.
* `clause19_endpoint`: the conditional second-stage tail bound and runtime ledger bounds.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.IntervalArith.IntervalOps
open Qatlib.Concepts.AdversaryBounds.AdvDuality.CacheOp
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.SketchSpectral.EvenSvtLaw
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.SqEstimation.InnerProduct
open Qatlib.Concepts.SketchSpectral.EvenSVT.ConstructionStageB.StageBSQNUMERICS
open Qatlib.Concepts.SketchSpectral.EvenSVT.ConstructionStageB.StageBSQNUMERICS.SqBitLedger
open Qatlib.Concepts.SketchSpectral.SketchAnalysis.ConstructionStageB.StageBSQSKETCHARITHMETIC

set_option autoImplicit false

namespace Qatlib.Concepts.SketchSpectral.SketchAnalysis
namespace ConstructionStageB
namespace StageBSQSKETCHARITHMETIC

open Matrix
open Polynomial
open Qatlib
open scoped Classical BigOperators Matrix.Norms.Frobenius

noncomputable section

/-- The probability of an independent sample tuple is nonnegative. -/
theorem probOf_nonneg {X : Type} [Fintype X] {L : ℕ} (p : FinDist X) (ω : Fin L → X) :
    0 ≤ p.probOf ω := Finset.prod_nonneg fun _ _ => p.nonneg _

/-- Inclusion of events implies the corresponding inequality between their probabilities. -/
theorem probEvent_mono {X : Type} [Fintype X] {L : ℕ} (p : FinDist X)
    {E E' : (Fin L → X) → Prop} [DecidablePred E] [DecidablePred E']
    (h : ∀ ω, E' ω → E ω) : p.probEvent E' ≤ p.probEvent E := by
  classical
  unfold FinDist.probEvent
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun ω hω => ?_) (fun ω hω hnot => ?_)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ ω, h ω (Finset.mem_filter.mp hω).2⟩
  · exact probOf_nonneg p ω

/-- The row product mass of a matrix with itself equals its total squared row energy. -/
theorem sketchRowProductMass_self {K C : Type} [Fintype K] [Fintype C] (A : Matrix K C ℂ) :
    sketchRowProductMass A A = sketchSquared A := by
  unfold sketchRowProductMass sketchSquared
  apply Finset.sum_congr rfl
  intro k _
  rw [Real.mul_self_sqrt (sketchRowSquared_nonneg A k)]

/-- The energy sampling law dominates the normalized row energy with oversampling factor one. -/
theorem energySampling_dominates_one {K C : Type} [Fintype K] [Fintype C]
    (A : Matrix K C ℂ) (hA : 0 < sketchSquared A) (k : K) :
    sketchRowSquared A k / (1 * sketchSquared A) ≤ (energySamplingLaw A hA).prob k := by
  rw [show (1 * sketchSquared A) = sketchSquared A by ring]
  exact le_rfl

/-- For a positive sample count, the total squared energy of the energy-sampled row sketch is at
most that of the source matrix. -/
theorem sqRowEnergy_le_source {K C : Type} [Fintype K] [DecidableEq K] [Fintype C]
    [DecidableEq C] (A : Matrix K C ℂ) (hA : 0 < sketchSquared A) (r : ℕ) (hr : 0 < r)
    (ω : Fin r → K) :
    sketchSquared (sqRowSketch A (energySamplingLaw A hA) r ω) ≤ sketchSquared A := by
  have h := (compact_sketch_frobenius_norm_bounds_and_tail K C (energySamplingLaw A hA) r A 1
    hr (by norm_num) hA (energySampling_dominates_one A hA)).2.1
  have h' := h ω
  simpa [sqRowSketch] using! h'

/-- Under energy sampling, the probability that the Frobenius Gram error reaches the stated
square-root threshold is at most `δ`. -/
theorem sqRowStageGram_tail {K C : Type} [Fintype K] [DecidableEq K] [Fintype C]
    [DecidableEq C] (A : Matrix K C ℂ) (hA : 0 < sketchSquared A) (r : ℕ) (hr : 0 < r)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (energySamplingLaw A hA).probEvent (fun ω : Fin r → K =>
      Real.sqrt (8 * Real.log (2 / δ) / (r : ℝ)) * sketchSquared A
        ≤ ‖sketchProduct (energySamplingLaw A hA) r A A ω - Aᴴ * A‖) ≤ δ := by
  have hW : 0 < sketchRowProductMass A A := by
    rw [sketchRowProductMass_self]
    exact hA
  have hdom : ∀ k, Real.sqrt (sketchRowSquared A k) * Real.sqrt (sketchRowSquared A k)
      / (1 * sketchRowProductMass A A) ≤ (energySamplingLaw A hA).prob k := by
    intro k
    rw [Real.mul_self_sqrt (sketchRowSquared_nonneg A k)]
    rw [sketchRowProductMass_self]
    exact energySampling_dominates_one A hA k
  have h := compact_sketch_two_sided_source_frobenius_tail K C C
    (energySamplingLaw A hA) r A A 1 δ hr (by norm_num) hW hδ hδ1 hdom
  rw [sketchRowProductMass_self] at h
  have hsqrt : (8 * 1 ^ 2 * Real.log (2 / δ) / (r : ℝ)) = 8 * Real.log (2 / δ) / (r : ℝ) := by
    ring
  rw [hsqrt] at h
  exact h

/-- For a fixed nonzero row sketch and dominated conditional column access, the second-stage
Frobenius Gram error reaches the stated oversampling threshold with probability at most `δ`. -/
theorem sqColStageGram_tail {K C : Type} [Fintype K] [DecidableEq K] [Fintype C]
    [DecidableEq C] {r : ℕ} (A : Matrix K C ℂ) (hA : 0 < sketchSquared A) (φ : ℝ)
    (hφ : 1 ≤ φ) (acc : SqConditionalAccess A (energySamplingLaw A hA) r φ) (c : ℕ)
    (hc : 0 < c) (hr : 0 < r) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (v : Fin r → K)
    (hRv : 0 < sketchSquared (sqRowSketch A (energySamplingLaw A hA) r v)ᴴ) :
    (acc.law v).probEvent (fun w : Fin c → C =>
      Real.sqrt (8 * φ ^ 2 * Real.log (2 / δ) / (c : ℝ)) * sketchSquared A
        ≤ ‖sketchProduct (acc.law v) c (sqRowSketch A (energySamplingLaw A hA) r v)ᴴ
              (sqRowSketch A (energySamplingLaw A hA) r v)ᴴ w
            - (sqRowSketch A (energySamplingLaw A hA) r v)
                * (sqRowSketch A (energySamplingLaw A hA) r v)ᴴ‖) ≤ δ := by
  let B : Matrix C (Fin r) ℂ := (sqRowSketch A (energySamplingLaw A hA) r v)ᴴ
  have hW : 0 < sketchRowProductMass B B := by
    rw [sketchRowProductMass_self]
    simpa [B] using! hRv
  have hdom : ∀ k, Real.sqrt (sketchRowSquared B k) * Real.sqrt (sketchRowSquared B k)
      / (φ * sketchRowProductMass B B) ≤ (acc.law v).prob k := by
    intro k
    rw [Real.mul_self_sqrt (sketchRowSquared_nonneg B k)]
    rw [sketchRowProductMass_self]
    simpa [B] using! acc.dominates v k
  have h := compact_sketch_two_sided_source_frobenius_tail C (Fin r) (Fin r)
    (acc.law v) c B B φ δ hc hφ hW hδ hδ1 hdom
  rw [sketchRowProductMass_self] at h
  have hle : sketchSquared B ≤ sketchSquared A := by
    have h1 : sketchSquared B = sketchSquared (sqRowSketch A (energySamplingLaw A hA) r v) := by
      simp [B, sketchSquared_adjoint]
    rw [h1]
    exact sqRowEnergy_le_source A hA r hr v
  have hscale : Real.sqrt (8 * φ ^ 2 * Real.log (2 / δ) / (c : ℝ)) * sketchSquared B
      ≤ Real.sqrt (8 * φ ^ 2 * Real.log (2 / δ) / (c : ℝ)) * sketchSquared A :=
    mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg _)
  have hweaken : (acc.law v).probEvent (fun w : Fin c → C =>
      Real.sqrt (8 * φ ^ 2 * Real.log (2 / δ) / (c : ℝ)) * sketchSquared A
        ≤ ‖sketchProduct (acc.law v) c B B w - Bᴴ * B‖)
      ≤ (acc.law v).probEvent (fun w : Fin c → C =>
      Real.sqrt (8 * φ ^ 2 * Real.log (2 / δ) / (c : ℝ)) * sketchSquared B
        ≤ ‖sketchProduct (acc.law v) c B B w - Bᴴ * B‖) :=
    probEvent_mono _ (fun w hw => hscale.trans hw)
  have hres := hweaken.trans h
  simpa [B, Matrix.conjTranspose_conjTranspose] using! hres

/-- The logarithm log(2 / (δ / 2)) is positive when 0 < δ < 1. -/
theorem log_two_over_delta_half_pos {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < Real.log (2 / (δ / 2)) := by
  have h : 1 < 2 / (δ / 2) := by
    have hδ2 : 0 < δ / 2 := div_pos hδ (by norm_num)
    exact (lt_div_iff₀ hδ2).2 (by linarith)
  exact Real.log_pos h

/-- A nonnegative upper bound on the square of a tail scale also bounds its square root. -/
theorem sqTailRoot_le {m δ n s : ℝ} (hs : 0 ≤ s)
    (h : m * Real.log (2 / (δ / 2)) / n ≤ s ^ 2) :
    Real.sqrt (m * Real.log (2 / (δ / 2)) / n) ≤ s := by
  rw [Real.sqrt_le_iff]
  exact ⟨hs, h⟩

/-- A row sample count meeting `sqRowStageSamples` makes the first-stage error scale at most ε /
2 under the stated positivity assumptions. -/
theorem sqRowStageSamples_sufficient {ε δ E : ℝ} {r : ℕ} (hE : 0 < E) (hε : 0 < ε)
    (hr : 0 < r)
    (hcount : sqRowStageSamples ε δ E ≤ (r : ℝ)) :
    Real.sqrt (8 * Real.log (2 / (δ / 2)) / (r : ℝ)) * E ≤ ε / 2 := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hcount' : 32 * Real.log (2 / (δ / 2)) * E ^ 2 ≤ ε ^ 2 * (r : ℝ) := by
    have h := hcount
    unfold sqRowStageSamples at h
    have hne : ε ^ 2 ≠ 0 := ne_of_gt hε2
    rw [div_le_iff₀ hε2] at h
    linarith
  have hA : 8 * Real.log (2 / (δ / 2)) / (r : ℝ) ≤ ε ^ 2 / (4 * E ^ 2) := by
    apply (div_le_iff₀ hrpos).2
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < 4 * E ^ 2)).2
    have h4 : 8 * Real.log (2 / (δ / 2)) * (4 * E ^ 2)
        = 32 * Real.log (2 / (δ / 2)) * E ^ 2 := by ring
    rw [h4]
    linarith [hcount']
  have hsq : ε ^ 2 / (4 * E ^ 2) = (ε / (2 * E)) ^ 2 := by
    have hne : 2 * E ≠ 0 := by positivity
    rw [div_pow]
    field_simp [hne]
    ring
  have hroot : Real.sqrt (8 * Real.log (2 / (δ / 2)) / (r : ℝ)) ≤ ε / (2 * E) := by
    apply sqTailRoot_le (by positivity)
    exact hA.trans (by rw [hsq])
  have hmul := mul_le_mul_of_nonneg_right hroot hE.le
  have hlast : (ε / (2 * E)) * E = ε / 2 := by
    field_simp
  linarith [hmul]

/-- A column sample count meeting `sqColStageSamples` makes the second-stage error scale at most
ε / 2 under the stated positivity assumptions. -/
theorem sqColStageSamples_sufficient {φ ε δ E : ℝ} {c : ℕ} (hE : 0 < E) (hε : 0 < ε)
    (hc : 0 < c)
    (hcount : sqColStageSamples φ ε δ E ≤ (c : ℝ)) :
    Real.sqrt (8 * φ ^ 2 * Real.log (2 / (δ / 2)) / (c : ℝ)) * E ≤ ε / 2 := by
  have hcpos : 0 < (c : ℝ) := by exact_mod_cast hc
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hcount' : 32 * φ ^ 2 * Real.log (2 / (δ / 2)) * E ^ 2 ≤ ε ^ 2 * (c : ℝ) := by
    have h := hcount
    unfold sqColStageSamples at h
    have hne : ε ^ 2 ≠ 0 := ne_of_gt hε2
    rw [div_le_iff₀ hε2] at h
    linarith
  have hA : 8 * φ ^ 2 * Real.log (2 / (δ / 2)) / (c : ℝ) ≤ ε ^ 2 / (4 * E ^ 2) := by
    apply (div_le_iff₀ hcpos).2
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : 0 < 4 * E ^ 2)).2
    have h4 : 8 * φ ^ 2 * Real.log (2 / (δ / 2)) * (4 * E ^ 2)
        = 32 * φ ^ 2 * Real.log (2 / (δ / 2)) * E ^ 2 := by ring
    rw [h4]
    linarith [hcount']
  have hsq : ε ^ 2 / (4 * E ^ 2) = (ε / (2 * E)) ^ 2 := by
    have hne : 2 * E ≠ 0 := by positivity
    rw [div_pow]
    field_simp [hne]
    ring
  have hroot : Real.sqrt (8 * φ ^ 2 * Real.log (2 / (δ / 2)) / (c : ℝ)) ≤ ε / (2 * E) := by
    apply sqTailRoot_le (by positivity)
    exact hA.trans (by rw [hsq])
  have hmul := mul_le_mul_of_nonneg_right hroot hE.le
  have hlast : (ε / (2 * E)) * E = ε / 2 := by
    field_simp
  linarith [hmul]

/-- The combined stage sample expression equals 32(1 + φ²) log(2 / (δ / 2)) E² / ε². -/
theorem sqUnifiedSampleCount_eq (φ ε δ E : ℝ) :
    sqUnifiedSampleCount φ ε δ E
      = 32 * (1 + φ ^ 2) * Real.log (2 / (δ / 2)) * E ^ 2 / ε ^ 2 := by
  unfold sqUnifiedSampleCount sqRowStageSamples sqColStageSamples
  ring_nf

/-- For φ ≥ 1 and valid positive accuracy and failure parameters, the combined sample expression
is at most 64E² times the unified rate. -/
theorem sqUnifiedSampleCount_le_rate {φ ε δ E : ℝ} (hφ : 1 ≤ φ) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    sqUnifiedSampleCount φ ε δ E ≤ 64 * E ^ 2 * sqUnifiedRate φ ε δ := by
  have hlog : Real.log (2 / (δ / 2)) = Real.log (4 / δ) := by
    have h1 : 2 / (δ / 2) = 4 / δ := by
      field_simp
      ring
    rw [h1]
  have hL : 0 < Real.log (4 / δ) := by
    have hδp : 0 < δ := hδ
    have h : 1 < 4 / δ := by
      exact (lt_div_iff₀ hδp).2 (by linarith)
    exact Real.log_pos h
  have hone : 1 + φ ^ 2 ≤ 2 * φ ^ 2 := by
    nlinarith [sq_nonneg (φ - 1)]
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have key : 32 * (1 + φ ^ 2) * Real.log (4 / δ) * E ^ 2
      ≤ 64 * φ ^ 2 * Real.log (4 / δ) * E ^ 2 := by
    have hnonneg : 0 ≤ 32 * Real.log (4 / δ) * E ^ 2 := by positivity
    have h := mul_le_mul_of_nonneg_right hone hnonneg
    linarith
  calc sqUnifiedSampleCount φ ε δ E
      = 32 * (1 + φ ^ 2) * Real.log (4 / δ) * E ^ 2 / ε ^ 2 := by
        rw [sqUnifiedSampleCount_eq]
        rw [hlog]
    _ ≤ (64 * φ ^ 2 * Real.log (4 / δ) * E ^ 2) / ε ^ 2 := by
      rw [div_le_div_iff_of_pos_right hε2]
      exact key
    _ = 64 * E ^ 2 * sqUnifiedRate φ ε δ := by
      unfold sqUnifiedRate
      ring

/-- For positive accuracy and 0 < δ ≤ 1 / 4, the unified rate is at most 2φ² log(1 / δ) / ε². -/
theorem sqUnifiedRate_le_log {φ ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    sqUnifiedRate φ ε δ ≤ 2 * φ ^ 2 * Real.log (1 / δ) / ε ^ 2 := by
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hlog : Real.log (4 / δ) ≤ 2 * Real.log (1 / δ) := by
    have h1 : 4 / δ = 4 * (1 / δ) := by
      field_simp
    have hpos : 0 < 1 / δ := by positivity
    have hlog4 : Real.log 4 ≤ Real.log (1 / δ) := by
      apply Real.log_le_log (by norm_num)
      apply (le_div_iff₀ hδ).2
      linarith [hδ4]
    rw [h1, Real.log_mul (by norm_num) (by positivity)]
    linarith
  unfold sqUnifiedRate
  rw [div_le_div_iff_of_pos_right hε2]
  have hφ2 : 0 ≤ φ ^ 2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hlog hφ2
  nlinarith [hmul]

/-- For φ ≥ 1, positive accuracy, and 0 < δ ≤ 1 / 4, the combined sample expression is at most
128φ² log(1 / δ) E² / ε². -/
theorem sqUnifiedSampleCount_le_log {φ ε δ E : ℝ} (hφ : 1 ≤ φ) (hε : 0 < ε)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    sqUnifiedSampleCount φ ε δ E ≤ 128 * φ ^ 2 * Real.log (1 / δ) * E ^ 2 / ε ^ 2 := by
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hlog2 : Real.log (2 / (δ / 2)) = Real.log (4 / δ) := by
    have h1 : 2 / (δ / 2) = 4 / δ := by
      field_simp
      ring
    rw [h1]
  have hL : 0 < Real.log (4 / δ) := by
    exact Real.log_pos ((lt_div_iff₀ hδ).2 (by linarith))
  have hone : 1 + φ ^ 2 ≤ 2 * φ ^ 2 := by
    nlinarith [sq_nonneg (φ - 1)]
  have hA : 32 * (1 + φ ^ 2) * Real.log (4 / δ) * E ^ 2
      ≤ 64 * E ^ 2 * φ ^ 2 * Real.log (4 / δ) := by
    have hnonneg : 0 ≤ 32 * Real.log (4 / δ) * E ^ 2 := by positivity
    have h := mul_le_mul_of_nonneg_right hone hnonneg
    linarith
  have hlog : Real.log (4 / δ) ≤ 2 * Real.log (1 / δ) := by
    have h1 : 4 / δ = 4 * (1 / δ) := by
      field_simp
    have hpos : 0 < 1 / δ := by positivity
    have hlog4 : Real.log 4 ≤ Real.log (1 / δ) := by
      apply Real.log_le_log (by norm_num)
      apply (le_div_iff₀ hδ).2
      linarith [hδ4]
    rw [h1, Real.log_mul (by norm_num) (by positivity)]
    linarith
  have hB : 64 * E ^ 2 * φ ^ 2 * Real.log (4 / δ)
      ≤ 128 * φ ^ 2 * Real.log (1 / δ) * E ^ 2 := by
    have hnonneg : 0 ≤ 64 * E ^ 2 * φ ^ 2 := by positivity
    have h := mul_le_mul_of_nonneg_right hlog hnonneg
    linarith
  calc sqUnifiedSampleCount φ ε δ E
      = (32 * (1 + φ ^ 2) * Real.log (4 / δ) * E ^ 2) / ε ^ 2 := by
        rw [sqUnifiedSampleCount_eq, hlog2]
    _ ≤ (64 * E ^ 2 * φ ^ 2 * Real.log (4 / δ)) / ε ^ 2 := by
        rw [div_le_div_iff_of_pos_right hε2]
        exact hA
    _ ≤ (128 * φ ^ 2 * Real.log (1 / δ) * E ^ 2) / ε ^ 2 := by
        rw [div_le_div_iff_of_pos_right hε2]
        exact hB
    _ = 128 * φ ^ 2 * Real.log (1 / δ) * E ^ 2 / ε ^ 2 := rfl

/-- The unified sample rate is positive for φ ≥ 1, positive accuracy, and a failure parameter in
(0, 1). -/
theorem sqUnifiedRate_pos {φ ε δ : ℝ} (hφ : 1 ≤ φ) (hε : 0 < ε) (hδ : 0 < δ)
    (hδ4 : δ < 1) : 0 < sqUnifiedRate φ ε δ := by
  unfold sqUnifiedRate
  have h1 : 0 < φ ^ 2 := sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hφ)
  have h2 : 0 < Real.log (4 / δ) := by
    have hpos : 0 < δ := hδ
    exact Real.log_pos ((lt_div_iff₀ hpos).2 (by linarith))
  have h3 : 0 < ε ^ 2 := sq_pos_of_pos hε
  exact div_pos (mul_pos h1 h2) h3

/-- The sampling law extracted from a finite sampling and query input is its stored sample
distribution. -/
theorem sqInput_samplingLaw_eq {X : Type} [Fintype X] (a : FiniteSQInput X) :
    sqInputSamplingLaw a = a.samples := rfl

/-- The input sampling probability is the squared envelope magnitude divided by the total
squared envelope norm. -/
theorem sqInput_envelope_energy {X : Type} [Fintype X] (a : FiniteSQInput X) (i : X) :
    (sqInputSamplingLaw a).prob i = Complex.normSq (a.envelope i) / sqSquaredNorm a.envelope :=
  a.sample_spec i

/-- For a positive sample count and positive source energy, the energy-sampled product sketch
has entrywise expectation XᴴY. -/
theorem sqSketch_unbiased {K C D : Type} [Fintype K] [DecidableEq K] [Fintype C]
    [DecidableEq C] [Fintype D] [DecidableEq D] (X : Matrix K C ℂ) (Y : Matrix K D ℂ)
    (hX : 0 < sketchSquared X) (r : ℕ) (hr : 0 < r) (i : C) (j : D) :
    (∑ ω : Fin r → K, (energySamplingLaw X hX).probOf ω
        * (sketchProduct (energySamplingLaw X hX) r X Y ω i j))
      = (Xᴴ * Y) i j := by
  have hz : ∀ k, (energySamplingLaw X hX).prob k = 0 →
      ∀ i j, star (X k i) * Y k j = 0 := by
    intro k hp i j
    have hk : sketchRowSquared X k = 0 := by
      have hprob : (energySamplingLaw X hX).prob k = sketchRowSquared X k / sketchSquared X := rfl
      rw [hprob] at hp
      rw [div_eq_zero_iff] at hp
      rcases hp with h | h
      · exact h
      · exact absurd h (ne_of_gt hX)
    have hentry := sketchRowSquared_eq_zero_entry X k hk i
    rw [hentry, star_zero, zero_mul]
  have hmean := sketchMean_eq_product (energySamplingLaw X hX) X Y hz
  have h := sketchProduct_unbiased_mean (energySamplingLaw X hX) r hr X Y i j
  rw [hmean] at h
  exact h

/-- For a positive sample count and positive source energy, the energy-sampled Gram sketch has
entrywise expectation XᴴX. -/
theorem sqSketch_unbiased_gram {K C : Type} [Fintype K] [DecidableEq K] [Fintype C]
    [DecidableEq C] (X : Matrix K C ℂ) (hX : 0 < sketchSquared X) (r : ℕ) (hr : 0 < r)
    (i : C) (j : C) :
    (∑ ω : Fin r → K, (energySamplingLaw X hX).probOf ω
        * (sketchProduct (energySamplingLaw X hX) r X X ω i j))
      = (Xᴴ * X) i j :=
  sqSketch_unbiased X X hX r hr i j

/-- Hermitian sketch functional calculus for a real polynomial agrees with matrix polynomial
evaluation after mapping coefficients to the complex numbers. -/
theorem sqSketchFunction_polynomial {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℂ} (hA : A.IsHermitian) (p : Polynomial ℝ) :
    sqSketchFunction hA (fun x => ((p.eval x : ℝ) : ℂ))
      = aeval A (p.map Complex.ofRealHom) :=
  hermitian_spectral_polynomial_evaluation I A hA p

/-- A nonnegative scalar Lipschitz bound between the two ordered spectra gives the corresponding
Frobenius perturbation bound for sketch functional calculus. -/
theorem sqSketchFunction_stability {I : Type} [Fintype I] [DecidableEq I]
    {A B : Matrix I I ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℂ) (L : ℝ)
    (hL : 0 ≤ L)
    (hpoint : ∀ i j, ‖f (orderedHermitianValues hA i)
        - f (orderedHermitianValues hB j)‖
        ≤ L * |orderedHermitianValues hA i - orderedHermitianValues hB j|) :
    spectralFrobenius (sqSketchFunction hA f - sqSketchFunction hB f)
      ≤ L * spectralFrobenius (A - B) :=
  hermitian_spectral_function_frobenius_stability I A B hA hB f L hL hpoint

/-- The sketch runtime is the total sample count multiplied by the cost per sample. -/
theorem sqSketchRuntime_eq (r c perSample : ℕ) :
    sqSketchRuntime r c perSample = (r + c) * perSample := rfl

/-- With unit cost per sample, the sketch runtime equals the two-stage ledger's sampler read
count. -/
theorem sqSketchRuntime_samplerReads (r c : ℕ) :
    sqSketchRuntime r c 1 = (sqTwoStageLedger r c).samplerReads := by
  simp [sqSketchRuntime, sqTwoStageLedger]

/-- With cost per sample at least one, the sketch runtime bounds the two-stage sampler read
count. -/
theorem sqSketchRuntime_ge_ledger (r c perSample : ℕ) (h : 1 ≤ perSample) :
    (sqTwoStageLedger r c).samplerReads ≤ sqSketchRuntime r c perSample := by
  have h' : r + c ≤ (r + c) * perSample := by
    have h2 := mul_le_mul_of_nonneg_right h (Nat.zero_le (r + c))
    simpa [mul_comm, mul_one] using! h2
  simpa [sqSketchRuntime, sqTwoStageLedger] using! h'

/-- With cost per sample at least one, the sketch runtime bounds the two-stage probability read
count. -/
theorem sqSketchRuntime_ge_probReads (r c perSample : ℕ) (h : 1 ≤ perSample) :
    (sqTwoStageLedger r c).probReads ≤ sqSketchRuntime r c perSample := by
  simpa [sqTwoStageLedger] using! sqSketchRuntime_ge_ledger r c perSample h

/-- The row sampling cost is n times r. -/
theorem sqRowSamplingCost_eq (n r : ℕ) : sqRowSamplingCost n r = n * r := rfl

/-- The row sampling cost equals the read count in the unit-cost sketch arithmetic ledger. -/
theorem sqRowSamplingCost_bridge (n r c : ℕ) :
    sqRowSamplingCost n r = (sketchArithmeticLedger n r c 1).reads := by
  simp [sqRowSamplingCost, sketchArithmeticLedger]

/-- The row sampling workspace equals the workspace word count in the unit-cost sketch
arithmetic ledger. -/
theorem sqRowSamplingWorkspace_eq (r n c : ℕ) :
    sqRowSamplingWorkspace r = (sketchArithmeticLedger n r c 1).workspaceWords := by
  simp [sqRowSamplingWorkspace, SqBitLedger.workspaceWords, sketchArithmeticLedger]

/-- For word size at least two and a positive combined read and multiplication count, the
arithmetic ledger's bit time strictly exceeds its RAM operation count. -/
theorem sqRowSampling_bitTime_ge_ram (n r c : ℕ) (w : ℕ) (hw : 2 ≤ w)
    (hpos : 0 < (sketchArithmeticLedger n r c 1).reads
        + (sketchArithmeticLedger n r c 1).multiplies) :
    (sketchArithmeticLedger n r c 1).ramOps
      < (sketchArithmeticLedger n r c 1).bitTime w :=
  SqBitLedger.bitTime_gt_ramOps _ w hw hpos

/-- Collects the unified sample-count bounds in terms of the failure logarithm and the unified
rate. -/
theorem clause17_endpoint {φ ε δ E : ℝ} (hφ : 1 ≤ φ) (hε : 0 < ε) (hδ : 0 < δ)
    (hδ4 : δ ≤ 1 / 4) :
    sqUnifiedSampleCount φ ε δ E ≤ 128 * φ ^ 2 * Real.log (1 / δ) * E ^ 2 / ε ^ 2 ∧
      sqUnifiedSampleCount φ ε δ E ≤ 64 * E ^ 2 * sqUnifiedRate φ ε δ := by
  exact ⟨sqUnifiedSampleCount_le_log hφ hε hδ hδ4,
    sqUnifiedSampleCount_le_rate hφ hε hδ (by linarith [hδ4])⟩

/-- Collects the input sampling-law identity, unbiased Gram sketch identity, and polynomial
functional calculus identity. -/
theorem clause18_endpoint {X : Type} [Fintype X] {K C : Type} [Fintype K] [DecidableEq K]
    [Fintype C] [DecidableEq C] {I : Type} [Fintype I] [DecidableEq I]
    (a : FiniteSQInput X) (M : Matrix K C ℂ) (hM : 0 < sketchSquared M)
    (r : ℕ) (hr : 0 < r) (i : C) (j : C)
    (H : Matrix I I ℂ) (hH : H.IsHermitian) (p : Polynomial ℝ) :
    sqInputSamplingLaw a = a.samples ∧
      (∑ ω : Fin r → K, (energySamplingLaw M hM).probOf ω
          * (sketchProduct (energySamplingLaw M hM) r M M ω i j)) = (Mᴴ * M) i j ∧
      sqSketchFunction hH (fun x => ((p.eval x : ℝ) : ℂ))
        = aeval H (p.map Complex.ofRealHom) := by
  exact ⟨sqInput_samplingLaw_eq a, sqSketch_unbiased_gram M hM r hr i j,
    sqSketchFunction_polynomial hH p⟩

/-- Combines the conditional second-stage Gram tail bound with the runtime identity and bounds
on sampler and probability reads. -/
theorem clause19_endpoint {K C : Type} [Fintype K] [DecidableEq K] [Fintype C]
    [DecidableEq C] {r : ℕ} (A : Matrix K C ℂ) (hA : 0 < sketchSquared A) (φ : ℝ)
    (hφ : 1 ≤ φ) (acc : SqConditionalAccess A (energySamplingLaw A hA) r φ) (c : ℕ)
    (hc : 0 < c) (hr : 0 < r) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (v : Fin r → K)
    (hRv : 0 < sketchSquared (sqRowSketch A (energySamplingLaw A hA) r v)ᴴ)
    (perSample : ℕ) (hper : 1 ≤ perSample) :
    (acc.law v).probEvent (fun w : Fin c → C =>
      Real.sqrt (8 * φ ^ 2 * Real.log (2 / δ) / (c : ℝ)) * sketchSquared A
        ≤ ‖sketchProduct (acc.law v) c (sqRowSketch A (energySamplingLaw A hA) r v)ᴴ
              (sqRowSketch A (energySamplingLaw A hA) r v)ᴴ w
            - (sqRowSketch A (energySamplingLaw A hA) r v)
                * (sqRowSketch A (energySamplingLaw A hA) r v)ᴴ‖) ≤ δ ∧
      sqSketchRuntime r c perSample = (r + c) * perSample ∧
      (sqTwoStageLedger r c).samplerReads ≤ sqSketchRuntime r c perSample ∧
      (sqTwoStageLedger r c).probReads ≤ sqSketchRuntime r c perSample := by
  refine ⟨sqColStageGram_tail A hA φ hφ acc c hc hr δ hδ hδ1 v hRv, ?_⟩
  exact ⟨sqSketchRuntime_eq r c perSample, sqSketchRuntime_ge_ledger r c perSample hper,
    sqSketchRuntime_ge_probReads r c perSample hper⟩

/-- Identifies row sampling cost and workspace with the arithmetic ledger and proves that bit
time strictly exceeds RAM operations under the stated assumptions. -/
theorem clause20_endpoint (n r c : ℕ) (w : ℕ) (hw : 2 ≤ w)
    (hpos : 0 < (sketchArithmeticLedger n r c 1).reads
        + (sketchArithmeticLedger n r c 1).multiplies) :
    sqRowSamplingCost n r = (sketchArithmeticLedger n r c 1).reads ∧
      sqRowSamplingWorkspace r = (sketchArithmeticLedger n r c 1).workspaceWords ∧
      (sketchArithmeticLedger n r c 1).ramOps
        < (sketchArithmeticLedger n r c 1).bitTime w := by
  exact ⟨sqRowSamplingCost_bridge n r c, sqRowSamplingWorkspace_eq r n c,
    sqRowSampling_bitTime_ge_ram n r c w hw hpos⟩

end

end StageBSQSKETCHARITHMETIC
