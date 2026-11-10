/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.AuxFiniteCircle
import Qatlib.Foundations.CbmdAnalysis.Core.AuxWeightBounds
import Qatlib.Foundations.CbmdAnalysis.Core.AuxCircleBounds
import Qatlib.Foundations.CbmdAnalysis.Core.DysonPiecewiseInput
import Mathlib.Order.Filter.AtTopBot.Interval
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace CBMD
open Complex Metric Set Filter MeasureTheory
open scoped Topology BigOperators Matrix.Norms.L2Operator ComplexOrder

section Banach
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem auxLCUSum_tendsto (s : Finset ℂ) (hs : s.Nonempty) {a : ℝ} (ha : 0 < a)
    (U : ℂ → E) (hUreal : ∀ x : ℝ, ‖U (x : ℂ)‖ ≤ 1) :
    Tendsto (fun n : ℕ => auxLCUSum s a n U) atTop (𝓝 (∑' k : ℤ, auxSample s a U k)) := by
  exact (auxWeight_smul_summable s hs ha U hUreal).hasSum.comp Finset.tendsto_Icc_neg

theorem aux_kernel_series_identity (s : Finset ℂ) (hs : s.Nonempty)
    (hsTarget : -Complex.I ∉ s) {a ρ : ℝ} (ha : 0 < a)
    (hsLattice : ∀ p ∈ s, ∀ k : ℤ, p ≠ (((k : ℝ) / a : ℝ) : ℂ))
    (hρ : ρ ≤ 2 * Real.pi * a) (U : ℂ → E) (hUanalytic : Differentiable ℂ U)
    (hU : ∀ z, ‖U z‖ ≤ Real.exp (max z.im 0 * ρ)) :
    U (-Complex.I) = (∑' k : ℤ, auxSample s a U k) - auxiliaryCorrection s a U := by
  have hreal (x : ℝ) : ‖U (x : ℂ)‖ ≤ 1 := by simpa using! hU (x : ℂ)
  have hsum := auxLCUSum_tendsto s hs ha U hreal
  have hc := auxContour_circle_tendsto_zero s hs ha hρ U hU
  have he : (fun n : ℕ => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ z in C(0, halfGridRadius a n), auxContourIntegrand s a U z) =ᶠ[atTop]
      (fun n => U (-Complex.I) - auxLCUSum s a n U + auxiliaryCorrection s a U) := by
    filter_upwards [(halfGridRadius_tendsto ha).eventually_gt_atTop (finitePoleRadius s)] with n hn
    exact auxContour_circle_identity_normalized s hsTarget ha hsLattice n
      (lt_of_le_of_lt (finitePoleRadius_ge_one s) hn)
      (fun p hp => lt_of_le_of_lt (norm_le_finitePoleRadius s p hp) hn) U hUanalytic
  have hr :=
      ((tendsto_const_nhds (x := U (-Complex.I))).sub hsum).add_const (auxiliaryCorrection s a U)
  have hz : U (-Complex.I) - (∑' k : ℤ, auxSample s a U k) + auxiliaryCorrection s a U = 0 :=
    tendsto_nhds_unique hr (hc.congr' he)
  calc
    U (-Complex.I) = (U (-Complex.I) - (∑' k : ℤ, auxSample s a U k) +
        auxiliaryCorrection s a U) + (∑' k : ℤ, auxSample s a U k) - auxiliaryCorrection s a U := by abel
    _ = _ := by rw [hz, zero_add]

theorem aux_kernel_series_identity_paper (s : Finset ℂ) (hs : s.Nonempty)
    (hsTarget : -Complex.I ∉ s) {a ρ : ℝ} (ha : 0 < a)
    (hsLattice : ∀ p ∈ s, ∀ k : ℤ, p ≠ (((k : ℝ) / a : ℝ) : ℂ))
    (hρ : ρ ≤ 2 * Real.pi * a) (U : ℂ → E) (hUanalytic : Differentiable ℂ U)
    (hU : ∀ z, ‖U z‖ ≤ Real.exp (max z.im 0 * ρ)) :
    U (-Complex.I) - (∑' k : ℤ, auxSample s a U k) -
      (∑ p ∈ s,
        (((Real.exp (-2 * Real.pi * a) - 1 : ℝ) : ℂ) /
          ((Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * p) - 1) *
            auxDeletedPoleProduct s p)) • U p) = 0 := by
  have h := aux_kernel_series_identity s hs hsTarget ha hsLattice hρ U hUanalytic hU
  have he : auxiliaryCorrection s a U =
      -(∑ p ∈ s,
        (((Real.exp (-2 * Real.pi * a) - 1 : ℝ) : ℂ) /
          ((Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * p) - 1) *
            auxDeletedPoleProduct s p)) • U p) := by
    unfold auxiliaryCorrection auxResidueCoefficient latticePoleFactor
    simp only [neg_div, div_div, neg_smul, Finset.sum_neg_distrib]
  rw [he] at h
  rw [h]
  abel

end Banach

theorem matrix_series_piecewise_dyson {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℕ → ℝ → Matrix I I ℂ) (hH : ∀ j, Continuous (H j))
    (hL : ∀ j, Continuous (L j))
    (hHherm : ∀ j u, (H j u).IsHermitian) (hLpos : ∀ j u, (L j u).PosSemidef)
    (τ : ℕ → ℝ) (hτ : StrictMono τ) (n : ℕ)
    (s : Finset ℂ) (hs : s.Nonempty) (hsTarget : -Complex.I ∉ s)
    {a : ℝ} (ha : 0 < a)
    (hsLattice : ∀ p ∈ s, ∀ k : ℤ, p ≠ (((k : ℝ) / a : ℝ) : ℂ))
    (hbudget : (∫ u in τ 0..τ n, ‖assembledField L τ n u‖) ≤ 2 * Real.pi * a) :
    let U := fun z => assembledDyson H L τ n z (τ n)
    Summable (fun k : ℤ => ‖auxSample s a U k‖) ∧
    U (-Complex.I) - (∑' k : ℤ, auxSample s a U k) -
      (∑ p ∈ s,
        (((Real.exp (-2 * Real.pi * a) - 1 : ℝ) : ℂ) /
          ((Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) * p) - 1) *
            auxDeletedPoleProduct s p)) • U p) = 0 := by
  let U : ℂ → Matrix I I ℂ := fun z => assembledDyson H L τ n z (τ n)
  have hreal (x : ℝ) : ‖U (x : ℂ)‖ ≤ 1 := by
    simpa only [Complex.ofReal_im, max_self, zero_mul, Real.exp_zero] using!
      assembledDyson_norm_le H L hH hL hHherm hLpos τ hτ n (x : ℂ)
  have hsummable := auxWeight_smul_norm_summable s hs ha U hreal
  exact ⟨hsummable, aux_kernel_series_identity_paper s hs hsTarget ha hsLattice hbudget U
    (assembledDyson_differentiable_parameter H L hH hL τ hτ n)
    (assembledDyson_norm_le H L hH hL hHherm hLpos τ hτ n)⟩

end CBMD

end
end Qatlib.Foundations.CbmdAnalysis.Core
