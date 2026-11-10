/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.Sqrt
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QWeakness97.MainResults

open Qatlib.Foundations.PureStateMath
open scoped BigOperators

variable {I : Type} [Fintype I]

def euclidDist (ψ φ : QState I) : ℝ :=
  Real.sqrt (∑ i, ‖ψ i - φ i‖ ^ 2)

def bornL1Dist (ψ φ : QState I) : ℝ :=
  ∑ i, |BornProb ψ i - BornProb φ i|

theorem bornL1Dist_nonneg (ψ φ : QState I) : 0 ≤ bornL1Dist ψ φ :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem euclidDist_nonneg (ψ φ : QState I) : 0 ≤ euclidDist ψ φ :=
  Real.sqrt_nonneg _

theorem abs_born_sub_born_le (a b : ℂ) :
    |BornProb (fun _ : Unit => a) () - BornProb (fun _ : Unit => b) ()| ≤
      ‖a - b‖ * (‖a‖ + ‖b‖) := by
  have h1 : |‖a‖ - ‖b‖| ≤ ‖a - b‖ := abs_norm_sub_norm_le a b
  have h2 : ‖a‖ ^ 2 - ‖b‖ ^ 2 = (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) := by ring
  have h3 : BornProb (fun _ : Unit => a) () - BornProb (fun _ : Unit => b) ()
      = (‖a‖ - ‖b‖) * (‖a‖ + ‖b‖) := by
    unfold BornProb
    simpa using h2
  rw [h3, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖a‖ + ‖b‖)]
  exact mul_le_mul_of_nonneg_right h1 (by positivity)

theorem bornL1Dist_le_weighted (ψ φ : QState I) :
    bornL1Dist ψ φ ≤ ∑ i, ‖ψ i - φ i‖ * (‖ψ i‖ + ‖φ i‖) := by
  unfold bornL1Dist BornProb
  exact Finset.sum_le_sum fun i _ => by
    have := abs_born_sub_born_le (ψ i) (φ i)
    simpa using! this

theorem weighted_sum_le_cauchy (ψ φ : QState I) :
    (∑ i, ‖ψ i - φ i‖ * (‖ψ i‖ + ‖φ i‖)) ≤
      Real.sqrt (∑ i, ‖ψ i - φ i‖ ^ 2) *
        Real.sqrt (∑ i, (‖ψ i‖ + ‖φ i‖) ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset I)
    (fun i => ‖ψ i - φ i‖) (fun i => ‖ψ i‖ + ‖φ i‖)
  have hf : 0 ≤ ∑ i, ‖ψ i - φ i‖ * (‖ψ i‖ + ‖φ i‖) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (by positivity)
  have hs : 0 ≤ ∑ i, ‖ψ i - φ i‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hg : 0 ≤ ∑ i, (‖ψ i‖ + ‖φ i‖) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hstep : (∑ i, ‖ψ i - φ i‖ * (‖ψ i‖ + ‖φ i‖)) ^ 2 ≤
      (∑ i, ‖ψ i - φ i‖ ^ 2) * ∑ i, (‖ψ i‖ + ‖φ i‖) ^ 2 := hcs
  have hsqrt := Real.sqrt_le_sqrt hstep
  rwa [Real.sqrt_sq hf, Real.sqrt_mul hs] at hsqrt

theorem norm_sum_sq_le_four (ψ φ : QState I)
    (hψ : Normalized ψ) (hφ : Normalized φ) :
    (∑ i, (‖ψ i‖ + ‖φ i‖) ^ 2) ≤ 4 := by
  have hsplit : ∀ i : I, (‖ψ i‖ + ‖φ i‖) ^ 2 ≤ 2 * ‖ψ i‖ ^ 2 + 2 * ‖φ i‖ ^ 2 := by
    intro i
    nlinarith [sq_nonneg (‖ψ i‖ - ‖φ i‖)]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hsplit i)
  rw [Finset.sum_add_distrib] at hsum
  have h2 : (∑ i, 2 * ‖ψ i‖ ^ 2) = 2 * ∑ i, ‖ψ i‖ ^ 2 := by
    rw [Finset.mul_sum]
  have h3 : (∑ i, 2 * ‖φ i‖ ^ 2) = 2 * ∑ i, ‖φ i‖ ^ 2 := by
    rw [Finset.mul_sum]
  rw [h2, h3] at hsum
  have hψ' : (∑ i, ‖ψ i‖ ^ 2) = 1 := hψ
  have hφ' : (∑ i, ‖φ i‖ ^ 2) = 1 := hφ
  rw [hψ', hφ'] at hsum
  norm_num at hsum ⊢
  exact hsum

theorem bornL1Dist_le_two_euclid (ψ φ : QState I)
    (hψ : Normalized ψ) (hφ : Normalized φ) :
    bornL1Dist ψ φ ≤ 2 * euclidDist ψ φ := by
  have h1 := bornL1Dist_le_weighted ψ φ
  have h2 := weighted_sum_le_cauchy ψ φ
  have h3 := norm_sum_sq_le_four ψ φ hψ hφ
  have hsq_nonneg : 0 ≤ ∑ i, (‖ψ i‖ + ‖φ i‖) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsqrt_le : Real.sqrt (∑ i, (‖ψ i‖ + ‖φ i‖) ^ 2) ≤ 2 := by
    have := Real.sqrt_le_sqrt h3
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rwa [h4] at this
  have hnon : 0 ≤ Real.sqrt (∑ i, ‖ψ i - φ i‖ ^ 2) := Real.sqrt_nonneg _
  calc bornL1Dist ψ φ
      ≤ ∑ i, ‖ψ i - φ i‖ * (‖ψ i‖ + ‖φ i‖) := h1
    _ ≤ Real.sqrt (∑ i, ‖ψ i - φ i‖ ^ 2) *
          Real.sqrt (∑ i, (‖ψ i‖ + ‖φ i‖) ^ 2) := h2
    _ ≤ Real.sqrt (∑ i, ‖ψ i - φ i‖ ^ 2) * 2 :=
        mul_le_mul_of_nonneg_left hsqrt_le hnon
    _ = 2 * euclidDist ψ φ := by
        unfold euclidDist
        ring

theorem theorem31_source (ψ φ : QState I) (hψ : Normalized ψ) (hφ : Normalized φ)
    (ε : ℝ) (h : euclidDist ψ φ ≤ ε) :
    bornL1Dist ψ φ ≤ 4 * ε := by
  have h2 := bornL1Dist_le_two_euclid ψ φ hψ hφ
  have hε : 0 ≤ ε := le_trans (euclidDist_nonneg ψ φ) h
  linarith

end Qatlib.Papers.QWeakness97.MainResults
