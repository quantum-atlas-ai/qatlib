/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.QaeLaw.PayoffError
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Qatlib.Papers.MonteCarloInt20.QaeLaw.Fourier Qatlib.Papers.MonteCarloInt20.QaeLaw.Payoff
namespace Qatlib.Papers.MonteCarloInt20.QaeLaw.Step

def strictStep (τ x : ℝ) : ℝ := if τ < x then 1 else 0

theorem step_margin_pointwise (τ a x δ : ℝ) (hδ : 0 < δ) (hm : δ ≤ |a-τ|) :
    |strictStep τ x-strictStep τ a| ≤ (x-a)^2/δ^2 := by
  by_cases ha : τ<a <;> by_cases hx : τ<x
  · simp only [strictStep,ha,hx,↓reduceIte,sub_self,abs_zero]
    positivity
  · simp only [strictStep,ha,hx,↓reduceIte,zero_sub,abs_neg,abs_one]
    apply (le_div_iff₀ (sq_pos_of_pos hδ)).mpr
    rw [abs_of_pos (sub_pos.mpr ha)] at hm
    have hxa : x ≤ τ := not_lt.mp hx
    nlinarith
  · simp only [strictStep,ha,hx,↓reduceIte,sub_zero,abs_one]
    apply (le_div_iff₀ (sq_pos_of_pos hδ)).mpr
    rw [abs_of_nonpos (sub_nonpos.mpr (not_lt.mp ha))] at hm
    nlinarith
  · simp only [strictStep,ha,hx,↓reduceIte,sub_self,abs_zero]
    positivity

theorem raw_scaled_second_moment (M : ℕ) (θ D : ℝ) (hM : 0 < M) :
    (∑ k,rawMass M θ k*(D*estimate M k-D*target θ)^2) ≤ D^2/(M:ℝ) := by
  have he := raw_expectation_eq_single M θ hM
    (fun k => (D*estimate M k-D*target θ)^2)
    (by intro k; dsimp only [estimate]; rw [sinSquare_reflection M hM])
  rw [he]
  calc
    _ = D^2*(∑ k,phaseMass M θ k*(estimate M k-target θ)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ D^2*(1/(M:ℝ)) := mul_le_mul_of_nonneg_left (second_moment_bound M θ hM) (sq_nonneg _)
    _ = _ := by ring

theorem step_payoff_margin_error (M : ℕ) (θ D τ δ : ℝ) (hM : 0 < M)
    (hδ : 0 < δ) (hmargin : δ ≤ |D*target θ-τ|) :
    |(∑ k,rawMass M θ k*strictStep τ (D*estimate M k))-strictStep τ (D*target θ)| ≤
      D^2/((M:ℝ)*δ^2) := by
  have hnorm : ∑ k,rawMass M θ k=1 := (rawLaw M θ hM).sum_one
  have he : (∑ k,rawMass M θ k*strictStep τ (D*estimate M k))-strictStep τ (D*target θ)=
    ∑ k,rawMass M θ k*(strictStep τ (D*estimate M k)-strictStep τ (D*target θ)) := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hnorm,one_mul]
  rw [he]
  calc
    _ ≤ ∑ k,|rawMass M θ k*(strictStep τ (D*estimate M k)-strictStep τ (D*target θ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k,rawMass M θ k*((D*estimate M k-D*target θ)^2/δ^2) := by
      apply Finset.sum_le_sum
      intro k _
      have hp : 0 ≤ rawMass M θ k := (rawLaw M θ hM).nonneg k
      rw [abs_mul,abs_of_nonneg hp]
      exact mul_le_mul_of_nonneg_left
        (step_margin_pointwise τ (D*target θ) (D*estimate M k) δ hδ hmargin)
        ((rawLaw M θ hM).nonneg k)
    _ = (∑ k,rawMass M θ k*(D*estimate M k-D*target θ)^2)/δ^2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ (D^2/(M:ℝ))/δ^2 := div_le_div_of_nonneg_right (raw_scaled_second_moment M θ D hM) (sq_nonneg _)
    _ = _ := by ring

end Qatlib.Papers.MonteCarloInt20.QaeLaw.Step
