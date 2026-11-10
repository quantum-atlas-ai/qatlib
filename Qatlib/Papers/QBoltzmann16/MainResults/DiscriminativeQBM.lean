/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QBoltzmann16.MainResults.TraceExpDerivative
import Qatlib.Papers.QBoltzmann16.MainResults.BoundBasedQBM
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix Filter
open scoped BigOperators ComplexOrder Topology Matrix Matrix.Norms.L2Operator
set_option warningAsError false
namespace Qatlib.Papers.QBoltzmann16.MainResults

theorem source_eq48_49_conditional_probability_lower_bound {D E : ℕ}
    (Hx : Operator D) (V : Matrix (Fin D) (Fin E) ℂ)
    (hD : 0 < D) (hHx : Hx.IsHermitian) (hV : Vᴴ*V = 1) :
    gibbsPartition E (clampHamiltonian V Hx)/gibbsPartition D Hx ≤
      conditionalProbability D Hx (V*Vᴴ) :=
  clamped_trace_probability_lower_bound Hx V hD hHx hV

theorem source_eq50_discriminative_negative_log_likelihood_upper_bound
    {X Y : Type*} [Fintype X] [Fintype Y] {D E : ℕ}
    (hD : 0 < D) (hE : 0 < E) (Hx : X → Operator D)
    (hHx : ∀x,(Hx x).IsHermitian) (V : Y → Matrix (Fin D) (Fin E) ℂ)
    (hV : ∀y,(V y)ᴴ*V y = 1) (data : X → Y → ℝ) (hd : ∀x y,0 ≤ data x y) :
    -(∑x,∑y,data x y*Real.log (conditionalProbability D (Hx x) (V y*(V y)ᴴ))) ≤
      -(∑x,∑y,data x y*Real.log
        (gibbsPartition E (clampHamiltonian (V y) (Hx x))/gibbsPartition D (Hx x))) := by
  have hs : (∑x,∑y,data x y*Real.log
      (gibbsPartition E (clampHamiltonian (V y) (Hx x))/gibbsPartition D (Hx x))) ≤
      ∑x,∑y,data x y*Real.log (conditionalProbability D (Hx x) (V y*(V y)ᴴ)) := by
    apply Finset.sum_le_sum
    intro x _
    apply Finset.sum_le_sum
    intro y _
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (clamped_ratio_pos (V y) (Hx x) hD hE (hHx x))
        (source_eq48_49_conditional_probability_lower_bound (Hx x) (V y) hD (hHx x) (hV y))) (hd x y)
  linarith

theorem log_gibbs_hasDerivAt (D : ℕ) (hD : 0 < D) (H Hprime : ℝ → Operator D)
    (theta : ℝ) (hH : ∀t,HasDerivAt H (Hprime t) t)
    (hc : ContinuousAt Hprime theta) (hHerm : ∀t,(H t).IsHermitian) :
    HasDerivAt (fun t=>Real.log (gibbsPartition D (H t)))
      (-boltzmannAverage D (H theta) (Hprime theta)) theta := by
  have h := (gibbsPartition_hasDerivAt D hD H Hprime theta hH hc).log
    (gibbsPartition_pos D (H theta) hD (hHerm theta)).ne'
  simpa only [boltzmannAverage,Complex.neg_re,neg_div] using! h

theorem source_eq51_parameter_gradient
    {X Y : Type*} [Fintype X] [Fintype Y] {D E : ℕ}
    (hD : 0 < D) (hE : 0 < E) (Hx Hprime : X → ℝ → Operator D)
    (V : Y → Matrix (Fin D) (Fin E) ℂ) (data : X → Y → ℝ) (theta : ℝ)
    (hHx : ∀x t,HasDerivAt (Hx x) (Hprime x t) t)
    (hc : ∀x,ContinuousAt (Hprime x) theta)
    (hHerm : ∀x t,(Hx x t).IsHermitian) :
    HasDerivAt
      (fun t=>-(∑x,∑y,data x y*Real.log
        (gibbsPartition E (clampHamiltonian (V y) (Hx x t))/gibbsPartition D (Hx x t))))
      (∑x,∑y,data x y*
        (boltzmannAverage E (clampHamiltonian (V y) (Hx x theta))
            (clampHamiltonian (V y) (Hprime x theta)) -
          boltzmannAverage D (Hx x theta) (Hprime x theta))) theta := by
  have hr (x : X) (y : Y) : HasDerivAt
      (fun t=>Real.log
        (gibbsPartition E (clampHamiltonian (V y) (Hx x t))/gibbsPartition D (Hx x t)))
      (boltzmannAverage D (Hx x theta) (Hprime x theta) -
        boltzmannAverage E (clampHamiltonian (V y) (Hx x theta))
          (clampHamiltonian (V y) (Hprime x theta))) theta := by
    have h1 := log_gibbs_hasDerivAt E hE (fun t=>clampHamiltonian (V y) (Hx x t))
      (fun t=>clampHamiltonian (V y) (Hprime x t)) theta
      (fun t=>clamp_hasDerivAt (V y) (Hx x) (Hprime x t) t (hHx x t))
      (clamp_continuousAt (V y) (Hprime x) theta (hc x))
      (fun t=>clamp_hermitian (V y) (Hx x t) (hHerm x t))
    have h2 := log_gibbs_hasDerivAt D hD (Hx x) (Hprime x) theta (hHx x) (hc x) (hHerm x)
    have hdiff := h1.sub h2
    have hval : -boltzmannAverage E (clampHamiltonian (V y) (Hx x theta))
        (clampHamiltonian (V y) (Hprime x theta)) -
        -boltzmannAverage D (Hx x theta) (Hprime x theta) =
      boltzmannAverage D (Hx x theta) (Hprime x theta) -
        boltzmannAverage E (clampHamiltonian (V y) (Hx x theta))
          (clampHamiltonian (V y) (Hprime x theta)) := by ring
    rw [hval] at hdiff
    have heq : (fun t=>Real.log
        (gibbsPartition E (clampHamiltonian (V y) (Hx x t))/gibbsPartition D (Hx x t))) =ᶠ[𝓝 theta]
        (fun t=>Real.log (gibbsPartition E (clampHamiltonian (V y) (Hx x t))) -
          Real.log (gibbsPartition D (Hx x t))) :=
      Eventually.of_forall (fun t=>Real.log_div
        (gibbsPartition_pos E _ hE (clamp_hermitian (V y) (Hx x t) (hHerm x t))).ne'
        (gibbsPartition_pos D _ hD (hHerm x t)).ne')
    exact hdiff.congr_of_eventuallyEq heq
  have hs := HasDerivAt.sum (u := Finset.univ) (fun x _=>
    HasDerivAt.sum (u := Finset.univ) (fun y _=>(hr x y).const_mul (data x y)))
  have hfun : (∑x : X,∑y : Y,fun t : ℝ=>data x y*Real.log
        (gibbsPartition E (clampHamiltonian (V y) (Hx x t))/gibbsPartition D (Hx x t))) =
      (fun t : ℝ=>∑x,∑y,data x y*Real.log
        (gibbsPartition E (clampHamiltonian (V y) (Hx x t))/gibbsPartition D (Hx x t))) := by
    funext t
    simp only [Finset.sum_apply]
  rw [hfun] at hs
  have hn := hs.neg
  convert! hn using 1
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem source_discriminative_qbm_main
    {X Y : Type*} [Fintype X] [Fintype Y] {D E : ℕ}
    (hD : 0 < D) (hE : 0 < E) (Hx : X → Operator D)
    (hHx : ∀x,(Hx x).IsHermitian) (V : Y → Matrix (Fin D) (Fin E) ℂ)
    (hV : ∀y,(V y)ᴴ*V y = 1) (data : X → Y → ℝ) (hd : ∀x y,0 ≤ data x y) :
    (∀x y,gibbsPartition E (clampHamiltonian (V y) (Hx x))/gibbsPartition D (Hx x) ≤
      conditionalProbability D (Hx x) (V y*(V y)ᴴ)) ∧
    -(∑x,∑y,data x y*Real.log (conditionalProbability D (Hx x) (V y*(V y)ᴴ))) ≤
      -(∑x,∑y,data x y*Real.log
        (gibbsPartition E (clampHamiltonian (V y) (Hx x))/gibbsPartition D (Hx x))) :=
  ⟨fun x y=>source_eq48_49_conditional_probability_lower_bound (Hx x) (V y) hD (hHx x) (hV y),
    source_eq50_discriminative_negative_log_likelihood_upper_bound hD hE Hx hHx V hV data hd⟩
end Qatlib.Papers.QBoltzmann16.MainResults
