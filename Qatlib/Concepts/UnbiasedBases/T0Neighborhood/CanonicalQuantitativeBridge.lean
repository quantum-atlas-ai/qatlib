/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.UnbiasedBases.T0Neighborhood.CanonicalQuantitativeCertificate
public import Qatlib.Concepts.UnbiasedBases.ThreeBasis.MUBProductBases

@[expose] public section
open Qatlib.Foundations.PureStateMath Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis.MUB

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.UnbiasedBases.T0Neighborhood
open Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis

namespace Qatlib.Concepts.UnbiasedBases.T0Neighborhood.CanonicalQuantitativeBridge
open Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis

/-- Expresses `omega` in terms of the square root of three and the imaginary unit. -/
private theorem omega_formula : omega = -1 / 2 + (Real.sqrt 3 : ℂ) * Complex.I / 2 := by
  apply Complex.ext <;> simp [omega]

/-- Expresses `omegaBar` in terms of the square root of three and the imaginary unit. -/
private theorem omegaBar_formula : omegaBar = -1 / 2 - (Real.sqrt 3 : ℂ) * Complex.I / 2 := by
  apply Complex.ext <;> simp [omegaBar]

/-- Identifies the norm of the complex residual with the absolute squared-norm residual from
six. -/
private theorem norm_residual (u : ℂ) :
    ‖u * (starRingEnd ℂ) u - 6‖ = |Complex.normSq u - 6| := by
  have he : u * (starRingEnd ℂ) u - 6 = ((Complex.normSq u - 6 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.ofReal_sub]
    norm_num
  rw [he, Complex.norm_real, Real.norm_eq_abs]

set_option maxHeartbeats 8000000 in

/-- Bounds the common overlap residual below by the reciprocal of 93429342244 for a flat vector
with first coordinate one. -/
theorem flat_residual_barrier (z : QState (Fin 6)) (hz0 : z 0 = 1)
    (hz : ∀ i, Complex.normSq (z i) = 1) (η : ℝ) (hη : 0 ≤ η)
    (hH : ∀ j, |Complex.normSq (Inner (fun i => H i j) z) - 6| ≤ η)
    (hK : ∀ j, |Complex.normSq (Inner (fun i => K i j) z) - 6| ≤ η) :
    (1 : ℝ) ≤ 93429342244 * η := by
  have hrN : ‖(Real.sqrt 3 : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 3)]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  have hn (i : Fin 6) : ‖z i‖ ≤ 1 := by
    have h := hz i
    rw [Complex.normSq_eq_norm_sq] at h
    nlinarith [norm_nonneg (z i)]
  have he (i : Fin 6) : ‖z i * (starRingEnd ℂ) (z i) - 1‖ ≤ η := by
    simpa only [Complex.mul_conj, hz, Complex.ofReal_one, sub_self, norm_zero] using hη
  have hh (j : Fin 6) : ‖Inner (fun i => H i j) z *
      (starRingEnd ℂ) (Inner (fun i => H i j) z) - 6‖ ≤ η := by
    rw [norm_residual]
    exact hH j
  have hk (j : Fin 6) : ‖Inner (fun i => K i j) z *
      (starRingEnd ℂ) (Inner (fun i => K i j) z) - 6‖ ≤ η := by
    rw [norm_residual]
    exact hK j
  apply certificate_barrier (Real.sqrt 3 : ℂ) (z 1) (z 2) (z 3) (z 4) (z 5)
    ((starRingEnd ℂ) (z 1)) ((starRingEnd ℂ) (z 2)) ((starRingEnd ℂ) (z 3))
    ((starRingEnd ℂ) (z 4)) ((starRingEnd ℂ) (z 5)) η
  · exact_mod_cast (Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num))
  · exact hrN
  · exact hn 2
  · exact hn 3
  · exact hn 4
  · exact hn 5
  · simpa only [Complex.norm_conj] using hn 1
  · simpa only [Complex.norm_conj] using hn 2
  · simpa only [Complex.norm_conj] using hn 3
  · simpa only [Complex.norm_conj] using hn 4
  · simpa only [Complex.norm_conj] using hn 5
  · exact he 1
  · exact he 2
  · exact he 3
  · exact he 4
  · exact he 5
  · have heq : (((z 1) + (z 2) + (z 3) + (z 4) + (z 5) + 1) * (((starRingEnd ℂ) (z 1)) + ((starRingEnd ℂ) (z 2)) + ((starRingEnd ℂ) (z 3)) + ((starRingEnd ℂ) (z 4)) + ((starRingEnd ℂ) (z 5)) + 1) - 6 : ℂ) =
        Inner (fun i => H i 0) z * (starRingEnd ℂ) (Inner (fun i => H i 0) z) - 6 := by
      simp [inner_apply, H, omega_formula, omegaBar_formula, Fin.sum_univ_succ, hz0]
      ring
    rw [heq]
    exact hh 0
  · have heq : (((z 1)*(-1/2 - (Real.sqrt 3 : ℂ)*Complex.I/2) + (z 2)*(-1/2 + (Real.sqrt 3 : ℂ)*Complex.I/2) + (z 3) + (z 4)*(-1/2 - (Real.sqrt 3 : ℂ)*Complex.I/2) + (z 5)*(-1/2 + (Real.sqrt 3 : ℂ)*Complex.I/2) + 1) * (((starRingEnd ℂ) (z 1))*(-1/2 + (Real.sqrt 3 : ℂ)*Complex.I/2) + ((starRingEnd ℂ) (z 2))*(-1/2 - (Real.sqrt 3 : ℂ)*Complex.I/2) + ((starRingEnd ℂ) (z 3)) + ((starRingEnd ℂ) (z 4))*(-1/2 + (Real.sqrt 3 : ℂ)*Complex.I/2) + ((starRingEnd ℂ) (z 5))*(-1/2 - (Real.sqrt 3 : ℂ)*Complex.I/2) + 1) - 6 : ℂ) =
        Inner (fun i => H i 1) z * (starRingEnd ℂ) (Inner (fun i => H i 1) z) - 6 := by
      simp [inner_apply, H, omega_formula, omegaBar_formula, Fin.sum_univ_succ, hz0, map_ofNat]
      norm_num
      ring
    rw [heq]
    exact hh 1
  · have heq : (((z 1)*(-1/2 + (Real.sqrt 3 : ℂ)*Complex.I/2) + (z 2)*(-1/2 - (Real.sqrt 3 : ℂ)*Complex.I/2) + (z 3) + (z 4)*(-1/2 + (Real.sqrt 3 : ℂ)*Complex.I/2) + (z 5)*(-1/2 - (Real.sqrt 3 : ℂ)*Complex.I/2) + 1) * (((starRingEnd ℂ) (z 1))*(-1/2 - (Real.sqrt 3 : ℂ)*Complex.I/2) + ((starRingEnd ℂ) (z 2))*(-1/2 + (Real.sqrt 3 : ℂ)*Complex.I/2) + ((starRingEnd ℂ) (z 3)) + ((starRingEnd ℂ) (z 4))*(-1/2 - (Real.sqrt 3 : ℂ)*Complex.I/2) + ((starRingEnd ℂ) (z 5))*(-1/2 + (Real.sqrt 3 : ℂ)*Complex.I/2) + 1) - 6 : ℂ) =
        Inner (fun i => H i 2) z * (starRingEnd ℂ) (Inner (fun i => H i 2) z) - 6 := by
      simp [inner_apply, H, omega_formula, omegaBar_formula, Fin.sum_univ_succ, hz0, map_ofNat]
      norm_num
      ring
    rw [heq]
    exact hh 2
  · have heq : (((z 1) + (z 2) - (z 3) - (z 4) - (z 5) + 1) * (((starRingEnd ℂ) (z 1)) + ((starRingEnd ℂ) (z 2)) - ((starRingEnd ℂ) (z 3)) - ((starRingEnd ℂ) (z 4)) - ((starRingEnd ℂ) (z 5)) + 1) - 6 : ℂ) =
        Inner (fun i => H i 3) z * (starRingEnd ℂ) (Inner (fun i => H i 3) z) - 6 := by
      simp [inner_apply, H, omega_formula, omegaBar_formula, Fin.sum_univ_succ, hz0]
      ring
    rw [heq]
    exact hh 3
  · have heq : (((z 1)*(-1/2 - (Real.sqrt 3 : ℂ)*Complex.I/2) + (z 2)*(-1/2 + (Real.sqrt 3 : ℂ)*Complex.I/2) - (z 3) + (z 4)*(1/2 + (Real.sqrt 3 : ℂ)*Complex.I/2) + (z 5)*(1/2 - (Real.sqrt 3 : ℂ)*Complex.I/2) + 1) * (((starRingEnd ℂ) (z 1))*(-1/2 + (Real.sqrt 3 : ℂ)*Complex.I/2) + ((starRingEnd ℂ) (z 2))*(-1/2 - (Real.sqrt 3 : ℂ)*Complex.I/2) - ((starRingEnd ℂ) (z 3)) + ((starRingEnd ℂ) (z 4))*(1/2 - (Real.sqrt 3 : ℂ)*Complex.I/2) + ((starRingEnd ℂ) (z 5))*(1/2 + (Real.sqrt 3 : ℂ)*Complex.I/2) + 1) - 6 : ℂ) =
        Inner (fun i => H i 4) z * (starRingEnd ℂ) (Inner (fun i => H i 4) z) - 6 := by
      simp [inner_apply, H, omega_formula, omegaBar_formula, Fin.sum_univ_succ, hz0, map_ofNat]
      norm_num
      ring
    rw [heq]
    exact hh 4
  · have heq : (((z 1)*(-1/2 - (Real.sqrt 3 : ℂ)*Complex.I/2) + (z 2)*(-1/2 - (Real.sqrt 3 : ℂ)*Complex.I/2) - Complex.I*(z 3) + (z 4)*(-(Real.sqrt 3 : ℂ)/2 + Complex.I/2) + (z 5)*(-(Real.sqrt 3 : ℂ)/2 + Complex.I/2) + 1) * (((starRingEnd ℂ) (z 1))*(-1/2 + (Real.sqrt 3 : ℂ)*Complex.I/2) + ((starRingEnd ℂ) (z 2))*(-1/2 + (Real.sqrt 3 : ℂ)*Complex.I/2) + Complex.I*((starRingEnd ℂ) (z 3)) + ((starRingEnd ℂ) (z 4))*(-(Real.sqrt 3 : ℂ)/2 - Complex.I/2) + ((starRingEnd ℂ) (z 5))*(-(Real.sqrt 3 : ℂ)/2 - Complex.I/2) + 1) - 6 : ℂ) =
        Inner (fun i => K i 0) z * (starRingEnd ℂ) (Inner (fun i => K i 0) z) - 6 := by
      simp [inner_apply, K, omega_formula, omegaBar_formula, Fin.sum_univ_succ, hz0, map_ofNat]
      ring_nf
      norm_num [Complex.I_sq]
      ring
    rw [heq]
    exact hk 0
  · have heq : (((z 1)*(-1/2 + (Real.sqrt 3 : ℂ)*Complex.I/2) + (z 2) - Complex.I*(z 3) + (z 4)*((Real.sqrt 3 : ℂ)/2 + Complex.I/2) - Complex.I*(z 5) + 1) * (((starRingEnd ℂ) (z 1))*(-1/2 - (Real.sqrt 3 : ℂ)*Complex.I/2) + ((starRingEnd ℂ) (z 2)) + Complex.I*((starRingEnd ℂ) (z 3)) + ((starRingEnd ℂ) (z 4))*((Real.sqrt 3 : ℂ)/2 - Complex.I/2) + Complex.I*((starRingEnd ℂ) (z 5)) + 1) - 6 : ℂ) =
        Inner (fun i => K i 1) z * (starRingEnd ℂ) (Inner (fun i => K i 1) z) - 6 := by
      simp [inner_apply, K, omega_formula, omegaBar_formula, Fin.sum_univ_succ, hz0, map_ofNat]
      ring_nf
      norm_num [Complex.I_sq]
      ring
    rw [heq]
    exact hk 1
  · have heq : (((z 1) + (z 2)*(-1/2 + (Real.sqrt 3 : ℂ)*Complex.I/2) - Complex.I*(z 3) - Complex.I*(z 4) + (z 5)*((Real.sqrt 3 : ℂ)/2 + Complex.I/2) + 1) * (((starRingEnd ℂ) (z 1)) + ((starRingEnd ℂ) (z 2))*(-1/2 - (Real.sqrt 3 : ℂ)*Complex.I/2) + Complex.I*((starRingEnd ℂ) (z 3)) + Complex.I*((starRingEnd ℂ) (z 4)) + ((starRingEnd ℂ) (z 5))*((Real.sqrt 3 : ℂ)/2 - Complex.I/2) + 1) - 6 : ℂ) =
        Inner (fun i => K i 2) z * (starRingEnd ℂ) (Inner (fun i => K i 2) z) - 6 := by
      simp [inner_apply, K, omega_formula, omegaBar_formula, Fin.sum_univ_succ, hz0, map_ofNat]
      ring_nf
      norm_num [Complex.I_sq]
      ring
    rw [heq]
    exact hk 2
  · have heq : (((z 1)*(-1/2 - (Real.sqrt 3 : ℂ)*Complex.I/2) + (z 2)*(-1/2 - (Real.sqrt 3 : ℂ)*Complex.I/2) + Complex.I*(z 3) + (z 4)*((Real.sqrt 3 : ℂ)/2 - Complex.I/2) + (z 5)*((Real.sqrt 3 : ℂ)/2 - Complex.I/2) + 1) * (((starRingEnd ℂ) (z 1))*(-1/2 + (Real.sqrt 3 : ℂ)*Complex.I/2) + ((starRingEnd ℂ) (z 2))*(-1/2 + (Real.sqrt 3 : ℂ)*Complex.I/2) - Complex.I*((starRingEnd ℂ) (z 3)) + ((starRingEnd ℂ) (z 4))*((Real.sqrt 3 : ℂ)/2 + Complex.I/2) + ((starRingEnd ℂ) (z 5))*((Real.sqrt 3 : ℂ)/2 + Complex.I/2) + 1) - 6 : ℂ) =
        Inner (fun i => K i 3) z * (starRingEnd ℂ) (Inner (fun i => K i 3) z) - 6 := by
      simp [inner_apply, K, omega_formula, omegaBar_formula, Fin.sum_univ_succ, hz0, map_ofNat]
      ring_nf
      norm_num [Complex.I_sq]
      ring
    rw [heq]
    exact hk 3
  · have heq : (((z 1)*(-1/2 + (Real.sqrt 3 : ℂ)*Complex.I/2) + (z 2) + Complex.I*(z 3) + (z 4)*(-(Real.sqrt 3 : ℂ)/2 - Complex.I/2) + Complex.I*(z 5) + 1) * (((starRingEnd ℂ) (z 1))*(-1/2 - (Real.sqrt 3 : ℂ)*Complex.I/2) + ((starRingEnd ℂ) (z 2)) - Complex.I*((starRingEnd ℂ) (z 3)) + ((starRingEnd ℂ) (z 4))*(-(Real.sqrt 3 : ℂ)/2 + Complex.I/2) - Complex.I*((starRingEnd ℂ) (z 5)) + 1) - 6 : ℂ) =
        Inner (fun i => K i 4) z * (starRingEnd ℂ) (Inner (fun i => K i 4) z) - 6 := by
      simp [inner_apply, K, omega_formula, omegaBar_formula, Fin.sum_univ_succ, hz0, map_ofNat]
      ring_nf
      norm_num [Complex.I_sq]
      ring
    rw [heq]
    exact hk 4

end Qatlib.Concepts.UnbiasedBases.T0Neighborhood.CanonicalQuantitativeBridge
