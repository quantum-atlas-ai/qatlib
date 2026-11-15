/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.UnbiasedBases.ThreeBasis.MUBProductBases
public import Qatlib.Concepts.UnbiasedBases.T0Neighborhood.CanonicalCertificate

@[expose] public section
open Qatlib.Foundations.PureStateMath Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis.MUB

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis

namespace Qatlib.Concepts.UnbiasedBases.T0Neighborhood.CanonicalBridge
open Qatlib.Concepts.UnbiasedBases.ThreeBasis Qatlib.Concepts.UnbiasedBases.ThreeBasis
open scoped Matrix

/-- Gives the explicit real and imaginary parts of the cube root of unity `omega`. -/
private theorem omega_formula : omega = -1 / 2 + (Real.sqrt 3 : ℂ) * Complex.I / 2 := by
  apply Complex.ext <;> simp [omega]

/-- Gives the explicit real and imaginary parts of the conjugate cube root of unity `omegaBar`. -/
private theorem omegaBar_formula : omegaBar = -1 / 2 - (Real.sqrt 3 : ℂ) * Complex.I / 2 := by
  apply Complex.ext <;> simp [omegaBar]

set_option maxHeartbeats 6000000 in

/-- Excludes a flat six-dimensional vector with first coordinate one having the prescribed
squared overlaps with every column of both `H` and `K`. -/
theorem no_flat_extension (z : QState (Fin 6)) (hz0 : z 0 = 1)
    (hz : ∀ i, Complex.normSq (z i) = 1)
    (hH : ∀ j, Complex.normSq (Inner (fun i => H i j) z) = 6)
    (hK : ∀ j, Complex.normSq (Inner (fun i => K i j) z) = 6) : False := by
  have he (i : Fin 6) : z i * (starRingEnd ℂ) (z i) - 1 = 0 := by
    rw [Complex.mul_conj, hz]; norm_num
  have hh (j : Fin 6) : Inner (fun i => H i j) z *
      (starRingEnd ℂ) (Inner (fun i => H i j) z) - 6 = 0 := by
    rw [Complex.mul_conj, hH]; norm_num
  have hk (j : Fin 6) : Inner (fun i => K i j) z *
      (starRingEnd ℂ) (Inner (fun i => K i j) z) - 6 = 0 := by
    rw [Complex.mul_conj, hK]; norm_num
  apply Qatlib.Concepts.UnbiasedBases.T0Neighborhood.no_solution (Real.sqrt 3 : ℂ)
    (z 1) (z 2) (z 3) (z 4) (z 5)
    ((starRingEnd ℂ) (z 1)) ((starRingEnd ℂ) (z 2))
    ((starRingEnd ℂ) (z 3)) ((starRingEnd ℂ) (z 4)) ((starRingEnd ℂ) (z 5))
  · exact_mod_cast (Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num))
  · exact he 1
  · exact he 2
  · exact he 3
  · exact he 4
  · exact he 5
  · convert hh 0 using 1
    simp [inner_apply, H, omega_formula, omegaBar_formula, Fin.sum_univ_succ, hz0]
    ring
  · convert hh 1 using 1
    simp [inner_apply, H, omega_formula, omegaBar_formula, Fin.sum_univ_succ, hz0, map_ofNat]
    norm_num
    ring
  · convert hh 2 using 1
    simp [inner_apply, H, omega_formula, omegaBar_formula, Fin.sum_univ_succ, hz0, map_ofNat]
    norm_num
    ring
  · convert hh 3 using 1
    simp [inner_apply, H, omega_formula, omegaBar_formula, Fin.sum_univ_succ, hz0]
    ring
  · convert hh 4 using 1
    simp [inner_apply, H, omega_formula, omegaBar_formula, Fin.sum_univ_succ, hz0, map_ofNat]
    norm_num
    ring
  · convert hk 0 using 1
    simp [inner_apply, K, omega_formula, omegaBar_formula, Fin.sum_univ_succ, hz0, map_ofNat]
    ring_nf
    norm_num [Complex.I_sq]
    ring
  · convert hk 1 using 1
    simp [inner_apply, K, omega_formula, omegaBar_formula, Fin.sum_univ_succ, hz0, map_ofNat]
    ring_nf
    norm_num [Complex.I_sq]
    ring
  · convert hk 2 using 1
    simp [inner_apply, K, omega_formula, omegaBar_formula, Fin.sum_univ_succ, hz0, map_ofNat]
    ring_nf
    norm_num [Complex.I_sq]
    ring
  · convert hk 3 using 1
    simp [inner_apply, K, omega_formula, omegaBar_formula, Fin.sum_univ_succ, hz0, map_ofNat]
    ring_nf
    norm_num [Complex.I_sq]
    ring
  · convert hk 4 using 1
    simp [inner_apply, K, omega_formula, omegaBar_formula, Fin.sum_univ_succ, hz0, map_ofNat]
    ring_nf
    norm_num [Complex.I_sq]
    ring

end Qatlib.Concepts.UnbiasedBases.T0Neighborhood.CanonicalBridge
