/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.CurlEigenstate.CKEigenstates
public import Qatlib.Papers.KnottedLight08.CurlEigenstate.HopfDipoleIntegrals
public import Qatlib.Papers.KnottedLight08.CurlEigenstate.HopfSpectralField

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Dipole curl eigenstate superposition for the Hopf pulse

The time-dependent Rañada field is a damped positive-frequency
superposition of the positive dipole curl modes. The modal value at
the spatial origin is supplied explicitly by the dipole's regular
radial normalization.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.CurlEigenstate

open MeasureTheory Set
open Qatlib.Papers.KnottedLight08.HopfField (ranadaField)
open Qatlib.Papers.KnotLight13.TorusFamily (complexDenominator)

/-- The positive dipole mode, using the regular radial value of its
curl partner at the spatial origin. -/
noncomputable def hopfDipoleMode (k x y z : ℝ) (j : Fin 3) : ℂ :=
  if ckRadius x y z = 0 then (k : ℂ) ^ 3 / 3 * ckConstantCurl j
  else ckBeltramiPlus k (x, y, z, 0) j

/-- The integral of each spatial component of the dipole pulse is
absolutely convergent and has the stated rational profile. -/
private theorem hopf_dipole_profile_integral (x y z t : ℝ) (j : Fin 3) :
    let a := 1 + Complex.I * (t : ℂ)
    let r := ckRadius x y z
    let D := a ^ 2 + (r : ℂ) ^ 2
    let U := fun k : ℝ => Complex.exp (-a * (k : ℂ)) * hopfDipoleMode k x y z j
    IntegrableOn U (Ioi 0) ∧
      (∫ k in Ioi (0 : ℝ), U k) =
        8 * a * ckAngular x y z j / D ^ 3 -
          8 * ckCurlAngular x y z j / D ^ 3 + 2 * ckConstantCurl j / D ^ 2 := by
  let a := 1 + Complex.I * (t : ℂ)
  let r := ckRadius x y z
  let D := a ^ 2 + (r : ℂ) ^ 2
  let E := fun k : ℝ => Complex.exp (-a * (k : ℂ))
  let U := fun k : ℝ => E k * hopfDipoleMode k x y z j
  have ha : 0 < a.re := by simp [a, Complex.add_re, Complex.mul_re]
  have hD : D ≠ 0 := hopf_time_radial_denominator_ne_zero r t
  change IntegrableOn U (Ioi 0) ∧ (∫ k in Ioi (0 : ℝ), U k) =
    8 * a * ckAngular x y z j / D ^ 3 - 8 * ckCurlAngular x y z j / D ^ 3 +
      2 * ckConstantCurl j / D ^ 2
  by_cases hr : r = 0
  · have hs : x ^ 2 + y ^ 2 + z ^ 2 = 0 :=
      (Real.sqrt_eq_zero (by positivity)).1 hr
    have hx : x = 0 := by
      by_contra hn
      exact (pow_ne_zero 2 hn) (by nlinarith [sq_nonneg y, sq_nonneg z])
    have hy : y = 0 := by
      by_contra hn
      exact (pow_ne_zero 2 hn) (by nlinarith [sq_nonneg x, sq_nonneg z])
    have hz : z = 0 := by
      by_contra hn
      exact (pow_ne_zero 2 hn) (by nlinarith [sq_nonneg x, sq_nonneg y])
    have hU : U = fun k : ℝ => (ckConstantCurl j / 3) * ((k : ℂ) ^ 3 * E k) := by
      funext k
      dsimp only [U]
      rw [hopfDipoleMode, ite_eq_left hr]
      ring
    rw [hU]
    refine ⟨(integrableOn_hopf_laplace_moment ha 3).const_mul _, ?_⟩
    rw [integral_const_mul, integral_hopf_laplace_moment ha 3]
    subst x y z
    have hD0 : D = a ^ 2 := by simp [D, r, ckRadius]
    rw [hD0]
    have ha₀ : a ≠ 0 := by
      intro h
      simp [h] at ha
    have hA0 : ckAngular 0 0 0 j = 0 := by
      fin_cases j <;> simp only [ckAngular, Complex.ofReal_zero, mul_zero, add_zero, neg_zero] <;> rfl
    have hB0 : ckCurlAngular 0 0 0 j = 0 := by
      fin_cases j <;> simp only [ckCurlAngular, Complex.ofReal_zero, mul_zero, zero_pow (by decide : 2 ≠ 0),
        add_zero, neg_zero, sub_zero] <;> rfl
    rw [hA0, hB0]
    norm_num [Nat.factorial]
    field_simp [ha₀]
    ring
  · let G := fun k : ℝ => E k * (ckKernel (k * r) : ℂ)
    let J := fun k : ℝ => E k * (k : ℂ) * (ckKernel (k * r) : ℂ)
    let H := fun k : ℝ => E k * ((k ^ 2 * r ^ 2 * Real.sin (k * r) - 3 * ckKernel (k * r) : ℝ) : ℂ)
    obtain ⟨hG, hJ, hH, hGv, hJv, hHv⟩ := hopf_dipole_radial_integrals ha r
    let A := ckAngular x y z j / (r : ℂ) ^ 3
    let B := ckCurlAngular x y z j / (r : ℂ) ^ 5
    let C := ckConstantCurl j / (r : ℂ) ^ 3
    have hU : U = fun k : ℝ => A * J k + B * H k + C * G k := by
      funext k
      dsimp only [U]
      rw [hopfDipoleMode, ite_eq_right hr]
      simp only [ckBeltramiPlus, ckMultipoleField, ckCurlMultipoleField, ckRadialComb]
      change E k * ((k : ℂ) * ((ckKernel (k * r) : ℂ) * ckAngular x y z j /
        ((r ^ 3 : ℝ) : ℂ)) +
        (((k ^ 2 * r ^ 2 * Real.sin (k * r) - 3 * ckKernel (k * r) : ℝ) : ℂ) *
          ckCurlAngular x y z j / ((r ^ 5 : ℝ) : ℂ) +
        (ckKernel (k * r) : ℂ) * ckConstantCurl j / ((r ^ 3 : ℝ) : ℂ))) = _
      dsimp only [A, B, C, J, H, G]
      push_cast
      ring
    have hA : IntegrableOn (fun k => A * J k) (Ioi 0) := hJ.const_mul A
    have hB : IntegrableOn (fun k => B * H k) (Ioi 0) := hH.const_mul B
    have hC : IntegrableOn (fun k => C * G k) (Ioi 0) := hG.const_mul C
    rw [hU]
    refine ⟨(hA.add hB).add hC, ?_⟩
    calc
      _ = (∫ k in Ioi (0 : ℝ), A * J k + B * H k) + ∫ k in Ioi (0 : ℝ), C * G k :=
        integral_add (hA.add hB) hC
      _ = ((∫ k in Ioi (0 : ℝ), A * J k) + ∫ k in Ioi (0 : ℝ), B * H k) +
          ∫ k in Ioi (0 : ℝ), C * G k := by
        exact congrArg (· + ∫ k in Ioi (0 : ℝ), C * G k) (integral_add hA hB)
      _ = _ := by
        rw [integral_const_mul, integral_const_mul, integral_const_mul, hJv, hHv, hGv]
        change A * (8 * a * (r : ℂ) ^ 3 / D ^ 3) +
          B * (-(8 * (r : ℂ) ^ 5) / D ^ 3) + C * (2 * (r : ℂ) ^ 3 / D ^ 2) = _
        dsimp only [A, B, C]
        field_simp [hD, Complex.ofReal_ne_zero.mpr hr]
        ring

/-- The actual spacetime Rañada field is the absolutely convergent
positive dipole curl-mode superposition, with its library normalization. -/
theorem ranadaField_eq_hopf_dipole_superposition (x y z t : ℝ) (j : Fin 3) :
    let a := 1 + Complex.I * (t : ℂ)
    let U := fun k : ℝ => Complex.exp (-a * (k : ℂ)) * hopfDipoleMode k x y z j
    IntegrableOn U (Ioi 0) ∧
      ranadaField x y z t j =
        (1 / (2 * (Real.pi : ℂ))) * ∫ k in Ioi (0 : ℝ), U k := by
  let a := 1 + Complex.I * (t : ℂ)
  let r := ckRadius x y z
  let D := a ^ 2 + (r : ℂ) ^ 2
  obtain ⟨hi, hval⟩ := hopf_dipole_profile_integral x y z t j
  refine ⟨hi, ?_⟩
  rw [hval, ranadaField_eq_hopf_null_secondDerivatives]
  simp only [second_deriv_hopfKernelNullSection]
  have hD : D = complexDenominator x y z t := hopf_time_denominator_eq x y z t
  rw [← hD]
  have hD₀ : D ≠ 0 := hopf_time_radial_denominator_ne_zero r t
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hrSq : (r : ℂ) ^ 2 = (x : ℂ) ^ 2 + (y : ℂ) ^ 2 + (z : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, show r ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 from Real.sq_sqrt (by positivity)]
    push_cast
    rfl
  fin_cases j <;>
    simp only [ckAngular, ckCurlAngular, ckConstantCurl] <;>
    field_simp [hD₀, hπ] <;>
    dsimp only [D, a] <;>
    rw [hrSq] <;>
    push_cast <;>
    ring_nf <;>
    norm_num [Complex.I_mul_I, pow_succ] <;>
    ring

end Qatlib.Papers.KnottedLight08.CurlEigenstate
