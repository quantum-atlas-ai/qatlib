/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.HopfField.RanadaField

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The spectral kernel of the Hopf pulse

[IrvineBouwmeester2008KnottedLight], p. 718 and Supplementary Methods 1,
[DOI](https://doi.org/10.1038/nphys1056).
The exponential factor `e^{-k}` in equation (4) turns the radial
sine kernel of the supplementary equation (8) into the Lorentzian
`1/(1+r²)` through the Laplace–sine integral
`∫₀^∞ e^{-k} sin(rk)/r dk = 1/(1+r²)`, which has no radial zeros.
The vector-potential weight in equation (4) integrates to
`∫₀^∞ k³ e^{-k} dk = 6`. Equation (5) gives the energy spectrum
`S(ω) ∝ ω e^{-ω}`. At time zero the `x`-component of the Rañada magnetic field equals
`(∂²_y + ∂²_z) [1/(1+r²)] / (2π)` in the library's Rañada convention.
This gives the transverse differential profile of Supplementary Methods
equation (8). The library's initial component has a factor `-2` relative
to the component in Supplementary Methods equation (4).
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.CurlEigenstate

open Qatlib.Papers.KnottedLight08.HopfField (ranadaB etaSumSq etaHomog etaNum etaDen
  etaNumGrad etaDenGrad etaNumX etaNumY etaNumZ etaDenX etaDenY etaDenZ
  etaNumGrad_one etaNumGrad_two etaDenGrad_one etaDenGrad_two)
open Qatlib.Papers.KnottedLight08.HopfField (ranadaA ranadaP ranadaQ ranadaR ranadaS)
open Qatlib.Papers.KnottedLight08.HopfField (cross3)
open scoped ComplexConjugate

/-! ### The Laplace–sine transform of the pulse weight -/

/-- The Laplace–sine transform of the pulse weight: the exponential `e^{-k}`
of the spectrum turns the radial sine into the rational profile
`r/(1+r²)`. -/
theorem integral_exp_mul_sin (r : ℝ) :
    ∫ k in Set.Ioi 0, Real.exp (-k) * Real.sin (r * k) = r / (1 + r ^ 2) := by
  have hre : (-1 + Complex.I * r).re < 0 := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  have hexp : ∀ k : ℝ, Complex.exp ((-1 + Complex.I * r) * k)
      = ((Real.exp (-k) * Real.cos (r * k) : ℝ) : ℂ)
        + Complex.I * ((Real.exp (-k) * Real.sin (r * k) : ℝ) : ℂ) := by
    intro k
    have h1 : (-1 + Complex.I * r) * k
        = -((k : ℂ)) + ((r * k : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h1, Complex.exp_add, show (-((k : ℂ))) = ((-k : ℝ) : ℂ) from by push_cast; ring,
      ← Complex.ofReal_exp, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  have hint := integral_exp_mul_complex_Ioi hre 0
  have hinteg : MeasureTheory.Integrable (fun k : ℝ => Complex.exp ((-1 + Complex.I * r) * k))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    integrableOn_exp_mul_complex_Ioi hre 0
  have him := integral_im (f := fun k : ℝ => Complex.exp ((-1 + Complex.I * r) * k))
    (μ := MeasureTheory.volume.restrict (Set.Ioi 0)) hinteg
  have him' : RCLike.im (∫ (k : ℝ) in Set.Ioi 0, Complex.exp ((-1 + Complex.I * r) * k))
      = ∫ (k : ℝ) in Set.Ioi 0, RCLike.im (Complex.exp ((-1 + Complex.I * r) * k)) :=
    him.symm
  have hEq : (fun k : ℝ => RCLike.im (Complex.exp ((-1 + Complex.I * r) * k)))
      = fun k : ℝ => Real.exp (-k) * Real.sin (r * k) := by
    funext k
    rw [hexp k, RCLike.im_eq_complex_im]
    simp only [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.I_re,
      Complex.ofReal_im, Complex.ofReal_re]
    ring
  have hns : Complex.normSq (-1 + Complex.I * r) = 1 + r ^ 2 := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
    ring
  have hima : (-1 + Complex.I * r).im = r := by
    simp [Complex.add_im, Complex.mul_im, Complex.I_im, Complex.neg_im]
  have hval : RCLike.im (-Complex.exp ((-1 + Complex.I * r) * ((0 : ℝ) : ℂ))
      / (-1 + Complex.I * r)) = r / (1 + r ^ 2) := by
    rw [RCLike.im_eq_complex_im, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      div_eq_inv_mul, mul_neg_one, Complex.neg_im, Complex.inv_im, hns, hima]
    ring
  rw [← hEq, ← him', hint, hval]

/-- Dividing the Laplace–sine transform by the radius gives the Lorentzian
spectral kernel of the supplementary equation (8). -/
theorem hopfSpectralKernel {r : ℝ} (hr : r ≠ 0) :
    (∫ k in Set.Ioi 0, Real.exp (-k) * Real.sin (r * k)) / r = 1 / (1 + r ^ 2) := by
  rw [integral_exp_mul_sin]
  field_simp

/-- The spectral kernel `1/(1+r²)` never vanishes: the exponential pulse
spectrum removes all radial zeros of the mode functions. -/
theorem hopfKernel_ne_zero (r : ℝ) : 1 / (1 + r ^ 2) ≠ 0 :=
  one_div_ne_zero (ne_of_gt (by positivity))

/-! ### The spectral weight integral -/

/-- The moments of the pulse weight are the factorials, by Euler's integral
for the Gamma function. -/
theorem integral_pow_exp_neg (n : ℕ) :
    ∫ k in Set.Ioi 0, Real.exp (-k) * k ^ n = (Nat.factorial n : ℝ) := by
  have h := Real.Gamma_eq_integral (s := (n : ℝ) + 1) (by positivity)
  rw [Real.Gamma_nat_eq_factorial] at h
  rw [show ((n : ℝ) + 1) - 1 = (n : ℝ) from by ring] at h
  simpa only [Real.rpow_natCast] using h.symm

/-- The vector-potential weight `k³ e^{-k}` in equation (4) integrates to `6`. -/
theorem hopfSpectralWeightIntegral :
    ∫ k in Set.Ioi 0, Real.exp (-k) * k ^ 3 = 6 := by
  have h := integral_pow_exp_neg 3
  norm_num at h ⊢
  exact h

/-! ### Second partials of the Lorentzian kernel -/

/-- The `y`-section derivative of the Lorentzian kernel. -/
theorem hasDerivAt_lorentzian_y (x y z : ℝ) :
    HasDerivAt (fun yy => 1 / (1 + x ^ 2 + yy ^ 2 + z ^ 2))
      (-(2 * y) / (1 + x ^ 2 + y ^ 2 + z ^ 2) ^ 2) y := by
  have hid : HasDerivAt (fun yy => yy) 1 y := hasDerivAt_id y
  have hQ : HasDerivAt (fun yy => 1 + x ^ 2 + yy ^ 2 + z ^ 2) (2 * y) y := by
    refine HasDerivAt.congr_deriv
      (HasDerivAt.fun_add
        (HasDerivAt.fun_add
          (HasDerivAt.fun_add (hasDerivAt_const y 1) (hasDerivAt_const y (x ^ 2)))
          (hid.pow 2))
        (hasDerivAt_const y (z ^ 2))) ?_
    ring
  refine HasDerivAt.congr_deriv
    ((hasDerivAt_const y (1 : ℝ)).fun_div hQ (by positivity)) ?_
  field_simp
  ring

/-- The `z`-section derivative of the Lorentzian kernel. -/
theorem hasDerivAt_lorentzian_z (x y z : ℝ) :
    HasDerivAt (fun zz => 1 / (1 + x ^ 2 + y ^ 2 + zz ^ 2))
      (-(2 * z) / (1 + x ^ 2 + y ^ 2 + z ^ 2) ^ 2) z := by
  have hid : HasDerivAt (fun zz => zz) 1 z := hasDerivAt_id z
  have hQ : HasDerivAt (fun zz => 1 + x ^ 2 + y ^ 2 + zz ^ 2) (2 * z) z := by
    refine HasDerivAt.congr_deriv
      (HasDerivAt.fun_add
        (HasDerivAt.fun_add
          (HasDerivAt.fun_add (hasDerivAt_const z 1) (hasDerivAt_const z (x ^ 2)))
          (hasDerivAt_const z (y ^ 2)))
        (hid.pow 2)) ?_
    ring
  refine HasDerivAt.congr_deriv
    ((hasDerivAt_const z (1 : ℝ)).fun_div hQ (by positivity)) ?_
  field_simp
  ring

/-- The second `y`-section derivative of the Lorentzian kernel. -/
theorem hasDerivAt_lorentzian_yy (x y z : ℝ) :
    HasDerivAt (fun yy => -2 * yy / (1 + x ^ 2 + yy ^ 2 + z ^ 2) ^ 2)
      (-(2 / (1 + x ^ 2 + y ^ 2 + z ^ 2) ^ 2)
        + 8 * y ^ 2 / (1 + x ^ 2 + y ^ 2 + z ^ 2) ^ 3) y := by
  have hid : HasDerivAt (fun yy => yy) 1 y := hasDerivAt_id y
  have hQ : HasDerivAt (fun yy => (1 + x ^ 2 + yy ^ 2 + z ^ 2) ^ 2)
      (2 * (1 + x ^ 2 + y ^ 2 + z ^ 2) * (2 * y)) y := by
    refine HasDerivAt.congr_deriv
      ((HasDerivAt.fun_add
        (HasDerivAt.fun_add
          (HasDerivAt.fun_add (hasDerivAt_const y 1) (hasDerivAt_const y (x ^ 2)))
          (hid.pow 2))
        (hasDerivAt_const y (z ^ 2))).pow 2) ?_
    simp only [Pi.pow_apply]
    ring
  have hnum : HasDerivAt (fun yy => -2 * yy) (-2 : ℝ) y := by
    refine HasDerivAt.congr_deriv
      (HasDerivAt.fun_mul (hasDerivAt_const y (-2 : ℝ)) hid) ?_
    ring
  refine HasDerivAt.congr_deriv (hnum.fun_div hQ (by positivity)) ?_
  field_simp
  ring

/-- The second `z`-section derivative of the Lorentzian kernel. -/
theorem hasDerivAt_lorentzian_zz (x y z : ℝ) :
    HasDerivAt (fun zz => -2 * zz / (1 + x ^ 2 + y ^ 2 + zz ^ 2) ^ 2)
      (-(2 / (1 + x ^ 2 + y ^ 2 + z ^ 2) ^ 2)
        + 8 * z ^ 2 / (1 + x ^ 2 + y ^ 2 + z ^ 2) ^ 3) z := by
  have hid : HasDerivAt (fun zz => zz) 1 z := hasDerivAt_id z
  have hQ : HasDerivAt (fun zz => (1 + x ^ 2 + y ^ 2 + zz ^ 2) ^ 2)
      (2 * (1 + x ^ 2 + y ^ 2 + z ^ 2) * (2 * z)) z := by
    refine HasDerivAt.congr_deriv
      ((HasDerivAt.fun_add
        (HasDerivAt.fun_add
          (HasDerivAt.fun_add (hasDerivAt_const z 1) (hasDerivAt_const z (x ^ 2)))
          (hasDerivAt_const z (y ^ 2)))
        (hid.pow 2)).pow 2) ?_
    simp only [Pi.pow_apply]
    ring
  have hnum : HasDerivAt (fun zz => -2 * zz) (-2 : ℝ) z := by
    refine HasDerivAt.congr_deriv
      (HasDerivAt.fun_mul (hasDerivAt_const z (-2 : ℝ)) hid) ?_
    ring
  refine HasDerivAt.congr_deriv (hnum.fun_div hQ (by positivity)) ?_
  field_simp
  ring

/-- The transverse second derivative of the Lorentzian kernel in closed
form. -/
theorem lorentzian_lap_yz (x y z : ℝ) :
    deriv (fun yy => deriv (fun yy' => 1 / (1 + x ^ 2 + yy' ^ 2 + z ^ 2)) yy) y
      + deriv (fun zz => deriv (fun zz' => 1 / (1 + x ^ 2 + y ^ 2 + zz' ^ 2)) zz) z
      = -4 * (1 + x ^ 2 - y ^ 2 - z ^ 2) / (1 + x ^ 2 + y ^ 2 + z ^ 2) ^ 3 := by
  have hfy : (fun yy => deriv (fun yy' => 1 / (1 + x ^ 2 + yy' ^ 2 + z ^ 2)) yy)
      = fun yy => -2 * yy / (1 + x ^ 2 + yy ^ 2 + z ^ 2) ^ 2 :=
    funext fun yy => by rw [(hasDerivAt_lorentzian_y x yy z).deriv]; ring
  have hfz : (fun zz => deriv (fun zz' => 1 / (1 + x ^ 2 + y ^ 2 + zz' ^ 2)) zz)
      = fun zz => -2 * zz / (1 + x ^ 2 + y ^ 2 + zz ^ 2) ^ 2 :=
    funext fun zz => by rw [(hasDerivAt_lorentzian_z x y zz).deriv]; ring
  rw [hfy, hfz, (hasDerivAt_lorentzian_yy x y z).deriv,
    (hasDerivAt_lorentzian_zz x y z).deriv]
  field_simp
  ring

/-! ### The initial Rañada field from the spectral kernel -/

/-- The squared-modulus denominator of the magnetic field at time zero is
the fourth power of `1 + r²` over `16`. -/
theorem etaSumSq_t_zero (x y z : ℝ) :
    etaSumSq x y z 0 = (((1 + x ^ 2 + y ^ 2 + z ^ 2) ^ 4 / 16 : ℝ) : ℂ) := by
  simp only [etaSumSq, etaNum, etaDen, ranadaQ, ranadaR, ranadaP, ranadaS, ranadaA,
    Complex.mul_conj, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  push_cast
  ring

/-- The `1/(4πi)` prefactor cancels the `2i` produced by the cross product of
a vector with its own conjugate, leaving a `1/(2π)` real prefactor. -/
theorem half_prefactor_cancel (c : ℂ) :
    (1 / (4 * Real.pi * Complex.I)) * (2 * Complex.I * c) = c / (2 * Real.pi) := by
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hpi : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (by positivity)
  have h4 : (((4 * Real.pi : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (by positivity)
  field_simp
  norm_num

set_option maxRecDepth 12000 in
/-- At time zero the `x`-component of the Rañada magnetic field has the
explicit rational closed form. -/
theorem ranadaB_initial_zero (x y z : ℝ) :
    ranadaB x y z 0 0 = ((-2 / Real.pi * (1 + x ^ 2 - y ^ 2 - z ^ 2)
        / (1 + x ^ 2 + y ^ 2 + z ^ 2) ^ 3 : ℝ) : ℂ) := by
  have hD : (((1 + x ^ 2 + y ^ 2 + z ^ 2) ^ 4 / 16 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  have hD2 : (((1 + x ^ 2 + y ^ 2 + z ^ 2) ^ 4 / 16 : ℝ) : ℂ) ^ 2 ≠ 0 :=
    pow_ne_zero _ hD
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hcross : cross3 (etaHomog x y z 0) (fun k => conj (etaHomog x y z 0 k)) 0
      = (2 * Complex.I) * ((-((1 + x ^ 2 - y ^ 2 - z ^ 2)
          * (1 + x ^ 2 + y ^ 2 + z ^ 2) ^ 5 / 64 : ℝ)) : ℂ) := by
    simp only [cross3, Matrix.cons_val_zero, etaHomog,
      etaNumGrad_one, etaNumGrad_two, etaDenGrad_one, etaDenGrad_two,
      etaNum, etaDen, etaNumY, etaNumZ, etaDenY, etaDenZ,
      ranadaQ, ranadaR, ranadaP, ranadaS, ranadaA,
      map_add, map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal]
    refine Complex.ext_iff.2 ⟨?_, ?_⟩ <;>
      · simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
          Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
        norm_num
        ring
  simp only [ranadaB]
  rw [hcross, etaSumSq_t_zero, half_prefactor_cancel]
  push_cast
  field_simp
  ring

/-- Component zero of the initial Rañada magnetic field is the transverse
second derivative of the Lorentzian spectral kernel, scaled by `1/(2π)`. -/
theorem ranadaB_initial_spectral (x y z : ℝ) :
    ranadaB x y z 0 0 = ((1 / (2 * Real.pi)
        * (deriv (fun yy => deriv (fun yy' => 1 / (1 + x ^ 2 + yy' ^ 2 + z ^ 2)) yy) y
          + deriv (fun zz => deriv (fun zz' => 1 / (1 + x ^ 2 + y ^ 2 + zz' ^ 2)) zz) z)
        : ℝ) : ℂ) := by
  rw [lorentzian_lap_yz x y z, ranadaB_initial_zero]
  push_cast
  field_simp
  ring

end Qatlib.Papers.KnottedLight08.CurlEigenstate
