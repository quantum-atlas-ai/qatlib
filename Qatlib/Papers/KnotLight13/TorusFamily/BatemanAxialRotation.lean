/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.PowerLineLevels
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanPoyntingRays

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Axial rotation and electric–magnetic duality of the Bateman powers

[Kedia2013TyingKnots], discussion of Fig. 2. The spatial rotation
changes the second scalar by a unit phase and leaves the first fixed.
After removing the spatial rotation of the vector components, the true
powered field acquires the `q`-th power of that phase. In particular the
positive axial angle `π / (2q)` exchanges the electric and magnetic
directions with the Maxwell duality sign.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Qatlib.Papers.KnotLight13.TorusFamily (radialAux rationalAlpha rationalBeta)
open scoped Real

/-- The positive-angle rotation on Cartesian components, over either
the real or the complex scalars. -/
def axialRotateVector {K : Type*} [CommRing K] (c s : K) (v : Fin 3 → K) : Fin 3 → K :=
  ![c * v 0 - s * v 1, s * v 0 + c * v 1, v 2]

/-- The physical rotation on a time slice about its vertical axis. -/
noncomputable def batemanAxialRotation (θ : ℝ) (s : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  (Real.cos θ * s.1 - Real.sin θ * s.2.1,
    Real.sin θ * s.1 + Real.cos θ * s.2.1, s.2.2)

/-- The complex phase of the rotated second Bateman coordinate. -/
noncomputable def batemanAxialPhase (θ : ℝ) : ℂ :=
  Complex.exp (-(θ : ℂ) * Complex.I)

/-- The axial phase in Cartesian real and imaginary coordinates. -/
theorem batemanAxialPhase_eq (θ : ℝ) :
    batemanAxialPhase θ = (Real.cos θ : ℂ) - Complex.I * (Real.sin θ : ℂ) := by
  simp only [batemanAxialPhase, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    Complex.ofReal_cos, Complex.ofReal_sin]
  ring

/-- Rotating the horizontal coordinates leaves their combined square unchanged. -/
private theorem radialAux_axialRotation (θ x y z t : ℝ) :
    let r := batemanAxialRotation θ (x, y, z)
    radialAux r.1 r.2.1 z t = radialAux x y z t := by
  simp only [batemanAxialRotation, radialAux]
  linear_combination (x ^ 2 + y ^ 2) * Real.sin_sq_add_cos_sq θ

/-- The reduced second scalar transforms with the exact complex phase. -/
private theorem betaReduced_axialRotation (θ x y z : ℝ) :
    let r := batemanAxialRotation θ (x, y, z)
    betaReducedNumerator r.1 r.2.1 = batemanAxialPhase θ * betaReducedNumerator x y := by
  simp only [batemanAxialRotation, batemanAxialPhase_eq, betaReducedNumerator,
    Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul]
  linear_combination -((Real.sin θ : ℂ) * (y : ℂ)) * Complex.I_sq

/-- The two scalar potentials transform by the identity and the axial
phase, respectively. -/
theorem batemanPair_axialRotation (θ x y z t : ℝ) :
    batemanPairAt t (batemanAxialRotation θ (x, y, z)) =
      (rationalAlpha x y z t, batemanAxialPhase θ * rationalBeta x y z t) := by
  let r := batemanAxialRotation θ (x, y, z)
  have hd : complexDenominator r.1 r.2.1 z t = complexDenominator x y z t := by
    rw [complexDenominator, complexDenominator, radialAux_axialRotation]
  apply Prod.ext
  · change rationalAlpha r.1 r.2.1 z t = rationalAlpha x y z t
    have hr : radialAux r.1 r.2.1 z t = radialAux x y z t := radialAux_axialRotation θ x y z t
    unfold rationalAlpha
    rw [hr]
  · change rationalBeta r.1 r.2.1 z t = _
    rw [rationalBeta_eq_reduced, rationalBeta_eq_reduced, hd, betaReduced_axialRotation θ x y z]
    ring

/-- Cartesian rotation commutes with common scalar multiplication. -/
private theorem axialRotateVector_mul {K : Type*} [CommRing K] (c s m : K) (v : Fin 3 → K) (j : Fin 3) :
    axialRotateVector c s (fun i => m * v i) j = m * axialRotateVector c s v j := by
  fin_cases j <;> simp [axialRotateVector] <;> ring

/-- The two spinor factors give the spatial rotation of the base vector
and one extra phase. -/
private theorem spinorField_axialRotation (θ : ℝ) (g h : ℂ) (j : Fin 3) :
    spinorField g (batemanAxialPhase θ * h) j =
      batemanAxialPhase θ * axialRotateVector (Real.cos θ : ℂ) (Real.sin θ : ℂ) (spinorField g h) j := by
  let c : ℂ := Real.cos θ
  let s : ℂ := Real.sin θ
  have hunit : s ^ 2 + c ^ 2 = 1 := by
    change (Real.sin θ : ℂ) ^ 2 + (Real.cos θ : ℂ) ^ 2 = 1
    exact_mod_cast Real.sin_sq_add_cos_sq θ
  have hi := Complex.I_sq
  have hphas : (c - Complex.I * s) * (c + Complex.I * s) = 1 := by
    linear_combination hunit - s ^ 2 * hi
  rw [batemanAxialPhase_eq]
  have h₀ : -(g ^ 2 + ((c - Complex.I * s) * h) ^ 2) =
      (c - Complex.I * s) * (c * (-(g ^ 2 + h ^ 2)) - s * (Complex.I * (g ^ 2 - h ^ 2))) := by
    linear_combination g ^ 2 * hphas
  have h₁ : Complex.I * (g ^ 2 - ((c - Complex.I * s) * h) ^ 2) =
      (c - Complex.I * s) * (s * (-(g ^ 2 + h ^ 2)) + c * (Complex.I * (g ^ 2 - h ^ 2))) := by
    linear_combination (-Complex.I * g ^ 2) * hphas +
      (c - Complex.I * s) * s * (g ^ 2 + h ^ 2) * hi
  fin_cases j
  · exact h₀
  · exact h₁
  · change -2 * Complex.I * g * ((c - Complex.I * s) * h) =
      (c - Complex.I * s) * (-2 * Complex.I * g * h)
    ring

/-- The physical powered field transforms as a Cartesian vector times
the full axial phase of the second powered potential. -/
theorem rationalPowerField_axialRotation (p : ℕ) {q : ℕ} (hq : 0 < q) (θ x y z t : ℝ) (j : Fin 3) :
    let r := batemanAxialRotation θ (x, y, z)
    rationalPowerField p q r.1 r.2.1 r.2.2 t j =
      batemanAxialPhase θ ^ q *
        axialRotateVector (Real.cos θ : ℂ) (Real.sin θ : ℂ) (rationalPowerField p q x y z t) j := by
  let r := batemanAxialRotation θ (x, y, z)
  let e := batemanAxialPhase θ
  let g := alphaCommonFactor z t
  let h := betaReducedNumerator x y
  let k : ℂ := 4 / complexDenominator x y z t ^ 3
  have ha : rationalAlpha r.1 r.2.1 z t = rationalAlpha x y z t :=
    congrArg Prod.fst (batemanPair_axialRotation θ x y z t)
  have hb : rationalBeta r.1 r.2.1 z t = e * rationalBeta x y z t :=
    congrArg Prod.snd (batemanPair_axialRotation θ x y z t)
  have hw : complexDenominator r.1 r.2.1 z t = complexDenominator x y z t := by
    rw [complexDenominator, complexDenominator, radialAux_axialRotation]
  have hf : rationalPowerFactor p q r.1 r.2.1 z t =
      e ^ (q - 1) * rationalPowerFactor p q x y z t := by
    rw [rationalPowerFactor, ha, hb, mul_pow, rationalPowerFactor]
    ring
  have hc (i : Fin 3) : rationalField r.1 r.2.1 z t i =
      k * (e * axialRotateVector (Real.cos θ : ℂ) (Real.sin θ : ℂ) (spinorField g h) i) := by
    rw [rationalField_eq_spinorField, hw, betaReduced_axialRotation θ x y z]
    rw [spinorField_axialRotation]
  change rationalPowerField p q r.1 r.2.1 z t j = _
  simp only [rationalPowerField_eq, hf, hc, rationalField_eq_spinorField, axialRotateVector_mul]
  have he : e ^ q = e ^ (q - 1) * e := by
    conv_lhs => rw [← Nat.sub_add_cancel (Nat.succ_le_of_lt hq), pow_succ]
  change _ = e ^ q * (rationalPowerFactor p q x y z t * (k *
    axialRotateVector (Real.cos θ : ℂ) (Real.sin θ : ℂ) (spinorField g h) j))
  rw [he]
  ring

/-- The `q`-th power of the phase at `π / (2q)` is the negative imaginary unit. -/
theorem batemanAxialPhase_special {q : ℕ} (hq : 0 < q) :
    batemanAxialPhase (π / (2 * (q : ℝ))) ^ q = -Complex.I := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [batemanAxialPhase, ← Complex.exp_nat_mul]
  have he : (q : ℂ) * (-((π / (2 * (q : ℝ)) : ℝ) : ℂ) * Complex.I) = -(π : ℂ) / 2 * Complex.I := by
    push_cast
    field_simp [hqC]
  rw [he, Complex.exp_neg_pi_div_two_mul_I]

/-- The field-line product label transforms by the same full phase. -/
theorem poweredProductLabel_axialRotation (p q : ℕ) (θ x y z t : ℝ) :
    let r := batemanAxialRotation θ (x, y, z)
    poweredProductLabel p q r.1 r.2.1 r.2.2 t =
      batemanAxialPhase θ ^ q * poweredProductLabel p q x y z t := by
  let r := batemanAxialRotation θ (x, y, z)
  have ha : rationalAlpha r.1 r.2.1 z t = rationalAlpha x y z t :=
    congrArg Prod.fst (batemanPair_axialRotation θ x y z t)
  have hb : rationalBeta r.1 r.2.1 z t = batemanAxialPhase θ * rationalBeta x y z t :=
    congrArg Prod.snd (batemanPair_axialRotation θ x y z t)
  change rationalAlpha r.1 r.2.1 z t ^ p * rationalBeta r.1 r.2.1 z t ^ q = _
  rw [ha, hb, mul_pow, poweredProductLabel]
  ring

/-- The positive special angle swaps electric and magnetic vectors,
with the negative sign on the transformed magnetic component. -/
theorem rationalPowerField_axialDuality (p : ℕ) {q : ℕ} (hq : 0 < q) (x y z t : ℝ) :
    let θ := π / (2 * (q : ℝ))
    let r := batemanAxialRotation θ (x, y, z)
    let F := rationalPowerField p q x y z t
    let Frot := rationalPowerField p q r.1 r.2.1 r.2.2 t
    (fun j => (Frot j).re) = axialRotateVector (Real.cos θ) (Real.sin θ) (fun j => (F j).im) ∧
    (fun j => (Frot j).im) = -(axialRotateVector (Real.cos θ) (Real.sin θ) (fun j => (F j).re)) := by
  dsimp only
  let θ := π / (2 * (q : ℝ))
  let r := batemanAxialRotation θ (x, y, z)
  let F := rationalPowerField p q x y z t
  have hphase := batemanAxialPhase_special hq
  have hfield (j : Fin 3) : rationalPowerField p q r.1 r.2.1 r.2.2 t j =
      -Complex.I * axialRotateVector (Real.cos θ : ℂ) (Real.sin θ : ℂ) F j := by
    have h := rationalPowerField_axialRotation p hq θ x y z t j
    change rationalPowerField p q r.1 r.2.1 r.2.2 t j = batemanAxialPhase θ ^ q *
      axialRotateVector (Real.cos θ : ℂ) (Real.sin θ : ℂ) F j at h
    rwa [hphase] at h
  constructor <;> funext j <;> rw [hfield] <;> fin_cases j <;>
    simp [axialRotateVector, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, θ, F, -Complex.ofReal_cos, -Complex.ofReal_sin]

end Qatlib.Papers.KnotLight13.TorusFamily
