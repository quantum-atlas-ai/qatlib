/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.PowerLineLevels
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanPotential
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanPoyntingRays

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith

/-!
# First integrals of Bateman electric and magnetic field lines

[Kedia2013TyingKnots], Fig. 2 and the accompanying text. On each
physical time slice the magnetic and electric curves conserve the real
and imaginary parts of the powered product label, respectively.
The statement applies on any closed parameter interval and allows
arbitrary speed along the given field direction.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Set
open Qatlib.Papers.KnotLight13.TorusFamily (rationalAlpha rationalBeta)
open Qatlib.Papers.KnottedLight08.HopfField (dot3 squaredLength riemannSilberstein null_iff)
open scoped BigOperators

local notation "Space" => ℝ × ℝ × ℝ

/-- The product of the powered potentials viewed as a function on a fixed slice. -/
noncomputable def batemanPoweredLabel (p q : ℕ) (t : ℝ) (x : Space) : ℂ :=
  batemanAlphaPower p t x * batemanBetaPower q t x

/-- The product label is smooth on the whole spatial slice. -/
theorem contDiff_batemanPoweredLabel (p q : ℕ) (t : ℝ) :
    ContDiff ℝ ⊤ (batemanPoweredLabel p q t) :=
  (contDiff_batemanAlphaPower p t).mul (contDiff_batemanBetaPower q t)

/-- The covector of the label in each Cartesian direction is its actual
coordinate gradient. -/
theorem fderiv_batemanPoweredLabel_axis (p q : ℕ) (t : ℝ) (x : Space) (j : Fin 3) :
    fderiv ℝ (batemanPoweredLabel p q t) x (batemanAxis j) =
      poweredProductGradient p q x.1 x.2.1 x.2.2 t j := by
  rcases x with ⟨u, v, w⟩
  have ha := ((contDiff_batemanAlphaPower p t).differentiable (by simp) (u, v, w)).hasFDerivAt
  have hb := ((contDiff_batemanBetaPower q t).differentiable (by simp) (u, v, w)).hasFDerivAt
  change fderiv ℝ (batemanAlphaPower p t * batemanBetaPower q t) (u, v, w) (batemanAxis j) = _
  rw [(ha.mul hb).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul,
    fderiv_batemanAlphaPower_axis, fderiv_batemanBetaPower_axis]
  change _ = rationalBeta u v w t ^ q * alphaPowerGradient p u v w t j +
    rationalAlpha u v w t ^ p * betaPowerGradient q u v w t j
  exact add_comm _ _

/-- In Cartesian components the label differential contracts with the
displacement by the three Euclidean coordinates. -/
theorem fderiv_batemanPoweredLabel_apply (p q : ℕ) (t : ℝ) (x u : Space) :
    fderiv ℝ (batemanPoweredLabel p q t) x u =
      ∑ j : Fin 3, (batemanCartesianCoordinates u j : ℂ) *
        poweredProductGradient p q x.1 x.2.1 x.2.2 t j := by
  conv_lhs => rw [← batemanCartesianBasis.sum_repr u]
  simp only [map_sum, map_smul, batemanCartesianBasis_apply, fderiv_batemanPoweredLabel_axis,
    batemanCartesianBasis_repr, Complex.real_smul]
  rfl

/-- The derivative of a projected label is zero when the curve's tangent
is a real multiple of a field vector annihilated by that projection. -/
private theorem hasDerivWithinAt_projectedLabel_zero
    (p q : ℕ) (t : ℝ) {curve : ℝ → Space} {s : ℝ} {U : Set ℝ}
    (project : ℂ →L[ℝ] ℝ) (speed : ℝ) (field : Fin 3 → ℝ)
    (hcurve : HasDerivWithinAt curve (speed • batemanCartesianCoordinates.symm field) U s)
    (hann : project (∑ j : Fin 3, (field j : ℂ) *
      poweredProductGradient p q (curve s).1 (curve s).2.1 (curve s).2.2 t j) = 0) :
    HasDerivWithinAt (fun r => project (batemanPoweredLabel p q t (curve r))) 0 U s := by
  have hlabel := ((contDiff_batemanPoweredLabel p q t).differentiable (by simp) (curve s)).hasFDerivAt
  have h := (project.hasFDerivAt.comp (curve s) hlabel).comp_hasDerivWithinAt s hcurve
  change HasDerivWithinAt (fun r => project (batemanPoweredLabel p q t (curve r)))
    (project (fderiv ℝ (batemanPoweredLabel p q t) (curve s)
      (speed • batemanCartesianCoordinates.symm field))) U s at h
  rw [map_smul, map_smul, fderiv_batemanPoweredLabel_apply, LinearEquiv.apply_symm_apply,
    hann, smul_zero] at h
  exact h

/-- A real function with zero derivative on an interval takes the same
value at all its points. -/
private theorem eqOn_of_hasDerivWithinAt_zero {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (h : ∀ s ∈ Icc a b, HasDerivWithinAt f 0 (Icc a b) s) :
    EqOn f (fun _ => f a) (Icc a b) := by
  apply eq_of_derivWithin_eq (fun s hs => (h s hs).differentiableWithinAt)
    (differentiableOn_const _) _ rfl
  intro s hs
  have hu := uniqueDiffOn_Icc hab s (mem_Icc_of_Ico hs)
  rw [(h s (mem_Icc_of_Ico hs)).derivWithin hu,
    (hasDerivWithinAt_const s (Icc a b) (f a)).derivWithin hu]

/-- The magnetic field-line equation conserves the real product label along
every actual parametrized line segment, including reparametrized segments. -/
theorem magnetic_line_preserves_label (p q : ℕ) (t : ℝ) {a b : ℝ} (hab : a < b)
    {curve : ℝ → Space} (speed : ℝ → ℝ)
    (hcurve : ∀ s ∈ Icc a b, HasDerivWithinAt curve
      (speed s • batemanCartesianCoordinates.symm (fun j =>
        (rationalPowerField p q (curve s).1 (curve s).2.1 (curve s).2.2 t j).im))
      (Icc a b) s) :
    EqOn (fun s => (batemanPoweredLabel p q t (curve s)).re)
      (fun _ => (batemanPoweredLabel p q t (curve a)).re) (Icc a b) := by
  apply eqOn_of_hasDerivWithinAt_zero hab
  intro s hs
  refine hasDerivWithinAt_projectedLabel_zero p q t Complex.reCLM (speed s) _ (hcurve s hs) ?_
  have h := (powered_field_line_levels p q (curve s).1 (curve s).2.1 (curve s).2.2 t).1
  simpa only [Complex.reCLM_apply, Fin.sum_univ_three, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, dot3] using h

/-- The electric field-line equation conserves the imaginary product label
along every actual parametrized line segment. -/
theorem electric_line_preserves_label (p q : ℕ) (t : ℝ) {a b : ℝ} (hab : a < b)
    {curve : ℝ → Space} (speed : ℝ → ℝ)
    (hcurve : ∀ s ∈ Icc a b, HasDerivWithinAt curve
      (speed s • batemanCartesianCoordinates.symm (fun j =>
        (rationalPowerField p q (curve s).1 (curve s).2.1 (curve s).2.2 t j).re))
      (Icc a b) s) :
    EqOn (fun s => (batemanPoweredLabel p q t (curve s)).im)
      (fun _ => (batemanPoweredLabel p q t (curve a)).im) (Icc a b) := by
  apply eqOn_of_hasDerivWithinAt_zero hab
  intro s hs
  refine hasDerivWithinAt_projectedLabel_zero p q t Complex.imCLM (speed s) _ (hcurve s hs) ?_
  have h := (powered_field_line_levels p q (curve s).1 (curve s).2.1 (curve s).2.2 t).2
  simpa only [Complex.imCLM_apply, Fin.sum_univ_three, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, dot3] using h

/-- A zero Euclidean squared length forces every Cartesian component to vanish. -/
private theorem eq_zero_of_squaredLength_zero {x : Fin 3 → ℝ} (h : squaredLength x = 0) :
    x = 0 := by
  unfold squaredLength dot3 at h
  funext j
  fin_cases j
  · change x 0 = 0
    nlinarith [sq_nonneg (x 1), sq_nonneg (x 2)]
  · change x 1 = 0
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 2)]
  · change x 2 = 0
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

/-- A nonzero power reparametrization factor makes each actual real field nonzero,
since the base field is nowhere zero and the powered field is null. -/
theorem powered_fields_nonzero_of_factor_ne_zero (p q : ℕ) (x y z t : ℝ)
    (hfactor : rationalPowerFactor p q x y z t ≠ 0) :
    (fun j => (rationalPowerField p q x y z t j).re) ≠ 0 ∧
      (fun j => (rationalPowerField p q x y z t j).im) ≠ 0 := by
  let F := rationalPowerField p q x y z t
  let E := fun j => (F j).re
  let B := fun j => (F j).im
  have hRS : riemannSilberstein E B = F := by
    funext j
    apply Complex.ext <;> simp [riemannSilberstein, E, B, Complex.mul_re, Complex.mul_im]
  have hlen : squaredLength E = squaredLength B :=
    ((null_iff E B).1 (hRS.symm ▸ rational_power_field_null p q x y z t)).2
  have hnonzero : F ≠ 0 := by
    intro hz
    have hbase : rationalField x y z t = 0 := by
      funext j
      have he := congrFun hz j
      change rationalPowerField p q x y z t j = 0 at he
      rw [rationalPowerField_eq] at he
      exact (mul_eq_zero.mp he).resolve_left hfactor
    have hh := rational_electric_length_pos x y z t
    change 0 < squaredLength (fun j => (rationalField x y z t j).re) at hh
    simp only [hbase, Pi.zero_apply, Complex.zero_re] at hh
    norm_num [squaredLength, dot3] at hh
  have hsum : E = 0 → B = 0 → False := by
    intro he hb
    apply hnonzero
    rw [← hRS, he, hb]
    funext j
    simp [riemannSilberstein]
  change E ≠ 0 ∧ B ≠ 0
  constructor
  · intro he
    apply hsum he
    apply eq_zero_of_squaredLength_zero
    rw [← hlen, he]
    simp [squaredLength, dot3]
  · intro hb
    apply hsum _ hb
    apply eq_zero_of_squaredLength_zero
    rw [hlen, hb]
    simp [squaredLength, dot3]

/-- For positive powers, at every nonzero complex label both actual real
fields are nonzero. This applies to all nonzero projected levels. -/
theorem powered_fields_nonzero_of_label_ne_zero {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (x y z t : ℝ) (h : poweredProductLabel p q x y z t ≠ 0) :
    (fun j => (rationalPowerField p q x y z t j).re) ≠ 0 ∧
      (fun j => (rationalPowerField p q x y z t j).im) ≠ 0 := by
  have ha : rationalAlpha x y z t ≠ 0 := by
    intro ha
    exact h (by simp [poweredProductLabel, ha, zero_pow hp.ne'])
  have hb : rationalBeta x y z t ≠ 0 := by
    intro hb
    exact h (by simp [poweredProductLabel, hb, zero_pow hq.ne'])
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hfactor : rationalPowerFactor p q x y z t ≠ 0 :=
    mul_ne_zero (mul_ne_zero hp' (pow_ne_zero _ ha)) (mul_ne_zero hq' (pow_ne_zero _ hb))
  exact powered_fields_nonzero_of_factor_ne_zero p q x y z t hfactor

end Qatlib.Papers.KnotLight13.TorusFamily
