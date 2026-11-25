/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.NullLinking.MagneticLinkingValue

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The Gauss linking value of distinct compact magnetic fibers

[IrvineBouwmeester2008KnottedLight], Eq. (2) and Fig. 1,
[DOI](https://doi.org/10.1038/nphys1056).
In the inverse radial coordinate the affine magnetic circles extend
smoothly to the oriented pole. Rotating the nonzero affine label
preserves the Gauss integral with the pole. For two distinct compact
affine fibers, the larger label can then move out towards the pole
without crossing the other label.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.KnottedLight08.NullLinking

open Qatlib.Papers.KnotLight13.TorusFamily (batemanRay_zero)
open Qatlib.Papers.SuperfluidHel18.CenterlineCL
  (gaussLinking gaussLinking_symm gaussLinking_eq_of_smooth_homotopy gaussLinking_eq_on_interval)
open Set

/-- The compact affine circle written in inverse radial chart
coordinates, with zero inverse radius giving the pole. -/
private def inverseRadiusCircle (a b r θ : ℝ) : Fin 3 → ℝ :=
  let p := Real.sqrt (1 + r ^ 2) * Real.cos θ - r
  ![-r * Real.sin θ, a * p + b * Real.sin θ, b * p - a * Real.sin θ]

/-- The squared size of the finite label for unit angular coordinates. -/
private theorem circleLabel_sq (a b r : ℝ)
    (hab : a ^ 2 + b ^ 2 = 1) :
    (a / r) ^ 2 + (b / r) ^ 2 = (1 / r) ^ 2 := by
  rw [div_pow, div_pow, ← add_div, hab, div_pow]
  norm_num

/-- In the positive inverse radius chart the formulas parameterize the
actual initial circle with the same angle and orientation. -/
private theorem inverseRadiusCircle_eq (a b r θ : ℝ)
    (hab : a ^ 2 + b ^ 2 = 1) (hr : 0 < r) :
    inverseRadiusCircle a b r θ =
      cartesianCoordinates (magneticCircleAt (a / r) (b / r) 0 θ) := by
  let u := a / r
  let v := b / r
  let d := u ^ 2 + v ^ 2
  let S := Real.sqrt (1 + r ^ 2)
  have hD : d = (1 / r) ^ 2 := circleLabel_sq a b r hab
  have hR : Real.sqrt d = 1 / r := by
    rw [hD, Real.sqrt_sq (by positivity)]
  have hS : Real.sqrt (d + 1) = S / r := by
    rw [hD, show (1 / r) ^ 2 + 1 = (1 + r ^ 2) / r ^ 2 by field_simp [hr.ne']]
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq hr.le]
  rw [magneticCircleAt, neg_zero, batemanRay_zero]
  funext j
  fin_cases j
  · change -r * Real.sin θ = 0 + -(Real.sqrt d * Real.sin θ) / d
    rw [hR, hD]
    field_simp
    ring
  · change a * (S * Real.cos θ - r) + b * Real.sin θ =
      -u / d + (u * (Real.sqrt (d + 1) * Real.cos θ) + v * (Real.sqrt d * Real.sin θ)) / d
    rw [hR, hS, hD]
    dsimp only [u, v]
    field_simp
    ring
  · change b * (S * Real.cos θ - r) - a * Real.sin θ =
      -v / d + (v * (Real.sqrt (d + 1) * Real.cos θ) - u * (Real.sqrt d * Real.sin θ)) / d
    rw [hR, hS, hD]
    dsimp only [u, v]
    field_simp
    ring

/-- At zero inverse radius the parameter is an orientation-preserving
shift of the actual pole angle. -/
private theorem inverseRadiusCircle_zero (φ θ : ℝ) :
    inverseRadiusCircle (Real.cos φ) (Real.sin φ) 0 θ =
      cartesianCoordinates (magneticPoleCircleAt 0 (θ - φ)) := by
  rw [magneticPoleCircleAt_zero_coords]
  simp only [inverseRadiusCircle, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero,
    Real.sqrt_one, one_mul, sub_zero, neg_zero, zero_mul, Real.sin_sub, Real.cos_sub]
  funext j
  fin_cases j
  · rfl
  · change Real.cos φ * Real.cos θ + Real.sin φ * Real.sin θ =
      Real.cos θ * Real.cos φ + Real.sin θ * Real.sin φ
    ring
  · change Real.sin φ * Real.cos θ - Real.cos φ * Real.sin θ =
      -(Real.sin θ * Real.cos φ - Real.cos θ * Real.sin φ)
    ring

/-- The inverse radial parametrization is smooth jointly after any
smooth choices of its three chart coordinates and angle. -/
private theorem contDiff_inverseRadiusCircle {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b r θ : E → ℝ}
    (ha : ContDiff ℝ 2 a) (hb : ContDiff ℝ 2 b)
    (hr : ContDiff ℝ 2 r) (hθ : ContDiff ℝ 2 θ) :
    ContDiff ℝ 2 (fun s => inverseRadiusCircle (a s) (b s) (r s) (θ s)) := by
  have hs : ContDiff ℝ 2 (fun s => Real.sqrt (1 + r s ^ 2)) :=
    (contDiff_const.add (hr.pow 2)).sqrt (fun _ => by positivity)
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · change ContDiff ℝ 2 (fun s => -r s * Real.sin (θ s))
    fun_prop
  · change ContDiff ℝ 2 (fun s =>
      a s * (Real.sqrt (1 + r s ^ 2) * Real.cos (θ s) - r s) + b s * Real.sin (θ s))
    fun_prop
  · change ContDiff ℝ 2 (fun s =>
      b s * (Real.sqrt (1 + r s ^ 2) * Real.cos (θ s) - r s) - a s * Real.sin (θ s))
    fun_prop

/-- Each inverse radial curve has the same full angular period. -/
private theorem inverseRadiusCircle_periodic (a b r : ℝ) :
    Function.Periodic (inverseRadiusCircle a b r) (2 * Real.pi) := by
  intro θ
  simp only [inverseRadiusCircle, Real.sin_add_two_pi, Real.cos_add_two_pi]

/-- The coordinate representation of any initial finite circle is smooth. -/
private theorem contDiff_initialCircle_coords (u v : ℝ) :
    ContDiff ℝ 2 (cartesianCoordinates ∘ magneticCircleAt u v 0) := by
  have he : cartesianCoordinates ∘ magneticCircleAt u v 0 =
      (fun s j => initialMagneticCircle u v s j) := by
    funext s j
    change cartesianCoordinates (magneticCircleAt u v 0 s) j = _
    rw [magneticCircleAt, neg_zero, batemanRay_zero]
    fin_cases j <;> rfl
  rw [he]
  apply contDiff_pi.mpr
  intro j
  let d := u ^ 2 + v ^ 2
  let ρ := Real.sqrt d
  let σ := Real.sqrt (d + 1)
  fin_cases j
  · change ContDiff ℝ 2 (fun θ => 0 + -(ρ * Real.sin θ) / d)
    fun_prop
  · change ContDiff ℝ 2 (fun θ => -u / d + (u * (σ * Real.cos θ) + v * (ρ * Real.sin θ)) / d)
    fun_prop
  · change ContDiff ℝ 2 (fun θ => -v / d + (v * (σ * Real.cos θ) - u * (ρ * Real.sin θ)) / d)
    fun_prop

/-- The pole coordinates are smooth in the angle. -/
private theorem contDiff_initialPole_coords :
    ContDiff ℝ 2 (cartesianCoordinates ∘ magneticPoleCircleAt 0) := by
  have hC : ContDiff ℝ 2 cartesianCoordinates :=
    cartesianCoordinates.toContinuousLinearEquiv.contDiff
  have hΓ : ContDiff ℝ 2 (fun p : ℝ × ℝ => magneticPoleCircleAt p.1 p.2) :=
    contDiff_magnetic_pole_circle_at_joint.of_le le_top
  have hPair : ContDiff ℝ 2 (fun s : ℝ => ((0 : ℝ), s)) :=
    contDiff_const.prodMk contDiff_id
  exact hC.comp (hΓ.comp hPair)

/-- A rigid shift of the traversal angle of the pole preserves the
Gauss integral with an actual finite nonzero initial circle. -/
private theorem gaussLinking_initialPole_shift (u v φ : ℝ) (huv : 0 < u ^ 2 + v ^ 2) :
    gaussLinking (cartesianCoordinates ∘ magneticCircleAt u v 0)
      (fun θ => cartesianCoordinates (magneticPoleCircleAt 0 (θ - φ))) =
    gaussLinking (cartesianCoordinates ∘ magneticCircleAt u v 0)
      (cartesianCoordinates ∘ magneticPoleCircleAt 0) := by
  let C := cartesianCoordinates ∘ magneticCircleAt u v 0
  let P := cartesianCoordinates ∘ magneticPoleCircleAt 0
  have hshift : ContDiff ℝ 2 (fun p : ℝ × ℝ => p.2 - p.1) := by fun_prop
  have hP : Function.Periodic P (2 * Real.pi) :=
    fun θ => congrArg cartesianCoordinates (magnetic_pole_circle_at_periodic 0 θ)
  have h := gaussLinking_eq_of_smooth_homotopy (fun p => C p.2) (fun p => P (p.2 - p.1))
    ((contDiff_initialCircle_coords u v).comp contDiff_snd)
    (contDiff_initialPole_coords.comp hshift)
    (fun t s θ h => (Set.disjoint_left.mp (magnetic_circle_disjoint_pole u v 0 huv))
      (Set.mem_range_self s)
      (cartesianCoordinates.injective h ▸ Set.mem_range_self (θ - t)))
    (fun _ s => congrArg cartesianCoordinates (magnetic_circle_at_periodic u v 0 s))
    (fun t θ => by
      change P (θ + 2 * Real.pi - t) = P (θ - t)
      rw [show θ + 2 * Real.pi - t = (θ - t) + 2 * Real.pi by ring, hP]) φ 0
  change gaussLinking C (fun θ => P (θ - φ)) = gaussLinking C (fun θ => P (θ - 0)) at h
  change gaussLinking C (fun θ => P (θ - φ)) = gaussLinking C P
  simpa only [sub_zero] using h

/-- Every finite nonzero magnetic circle has Gauss linking value one
with the oriented pole, on each physical time slice. -/
theorem gaussLinking_magnetic_circle_pole_eq_one (u v t : ℝ) (huv : 0 < u ^ 2 + v ^ 2) :
    gaussLinking (cartesianCoordinates ∘ magneticCircleAt u v t)
      (cartesianCoordinates ∘ magneticPoleCircleAt t) = 1 := by
  rw [gaussLinking_magnetic_circle_pole_eq u v t 0 huv]
  let R := Real.sqrt (u ^ 2 + v ^ 2)
  let r := 1 / R
  have hR : 0 < R := Real.sqrt_pos.2 huv
  have hr : 0 < r := by dsimp only [r]; positivity
  have hRN : R ^ 2 = u ^ 2 + v ^ 2 := Real.sq_sqrt huv.le
  have hab : (u / R) ^ 2 + (v / R) ^ 2 = 1 := by
    rw [div_pow, div_pow, ← add_div, ← hRN, div_self (pow_ne_zero 2 hR.ne')]
  obtain ⟨φ, hcos, hsin⟩ := exists_angle_of_unit_coordinates (u / R) (v / R) hab
  let Γ (p : ℝ × ℝ) := inverseRadiusCircle (Real.cos p.1) (Real.sin p.1) r p.2
  let P := cartesianCoordinates ∘ magneticPoleCircleAt 0
  have hΓ : ContDiff ℝ 2 Γ :=
    contDiff_inverseRadiusCircle (Real.contDiff_cos.comp contDiff_fst)
      (Real.contDiff_sin.comp contDiff_fst) contDiff_const contDiff_snd
  have hdisj (α s θ : ℝ) : Γ (α, s) ≠ P θ := by
    have hunit : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := by rw [add_comm, Real.sin_sq_add_cos_sq]
    have hd : 0 < (Real.cos α / r) ^ 2 + (Real.sin α / r) ^ 2 := by
      rw [circleLabel_sq _ _ r hunit]
      positivity
    intro h
    rw [show Γ (α, s) = _ from inverseRadiusCircle_eq _ _ r s hunit hr] at h
    exact (Set.disjoint_left.mp (magnetic_circle_disjoint_pole _ _ 0 hd))
      (Set.mem_range_self s) (cartesianCoordinates.injective h ▸ Set.mem_range_self θ)
  have hom := gaussLinking_eq_of_smooth_homotopy Γ (fun p => P p.2) hΓ
    (contDiff_initialPole_coords.comp contDiff_snd) hdisj
    (fun α => inverseRadiusCircle_periodic (Real.cos α) (Real.sin α) r)
    (fun _ θ => congrArg cartesianCoordinates (magnetic_pole_circle_at_periodic 0 θ)) φ 0
  have hφ : (fun θ => Γ (φ, θ)) = cartesianCoordinates ∘ magneticCircleAt u v 0 := by
    funext θ
    change inverseRadiusCircle (Real.cos φ) (Real.sin φ) r θ = _
    rw [hcos, hsin, inverseRadiusCircle_eq _ _ r θ hab hr]
    have hu' : (u / R) / r = u := by dsimp only [r]; field_simp
    have hv' : (v / R) / r = v := by dsimp only [r]; field_simp
    rw [hu', hv']
    rfl
  have h0 : (fun θ => Γ (0, θ)) = cartesianCoordinates ∘ magneticCircleAt R 0 0 := by
    funext θ
    change inverseRadiusCircle (Real.cos 0) (Real.sin 0) r θ = _
    rw [Real.cos_zero, Real.sin_zero, inverseRadiusCircle_eq _ _ r θ (by norm_num) hr,
      zero_div, show 1 / r = R by simp [r]]
    rfl
  rw [hφ, h0] at hom
  exact hom.trans (gaussLinking_real_magnetic_circle_pole_eq_one R 0 hR)

/-- With the larger affine label in the second slot, its circle can be
moved toward the pole by decreasing its inverse radius. -/
private theorem gaussLinking_initial_magnetic_circles_eq_one_of_le (u v p q : ℝ)
    (huv : 0 < u ^ 2 + v ^ 2) (hpq : 0 < p ^ 2 + q ^ 2)
    (hsize : u ^ 2 + v ^ 2 ≤ p ^ 2 + q ^ 2)
    (hne : ((u : ℂ) + Complex.I * (v : ℂ)) ≠ ((p : ℂ) + Complex.I * (q : ℂ))) :
    gaussLinking (cartesianCoordinates ∘ magneticCircleAt u v 0)
      (cartesianCoordinates ∘ magneticCircleAt p q 0) = 1 := by
  let R := Real.sqrt (p ^ 2 + q ^ 2)
  let r := 1 / R
  have hR : 0 < R := Real.sqrt_pos.2 hpq
  have hr : 0 < r := by dsimp only [r]; positivity
  have hRN : R ^ 2 = p ^ 2 + q ^ 2 := Real.sq_sqrt hpq.le
  have hab : (p / R) ^ 2 + (q / R) ^ 2 = 1 := by
    rw [div_pow, div_pow, ← add_div, ← hRN, div_self (pow_ne_zero 2 hR.ne')]
  obtain ⟨φ, hcos, hsin⟩ := exists_angle_of_unit_coordinates (p / R) (q / R) hab
  have hunit : Real.cos φ ^ 2 + Real.sin φ ^ 2 = 1 := by rw [hcos, hsin, hab]
  have hpr : (Real.cos φ / r) = p := by rw [hcos]; dsimp only [r]; field_simp
  have hqr : (Real.sin φ / r) = q := by rw [hsin]; dsimp only [r]; field_simp
  let C := cartesianCoordinates ∘ magneticCircleAt u v 0
  let Γ (x : ℝ × ℝ) := inverseRadiusCircle (Real.cos φ) (Real.sin φ) x.1 x.2
  have hΓ : ContDiff ℝ 2 Γ :=
    contDiff_inverseRadiusCircle contDiff_const contDiff_const contDiff_fst contDiff_snd
  have hdisj (z : ℝ) (hz : z ∈ Icc 0 r) (s θ : ℝ) : C s ≠ Γ (z, θ) := by
    rcases hz.1.eq_or_lt with hzero | hz0
    · intro h
      rw [← hzero, show Γ (0, θ) = _ from inverseRadiusCircle_zero φ θ] at h
      exact (Set.disjoint_left.mp (magnetic_circle_disjoint_pole u v 0 huv))
        (Set.mem_range_self s)
        (cartesianCoordinates.injective h ▸ Set.mem_range_self (θ - φ))
    · have hnorm := circleLabel_sq (Real.cos φ) (Real.sin φ) z hunit
      have hzpos : 0 < (Real.cos φ / z) ^ 2 + (Real.sin φ / z) ^ 2 := by
        rw [hnorm]
        positivity
      have hlabel : ((u : ℂ) + Complex.I * (v : ℂ)) ≠
          ((Real.cos φ / z : ℝ) : ℂ) + Complex.I * ((Real.sin φ / z : ℝ) : ℂ) := by
        intro he
        by_cases heq : z = r
        · rw [heq, hpr, hqr] at he
          exact hne he
        · have hzr : z < r := lt_of_le_of_ne hz.2 heq
          have hInv : R < 1 / z := by
            simpa [r] using one_div_lt_one_div_of_lt hz0 hzr
          have hsq : R ^ 2 < (1 / z) ^ 2 :=
            pow_lt_pow_left₀ hInv hR.le (by norm_num)
          have hlt : u ^ 2 + v ^ 2 < (Real.cos φ / z) ^ 2 + (Real.sin φ / z) ^ 2 := by
            rw [hnorm]
            exact hsize.trans_lt (hRN ▸ hsq)
          have hu : u = Real.cos φ / z := by
            simpa only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
              using congrArg Complex.re he
          have hv : v = Real.sin φ / z := by
            simpa only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, one_mul, zero_add]
              using congrArg Complex.im he
          exact hlt.ne (by rw [hu, hv])
      intro h
      rw [show Γ (z, θ) = _ from inverseRadiusCircle_eq _ _ z θ hunit hz0] at h
      exact (Set.disjoint_left.mp (magnetic_circles_disjoint _ _ _ _ 0 huv hzpos hlabel))
        (Set.mem_range_self s) (cartesianCoordinates.injective h ▸ Set.mem_range_self θ)
  have h := gaussLinking_eq_on_interval (fun x => C x.2) Γ hr.le
    ((contDiff_initialCircle_coords u v).comp contDiff_snd).contDiffOn hΓ.contDiffOn hdisj
    (fun _ _ s => congrArg cartesianCoordinates (magnetic_circle_at_periodic u v 0 s))
    (fun z _ => inverseRadiusCircle_periodic (Real.cos φ) (Real.sin φ) z)
  have h0 : (fun θ => Γ (0, θ)) = fun θ =>
      cartesianCoordinates (magneticPoleCircleAt 0 (θ - φ)) :=
    funext (inverseRadiusCircle_zero φ)
  have hr' : (fun θ => Γ (r, θ)) = cartesianCoordinates ∘ magneticCircleAt p q 0 := by
    funext θ
    change inverseRadiusCircle (Real.cos φ) (Real.sin φ) r θ = _
    rw [inverseRadiusCircle_eq _ _ r θ hunit hr, hpr, hqr]
    rfl
  rw [h0, hr'] at h
  exact h.symm.trans ((gaussLinking_initialPole_shift u v φ huv).trans
    (gaussLinking_magnetic_circle_pole_eq_one u v 0 huv))

/-- The Gauss linking integral of any two distinct finite nonzero
oriented magnetic circles equals one on every physical time slice. -/
theorem gaussLinking_magnetic_circles_eq_one (u v p q t : ℝ)
    (huv : 0 < u ^ 2 + v ^ 2) (hpq : 0 < p ^ 2 + q ^ 2)
    (hne : ((u : ℂ) + Complex.I * (v : ℂ)) ≠ ((p : ℂ) + Complex.I * (q : ℂ))) :
    gaussLinking (cartesianCoordinates ∘ magneticCircleAt u v t)
      (cartesianCoordinates ∘ magneticCircleAt p q t) = 1 := by
  rw [gaussLinking_magnetic_circles_eq u v p q t 0 huv hpq hne]
  rcases le_total (u ^ 2 + v ^ 2) (p ^ 2 + q ^ 2) with hl | hl
  · exact gaussLinking_initial_magnetic_circles_eq_one_of_le u v p q huv hpq hl hne
  · have hsw := gaussLinking_symm (cartesianCoordinates ∘ magneticCircleAt u v 0)
      (cartesianCoordinates ∘ magneticCircleAt p q 0)
      ((contDiff_initialCircle_coords u v).of_le (by norm_num))
      ((contDiff_initialCircle_coords p q).of_le (by norm_num))
      (fun s θ h => (Set.disjoint_left.mp (magnetic_circles_disjoint u v p q 0 huv hpq hne))
        (Set.mem_range_self s) (cartesianCoordinates.injective h ▸ Set.mem_range_self θ))
    exact hsw.trans (gaussLinking_initial_magnetic_circles_eq_one_of_le p q u v hpq huv hl hne.symm)

end Qatlib.Papers.KnottedLight08.NullLinking
