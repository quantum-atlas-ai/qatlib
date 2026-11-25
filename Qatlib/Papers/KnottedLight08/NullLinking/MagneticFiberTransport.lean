/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.HopfField.RanadaField
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanTimeSlices

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Transport of the Rañada magnetic fibers

[IrvineBouwmeester2008KnottedLight], Eq. (2) and Fig. 1,
[DOI](https://doi.org/10.1038/nphys1056).
The reflected Bateman pair recovers the Rañada homogeneous coordinates
up to a common real factor. The physical ray homeomorphism transports
the affine fibers and the projective pole fiber to every time slice.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.NullLinking

open Qatlib.Papers.KnottedLight08.HopfField
open Qatlib.Papers.KnotLight13.TorusFamily
open Qatlib.Papers.KnotLight13.TorusFamily (radialAux rationalAlpha rationalBeta)

/-- The two homogeneous magnetic chart entries taken from the real and
imaginary components of the reflected Bateman pair. -/
noncomputable def batemanMagneticPair (w : ℂ × ℂ) : ℂ × ℂ :=
  ((w.1.im : ℂ) + Complex.I * (w.2.im : ℂ),
    (w.2.re : ℂ) + Complex.I * (w.1.re : ℂ))

/-- The reflected Bateman radial coordinate is twice the Rañada letter
`A` on each time slice. -/
private theorem reflected_radialAux (x y z t : ℝ) :
    radialAux x y z (-t) = 2 * ranadaA x y z t := by
  unfold radialAux ranadaA
  ring

/-- The first Bateman entry multiplied by the common positive factor
has real part `S` and imaginary part `Q`. -/
private theorem magnetic_alpha_factor (x y z t : ℝ) :
    rationalAlpha x y z (-t) * ((ranadaA x y z t ^ 2 + t ^ 2 : ℝ) : ℂ) =
      (ranadaS x y z t : ℂ) + Complex.I * (ranadaQ x y z t : ℂ) := by
  change alphaNumerator x y z (-t) / complexDenominator x y z (-t) * _ = _
  field_simp [complex_denominator_ne_zero]
  simp only [alphaNumerator, complexDenominator, reflected_radialAux]
  apply Complex.ext <;>
    simp [ranadaS, ranadaQ, pow_two, Complex.mul_re, Complex.mul_im] <;> ring

/-- The second Bateman entry multiplied by the same factor has real part
`P` and imaginary part `R`. -/
private theorem magnetic_beta_factor (x y z t : ℝ) :
    rationalBeta x y z (-t) * ((ranadaA x y z t ^ 2 + t ^ 2 : ℝ) : ℂ) =
      (ranadaP x y z t : ℂ) + Complex.I * (ranadaR x y z t : ℂ) := by
  rw [rationalBeta_eq_reduced]
  field_simp [complex_denominator_ne_zero]
  simp only [betaReducedNumerator, complexDenominator, reflected_radialAux]
  apply Complex.ext <;>
    simp [ranadaP, ranadaR, pow_two, Complex.mul_re, Complex.mul_im] <;> ring

/-- The actual Rañada homogeneous magnetic coordinates are obtained from
the reflected Bateman pair by one common, nowhere zero factor. -/
theorem ranada_magnetic_pair_eq_bateman (x y z t : ℝ) :
    let w := batemanMagneticPair (batemanPairAt (-t) (x, y, z))
    let d : ℂ := ((ranadaA x y z t ^ 2 + t ^ 2 : ℝ) : ℂ)
    (etaNum x y z t, etaDen x y z t) = (d * w.1, d * w.2) := by
  let d := ranadaA x y z t ^ 2 + t ^ 2
  let w := batemanPairAt (-t) (x, y, z)
  have hα : w.1 * (d : ℂ) = (ranadaS x y z t : ℂ) + Complex.I * (ranadaQ x y z t : ℂ) :=
    magnetic_alpha_factor x y z t
  have hβ : w.2 * (d : ℂ) = (ranadaP x y z t : ℂ) + Complex.I * (ranadaR x y z t : ℂ) :=
    magnetic_beta_factor x y z t
  have hS : d * w.1.re = ranadaS x y z t := by
    simpa [Complex.mul_re, mul_comm] using congrArg Complex.re hα
  have hQ : d * w.1.im = ranadaQ x y z t := by
    simpa [Complex.mul_im, mul_comm] using congrArg Complex.im hα
  have hP : d * w.2.re = ranadaP x y z t := by
    simpa [Complex.mul_re, mul_comm] using congrArg Complex.re hβ
  have hR : d * w.2.im = ranadaR x y z t := by
    simpa [Complex.mul_im, mul_comm] using congrArg Complex.im hβ
  change (etaNum x y z t, etaDen x y z t) =
    ((d : ℂ) * (batemanMagneticPair w).1, (d : ℂ) * (batemanMagneticPair w).2)
  apply Prod.ext
  · change etaNum x y z t = (d : ℂ) * (batemanMagneticPair w).1
    apply Complex.ext <;> simp [etaNum, batemanMagneticPair, Complex.mul_re, Complex.mul_im, hQ, hR]
  · change etaDen x y z t = (d : ℂ) * (batemanMagneticPair w).2
    apply Complex.ext <;> simp [etaDen, batemanMagneticPair, Complex.mul_re, Complex.mul_im, hP, hS]

/-- A reflected Bateman ray preserves the literal Rañada magnetic scalar
and the information determining whether its affine chart is defined. -/
theorem ranada_eta_along_reflected_ray (t : ℝ) (s : ℝ × ℝ × ℝ) :
    let r := batemanRay (-t) s
    (etaDen r.1 r.2.1 r.2.2 t = 0 ↔ etaDen s.1 s.2.1 s.2.2 0 = 0) ∧
      ranadaEta r.1 r.2.1 r.2.2 t = ranadaEta s.1 s.2.1 s.2.2 0 := by
  let r := batemanRay (-t) s
  let wt := batemanMagneticPair (batemanPairAt (-t) r)
  let w0 := batemanMagneticPair (batemanPairAt 0 s)
  let dt : ℂ := ((ranadaA r.1 r.2.1 r.2.2 t ^ 2 + t ^ 2 : ℝ) : ℂ)
  let d0 : ℂ := ((ranadaA s.1 s.2.1 s.2.2 0 ^ 2 + (0 : ℝ) ^ 2 : ℝ) : ℂ)
  have hdt : dt ≠ 0 := Complex.ofReal_ne_zero.mpr (ranadaA_sq_add_t_sq_pos _ _ _ _).ne'
  have hd0 : d0 ≠ 0 := Complex.ofReal_ne_zero.mpr (ranadaA_sq_add_t_sq_pos _ _ _ _).ne'
  have hsame : wt = w0 := congrArg batemanMagneticPair (batemanPairAt_batemanRay (-t) s)
  have ht : (etaNum r.1 r.2.1 r.2.2 t, etaDen r.1 r.2.1 r.2.2 t) =
      (dt * wt.1, dt * wt.2) := ranada_magnetic_pair_eq_bateman _ _ _ _
  have h0 : (etaNum s.1 s.2.1 s.2.2 0, etaDen s.1 s.2.1 s.2.2 0) =
      (d0 * w0.1, d0 * w0.2) := by
    simpa only [neg_zero] using ranada_magnetic_pair_eq_bateman s.1 s.2.1 s.2.2 0
  rw [hsame] at ht
  have htN : etaNum r.1 r.2.1 r.2.2 t = dt * w0.1 := congrArg Prod.fst ht
  have htD : etaDen r.1 r.2.1 r.2.2 t = dt * w0.2 := congrArg Prod.snd ht
  have h0N : etaNum s.1 s.2.1 s.2.2 0 = d0 * w0.1 := congrArg Prod.fst h0
  have h0D : etaDen s.1 s.2.1 s.2.2 0 = d0 * w0.2 := congrArg Prod.snd h0
  change (etaDen r.1 r.2.1 r.2.2 t = 0 ↔ etaDen s.1 s.2.1 s.2.2 0 = 0) ∧
    ranadaEta r.1 r.2.1 r.2.2 t = ranadaEta s.1 s.2.1 s.2.2 0
  constructor
  · rw [htD, h0D, mul_eq_zero, mul_eq_zero, or_iff_right hdt, or_iff_right hd0]
  · rw [ranadaEta_def, ranadaEta_def, htN, htD, h0N, h0D,
      mul_div_mul_left _ _ hdt, mul_div_mul_left _ _ hd0]

/-- A literal finite affine magnetic fiber at any time, with the chart
domain included in the definition. -/
def magneticFiberAt (t : ℝ) (w : ℂ) : Set (ℝ × ℝ × ℝ) :=
  {s | etaDen s.1 s.2.1 s.2.2 t ≠ 0 ∧ ranadaEta s.1 s.2.1 s.2.2 t = w}

/-- The reflected ray homeomorphism carries the complete initial affine
fiber to the corresponding finite magnetic fiber on the new slice. -/
theorem magnetic_fiber_at_eq_reflected_ray_image (t : ℝ) (w : ℂ) :
    batemanRay (-t) '' magneticFiberAt 0 w = magneticFiberAt t w := by
  have hm (s : ℝ × ℝ × ℝ) : batemanRay (-t) s ∈ magneticFiberAt t w ↔ s ∈ magneticFiberAt 0 w := by
    obtain ⟨hden, heta⟩ := ranada_eta_along_reflected_ray t s
    change (etaDen _ _ _ t ≠ 0 ∧ ranadaEta _ _ _ t = w) ↔
      (etaDen _ _ _ 0 ≠ 0 ∧ ranadaEta _ _ _ 0 = w)
    rw [heta, ne_eq, hden]
  ext s
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (hm p).2 hp
  · intro hs
    let p := (batemanSliceHomeomorph (-t)).symm s
    have he : batemanRay (-t) p = s := (batemanSliceHomeomorph (-t)).apply_symm_apply s
    exact ⟨p, (hm p).1 (he ▸ hs), he⟩

/-- The pole fiber is transported by the same ray map, using the
homogeneous denominator to describe it at every time. -/
theorem magnetic_pole_fiber_eq_reflected_ray_image (t : ℝ) :
    batemanRay (-t) '' {s : ℝ × ℝ × ℝ | etaDen s.1 s.2.1 s.2.2 0 = 0} =
      {s : ℝ × ℝ × ℝ | etaDen s.1 s.2.1 s.2.2 t = 0} := by
  ext s
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (ranada_eta_along_reflected_ray t p).1.2 hp
  · intro hs
    let p := (batemanSliceHomeomorph (-t)).symm s
    have he : batemanRay (-t) p = s := (batemanSliceHomeomorph (-t)).apply_symm_apply s
    exact ⟨p, (ranada_eta_along_reflected_ray t p).1.1 (he ▸ hs), he⟩

end Qatlib.Papers.KnottedLight08.NullLinking
