/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.InitialSpatialKnot
public import Qatlib.Papers.KnotLight13.TorusFamily.RationalSmoothness

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Time slices of the rational Bateman pair

[Kedia2013TyingKnots], Eq. (5) and Fig. 3,
[DOI](https://doi.org/10.1103/physrevlett.111.150404).
The rational potentials are constant on explicit straight space-time rays.
At each time these rays induce a homeomorphism of physical space from the
initial slice. It carries the full zero locus of the torus polynomial to
its zero locus at the new time.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Qatlib.Papers.KnotLight13.TorusFamily
  (radialAux rationalAlpha rationalBeta complex_rational_pair_unit torusPolynomial)

/-- The rational Bateman coordinates on a fixed physical time slice. -/
noncomputable def batemanPairAt (t : ℝ) (s : ℝ × ℝ × ℝ) : ℂ × ℂ :=
  (rationalAlpha s.1 s.2.1 s.2.2 t, rationalBeta s.1 s.2.1 s.2.2 t)

/-- The position at time `t` of the straight ray from the given initial point. -/
noncomputable def batemanRay (t : ℝ) (s : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let (x, y, z) := s
  let l := 2 * t / (x ^ 2 + y ^ 2 + z ^ 2 + 1)
  (x + l * (y - z * x), y - l * (x + z * y), z + t - l * (z ^ 2 + 1))

/-- The ray at time zero is at its prescribed initial position. -/
theorem batemanRay_zero (s : ℝ × ℝ × ℝ) : batemanRay 0 s = s := by
  rcases s with ⟨x, y, z⟩
  simp [batemanRay]

/-- Subtracting the first printed potential from one leaves the common factor. -/
theorem one_sub_rationalAlpha (x y z t : ℝ) :
    1 - rationalAlpha x y z t =
      2 * alphaCommonFactor z t / complexDenominator x y z t := by
  change 1 - alphaNumerator x y z t / complexDenominator x y z t = _
  field_simp [complex_denominator_ne_zero]
  simp only [complexDenominator, alphaNumerator, alphaCommonFactor,
    Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat]
  ring

/-- The second printed potential has reduced numerator `x - iy`. -/
theorem rationalBeta_eq_reduced (x y z t : ℝ) :
    rationalBeta x y z t = 2 * betaReducedNumerator x y / complexDenominator x y z t := by
  unfold rationalBeta betaReducedNumerator complexDenominator
  push_cast
  congr 1
  ring

/-- Along a ray the squared spatial radius minus the squared time has an
affine expression in the initial coordinates. -/
private theorem radialAux_batemanRay (x y z t : ℝ) :
    let s := batemanRay t (x, y, z)
    radialAux s.1 s.2.1 s.2.2 t =
      x ^ 2 + y ^ 2 + z ^ 2 + 1 - 2 * t * z := by
  have hd : 0 < x ^ 2 + y ^ 2 + z ^ 2 + 1 := by positivity
  dsimp only [batemanRay, radialAux]
  field_simp [hd.ne']
  ring

/-- The common complex multiplier of the rational numerators and denominator
along a Bateman ray. -/
noncomputable def batemanRayMultiplier (t : ℝ) (s : ℝ × ℝ × ℝ) : ℂ :=
  let l := 2 * t / (s.1 ^ 2 + s.2.1 ^ 2 + s.2.2 ^ 2 + 1)
  (1 - s.2.2 * l : ℝ) + Complex.I * (l : ℂ)

/-- The denominator and the two reduced factors have the same multiplier
along every ray. -/
theorem batemanRay_factors (t : ℝ) (s : ℝ × ℝ × ℝ) :
    let r := batemanRay t s
    let m := batemanRayMultiplier t s
    complexDenominator r.1 r.2.1 r.2.2 t = complexDenominator s.1 s.2.1 s.2.2 0 * m ∧
      alphaCommonFactor r.2.2 t = alphaCommonFactor s.2.2 0 * m ∧
      betaReducedNumerator r.1 r.2.1 = betaReducedNumerator s.1 s.2.1 * m := by
  rcases s with ⟨x, y, z⟩
  let d := x ^ 2 + y ^ 2 + z ^ 2 + 1
  let l := 2 * t / d
  let m := batemanRayMultiplier t (x, y, z)
  have hm : m = (1 - z * l : ℝ) + Complex.I * (l : ℂ) := rfl
  let r := batemanRay t (x, y, z)
  have hd : 0 < d := by positivity
  have hdl : d * l = 2 * t := by
    dsimp only [l]
    field_simp [hd.ne']
  have hw : complexDenominator r.1 r.2.1 r.2.2 t =
      complexDenominator x y z 0 * m := by
    unfold complexDenominator
    rw [radialAux_batemanRay x y z t]
    have hreal : radialAux x y z 0 = d := by simp [d, radialAux]
    rw [hreal]
    refine Complex.ext ?_ ?_ <;>
      simp only [hm, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul,
        mul_zero, one_mul, add_zero, zero_add, sub_zero]
    · change d - 2 * t * z = d * (1 - z * l)
      linear_combination z * hdl
    · exact hdl.symm
  have hg : alphaCommonFactor r.2.2 t = alphaCommonFactor z 0 * m := by
    dsimp only [r, batemanRay, alphaCommonFactor]
    refine Complex.ext ?_ ?_ <;>
      simp only [hm, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, one_mul, add_zero, zero_add,
        sub_zero, zero_sub] <;> ring
  have hb : betaReducedNumerator r.1 r.2.1 = betaReducedNumerator x y * m := by
    dsimp only [r, batemanRay, betaReducedNumerator]
    refine Complex.ext ?_ ?_ <;>
      simp only [hm, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, one_mul, add_zero, zero_add,
        sub_zero, zero_sub] <;> ring
  exact ⟨hw, hg, hb⟩

/-- The complex multiplier of the Bateman factors never vanishes. -/
theorem batemanRayMultiplier_ne_zero (t : ℝ) (s : ℝ × ℝ × ℝ) :
    batemanRayMultiplier t s ≠ 0 := by
  intro hm
  have hw := (batemanRay_factors t s).1
  rw [hm, mul_zero] at hw
  exact complex_denominator_ne_zero _ _ _ _ hw

/-- Both Bateman potentials are constant along each straight ray. -/
theorem batemanPairAt_batemanRay (t : ℝ) (s : ℝ × ℝ × ℝ) :
    batemanPairAt t (batemanRay t s) = initialBatemanPair s := by
  rcases s with ⟨x, y, z⟩
  let r := batemanRay t (x, y, z)
  let m := batemanRayMultiplier t (x, y, z)
  obtain ⟨hw, hg, hb⟩ := batemanRay_factors t (x, y, z)
  change complexDenominator r.1 r.2.1 r.2.2 t = complexDenominator x y z 0 * m at hw
  change alphaCommonFactor r.2.2 t = alphaCommonFactor z 0 * m at hg
  change betaReducedNumerator r.1 r.2.1 = betaReducedNumerator x y * m at hb
  have hm : m ≠ 0 := batemanRayMultiplier_ne_zero t (x, y, z)
  refine Prod.ext ?_ ?_
  · change rationalAlpha r.1 r.2.1 r.2.2 t = rationalAlpha x y z 0
    have h : 1 - rationalAlpha r.1 r.2.1 r.2.2 t = 1 - rationalAlpha x y z 0 := by
      rw [one_sub_rationalAlpha, one_sub_rationalAlpha, hw, hg, ← mul_assoc,
        mul_div_mul_right _ _ hm]
    linear_combination -h
  · change rationalBeta r.1 r.2.1 r.2.2 t = rationalBeta x y z 0
    rw [rationalBeta_eq_reduced, rationalBeta_eq_reduced, hw, hb, ← mul_assoc,
      mul_div_mul_right _ _ hm]

/-- The first Bateman coordinate always has real part strictly less than one. -/
theorem rationalAlpha_re_lt_one (x y z t : ℝ) :
    (rationalAlpha x y z t).re < 1 := by
  have h := congrArg Complex.re (one_sub_rationalAlpha x y z t)
  have hd : 0 < Complex.normSq (complexDenominator x y z t) :=
    Complex.normSq_pos.mpr (complex_denominator_ne_zero x y z t)
  simp only [Complex.sub_re, Complex.one_re, Complex.div_re, Complex.mul_re,
    Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat] at h
  have hr : radialAux x y z t + (t - z) * (2 * t) = x ^ 2 + y ^ 2 + (z - t) ^ 2 + 1 := by
    unfold radialAux
    ring
  have hpos : 0 < x ^ 2 + y ^ 2 + (z - t) ^ 2 + 1 := by positivity
  apply sub_pos.mp
  rw [h, ← add_div]
  apply div_pos _ hd
  simp [alphaCommonFactor, complexDenominator, Complex.mul_re, Complex.mul_im]
  nlinarith only [hr, hpos]

/-- At a fixed time the two potentials distinguish every pair of physical points. -/
theorem batemanPairAt_injective (t : ℝ) : Function.Injective (batemanPairAt t) := by
  rintro ⟨x, y, z⟩ ⟨x', y', z'⟩ h
  have ha : rationalAlpha x y z t = rationalAlpha x' y' z' t := congrArg Prod.fst h
  have hb : rationalBeta x y z t = rationalBeta x' y' z' t := congrArg Prod.snd h
  let w := complexDenominator x y z t
  let w' := complexDenominator x' y' z' t
  let a := radialAux x y z t
  let a' := radialAux x' y' z' t
  have htimes : alphaCommonFactor z t * w' = alphaCommonFactor z' t * w := by
    have he := congrArg (fun a : ℂ => 1 - a) ha
    rw [one_sub_rationalAlpha, one_sub_rationalAlpha,
      div_eq_div_iff (complex_denominator_ne_zero _ _ _ _)
        (complex_denominator_ne_zero _ _ _ _)] at he
    apply mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0)
    simpa only [mul_assoc] using he
  have hreal : a' - (t - z) * (2 * t) = a - (t - z') * (2 * t) := by
    simpa [w, w', a, a', alphaCommonFactor, complexDenominator,
      Complex.mul_re, Complex.mul_im] using congrArg Complex.re htimes
  have himag : (t - z) * a' = (t - z') * a := by
    have h := congrArg Complex.im htimes
    simp only [w, w', alphaCommonFactor, complexDenominator, Complex.mul_re,
      Complex.mul_im, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] at h
    ring_nf at h ⊢
    linarith only [h]
  have hpos : 0 < a + (t - z) * (2 * t) := by
    have hpos : 0 < x ^ 2 + y ^ 2 + (z - t) ^ 2 + 1 := by positivity
    convert hpos using 1
    unfold a radialAux
    ring
  have hzero : (z' - z) * (a + (t - z) * (2 * t)) = 0 := by
    linear_combination himag - (t - z) * hreal
  have hz : z' = z := sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hpos.ne')
  have haa : a' = a := by rw [hz] at hreal; linarith only [hreal]
  have hww : w' = w := by
    unfold w' w complexDenominator
    rw [show radialAux x' y' z' t = radialAux x y z t from haa]
  rw [rationalBeta_eq_reduced, rationalBeta_eq_reduced,
    show complexDenominator x' y' z' t = complexDenominator x y z t from hww,
    div_left_inj' (complex_denominator_ne_zero x y z t)] at hb
  have hbeta : betaReducedNumerator x y = betaReducedNumerator x' y' :=
    mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0) hb
  have hx : x = x' := by
    simpa [betaReducedNumerator, Complex.mul_re] using congrArg Complex.re hbeta
  have hy : y = y' := by
    simpa [betaReducedNumerator, Complex.mul_im] using congrArg Complex.im hbeta
  exact Prod.ext hx (Prod.ext hy hz.symm)

/-- Applying the initial stereographic inverse to the pair on a ray returns its origin. -/
theorem initialCartesianPoint_batemanPairAt_batemanRay (t : ℝ) (s : ℝ × ℝ × ℝ) :
    initialCartesianPoint (batemanPairAt t (batemanRay t s)) = s := by
  rw [batemanPairAt_batemanRay, initialCartesianPoint_initialBatemanPair]

/-- Each physical point at time `t` lies on the ray determined by its pair. -/
theorem batemanRay_initialCartesianPoint_batemanPairAt (t : ℝ) (s : ℝ × ℝ × ℝ) :
    batemanRay t (initialCartesianPoint (batemanPairAt t s)) = s := by
  apply batemanPairAt_injective t
  rw [batemanPairAt_batemanRay]
  apply initialBatemanPair_initialCartesianPoint
  · rcases s with ⟨x, y, z⟩
    simpa only [batemanPairAt, Complex.normSq_eq_norm_sq] using
      complex_rational_pair_unit x y z t
  · exact rationalAlpha_re_lt_one _ _ _ _

/-- The explicit rays vary continuously with time and initial position together. -/
theorem continuous_batemanRay_joint : Continuous (fun a : ℝ × (ℝ × ℝ × ℝ) => batemanRay a.1 a.2) := by
  let A := ℝ × (ℝ × ℝ × ℝ)
  have ht : Continuous (fun a : A => a.1) := continuous_fst
  have hx : Continuous (fun a : A => a.2.1) := continuous_fst.comp continuous_snd
  have hy : Continuous (fun a : A => a.2.2.1) :=
    continuous_fst.comp (continuous_snd.comp continuous_snd)
  have hz : Continuous (fun a : A => a.2.2.2) :=
    continuous_snd.comp (continuous_snd.comp continuous_snd)
  have hl : Continuous (fun a : A =>
      2 * a.1 / (a.2.1 ^ 2 + a.2.2.1 ^ 2 + a.2.2.2 ^ 2 + 1)) :=
    (continuous_const.mul ht).div
      ((((hx.pow 2).add (hy.pow 2)).add (hz.pow 2)).add continuous_const)
      (fun _ => by positivity)
  exact (hx.add (hl.mul (hy.sub (hz.mul hx)))).prodMk
    ((hy.sub (hl.mul (hx.add (hz.mul hy)))).prodMk
      ((hz.add ht).sub (hl.mul ((hz.pow 2).add continuous_const))))

/-- The initial Cartesian inverse is continuous on the image of each time slice. -/
theorem continuous_initialCartesianPoint_batemanPairAt (t : ℝ) :
    Continuous (initialCartesianPoint ∘ batemanPairAt t) := by
  have hi : Continuous (fun s : ℝ × ℝ × ℝ => (s.1, s.2.1, s.2.2, t)) :=
    continuous_fst.prodMk ((continuous_fst.comp continuous_snd).prodMk
      ((continuous_snd.comp continuous_snd).prodMk continuous_const))
  have ha := contDiff_rationalAlpha.continuous.comp hi
  have hb := contDiff_rationalBeta.continuous.comp hi
  change Continuous (fun s => (batemanPairAt t s).1) at ha
  change Continuous (fun s => (batemanPairAt t s).2) at hb
  have hd : Continuous (fun s => 1 - (batemanPairAt t s).1.re) :=
    continuous_const.sub (Complex.continuous_re.comp ha)
  have hne (s : ℝ × ℝ × ℝ) : 1 - (batemanPairAt t s).1.re ≠ 0 :=
    (sub_pos.mpr (rationalAlpha_re_lt_one _ _ _ _)).ne'
  exact ((Complex.continuous_re.comp hb).div hd hne).prodMk
    (((Complex.continuous_im.comp hb).neg.div hd hne).prodMk
      ((Complex.continuous_im.comp ha).div hd hne))

/-- At each time, the rays transport the entire initial physical slice
homeomorphically, with explicit stereographic inverse. -/
noncomputable def batemanSliceHomeomorph (t : ℝ) : (ℝ × ℝ × ℝ) ≃ₜ (ℝ × ℝ × ℝ) where
  toFun := batemanRay t
  invFun := initialCartesianPoint ∘ batemanPairAt t
  left_inv := initialCartesianPoint_batemanPairAt_batemanRay t
  right_inv := batemanRay_initialCartesianPoint_batemanPairAt t
  continuous_toFun := continuous_batemanRay_joint.comp (continuous_const.prodMk continuous_id)
  continuous_invFun := continuous_initialCartesianPoint_batemanPairAt t

/-- The ray transport at any fixed time is injective on the whole
physical space, being the forward map of the slice homeomorphism. -/
theorem batemanRay_injective (t : ℝ) : Function.Injective (batemanRay t) :=
  (batemanSliceHomeomorph t).injective

/-- The physical zero locus of the torus polynomial on the slice at time `t`. -/
def spatialKnotAt (p q : ℕ) (t : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {s | torusPolynomial p q (batemanPairAt t s).1 (batemanPairAt t s).2 = 0}

/-- The ambient homeomorphism transports the entire initial zero locus
onto the entire zero locus at time `t`, for all exponents. -/
theorem batemanSliceHomeomorph_image_initialSpatialKnot (p q : ℕ) (t : ℝ) :
    batemanSliceHomeomorph t '' initialSpatialKnot p q = spatialKnotAt p q t := by
  ext s
  constructor
  · rintro ⟨u, hu, rfl⟩
    change torusPolynomial p q (batemanPairAt t (batemanRay t u)).1
      (batemanPairAt t (batemanRay t u)).2 = 0
    rw [batemanPairAt_batemanRay]
    exact hu
  · intro hs
    refine ⟨(batemanSliceHomeomorph t).symm s, ?_, (batemanSliceHomeomorph t).apply_symm_apply s⟩
    change torusPolynomial p q (initialBatemanPair (initialCartesianPoint (batemanPairAt t s))).1
      (initialBatemanPair (initialCartesianPoint (batemanPairAt t s))).2 = 0
    rw [← batemanPairAt_batemanRay t, batemanRay_initialCartesianPoint_batemanPairAt]
    exact hs

end Qatlib.Papers.KnotLight13.TorusFamily
