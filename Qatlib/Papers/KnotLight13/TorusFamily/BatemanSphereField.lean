/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.HelicityTransport
public import Qatlib.Papers.KnotLight13.TorusFamily.InitialHelicityDensity
public import Qatlib.Papers.KnotLight13.TorusFamily.PowerCoreLevels
public import Mathlib.Analysis.Complex.Circle

import Qatlib.Papers.KnotLight13.TorusFamily.RationalLineGeometry
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# The powered Bateman fields in sphere coordinates

[Kedia2013TyingKnots], equations (5) and (6).
The differential of the stereographic Bateman pair sends the physical
fields to polynomial fields on the sphere up to a positive radial
factor. The polynomial magnetic field has the weighted phase symmetry
of the product label. On each nonzero strict intermediate real level
its projection to the squared radius and the imaginary product has
nonzero velocity.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Qatlib.Papers.KnotLight13.TorusFamily (radialAux rationalAlpha rationalBeta)
open Qatlib.Papers.KnottedLight08.HopfField (cross3 dot3)
open scoped ComplexConjugate

local notation "Space" => ℝ × ℝ × ℝ

/-- The positive stereographic scale on the initial spatial slice. -/
noncomputable def batemanStereoScale (s : Space) : ℝ :=
  2 / (s.1 ^ 2 + s.2.1 ^ 2 + s.2.2 ^ 2 + 1)

/-- The stereographic factor preserves the direction of time along a line. -/
theorem batemanStereoScale_pos (s : Space) : 0 < batemanStereoScale s := by
  unfold batemanStereoScale
  positivity

/-- The conjugate first gradient contracts with the initial field to
a multiple of the second Bateman coordinate. -/
private theorem conj_alphaGradient_dot_field (x y z : ℝ) :
    dot3 (fun j => conj (alphaGradient x y z 0 j)) (rationalField x y z 0) =
      -16 * rationalBeta x y z 0 / ((x ^ 2 + y ^ 2 + z ^ 2 + 1 : ℝ) : ℂ) ^ 3 := by
  let d := x ^ 2 + y ^ 2 + z ^ 2 + 1
  let u := alphaGradientNumerators x y z 0
  let n := cross3 u (betaGradientNumerators x y z 0)
  have hd : 0 < d := by dsimp [d]; positivity
  have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  have h₀ : complexDenominator x y z 0 = (d : ℂ) := by
    simp [complexDenominator, radialAux, d]
  have hn : dot3 (fun j => conj (u j)) n = -16 * betaNumerator x y * (d : ℂ) ^ 2 := by
    apply Complex.ext <;>
      simp [u, n, dot3, cross3, alphaGradientNumerators, betaGradientNumerators,
        alphaXNumerator, alphaYNumerator, alphaZNumerator, betaXNumerator,
        betaYNumerator, betaZNumerator, betaReducedNumerator, alphaCommonFactor,
        betaNumerator, h₀, Complex.conj_re, Complex.conj_im, Complex.mul_re, Complex.mul_im,
        Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, pow_two, d] <;> ring
  have hβ : rationalBeta x y z 0 = betaNumerator x y / (d : ℂ) := by
    rw [rationalBeta_eq, h₀]
  have hF (j : Fin 3) : rationalField x y z 0 j = n j / (d : ℂ) ^ 4 := by
    rw [rationalField_eq_cross_div, h₀]
  have hA (j : Fin 3) : alphaGradient x y z 0 j = u j / (d : ℂ) ^ 2 := by
    unfold alphaGradient
    rw [h₀]
  calc
    dot3 (fun j => conj (alphaGradient x y z 0 j)) (rationalField x y z 0) =
        dot3 (fun j => conj (u j)) n / (d : ℂ) ^ 6 := by
      simp only [dot3, hA, hF, map_div₀, map_pow, Complex.conj_ofReal]
      field_simp [hdC]
    _ = _ := by
      rw [hn, hβ]
      change -16 * betaNumerator x y * (d : ℂ) ^ 2 / (d : ℂ) ^ 6 =
        -16 * (betaNumerator x y / (d : ℂ)) / (d : ℂ) ^ 3
      field_simp [hdC]

/-- The real contraction of a field orthogonal to a complex gradient
is half the conjugate of its Hermitian contraction. -/
private theorem field_dot_re (f g : Fin 3 → ℂ) (h : dot3 g f = 0) :
    dot3 g (fun i => ((f i).re : ℂ)) =
      conj (dot3 (fun i => conj (g i)) f) / 2 := by
  have hr (z : ℂ) : (z.re : ℂ) = (z + conj z) / 2 := by
    apply Complex.ext <;> simp
  have hc : conj (dot3 (fun i => conj (g i)) f) = dot3 g (fun i => conj (f i)) := by
    simp [dot3, map_add, map_mul]
  rw [hc]
  simp only [hr, dot3] at *
  linear_combination h / 2

/-- The imaginary contraction of a field orthogonal to a complex gradient
is the real contraction multiplied by the imaginary unit. -/
private theorem field_dot_im (f g : Fin 3 → ℂ) (h : dot3 g f = 0) :
    dot3 g (fun i => ((f i).im : ℂ)) = Complex.I * dot3 g (fun i => ((f i).re : ℂ)) := by
  have hs : dot3 g f = dot3 g (fun i => ((f i).re : ℂ)) +
      Complex.I * dot3 g (fun i => ((f i).im : ℂ)) := by
    conv_lhs =>
      unfold dot3
      rw [← Complex.re_add_im (f 0), ← Complex.re_add_im (f 1), ← Complex.re_add_im (f 2)]
    unfold dot3
    ring
  linear_combination
    -Complex.I * (hs.symm.trans h) + dot3 g (fun i => ((f i).im : ℂ)) * Complex.I_mul_I

/-- The power Jacobian in complex sphere coordinates. -/
noncomputable def batemanSphereFactor (p q : ℕ) (w : ℂ × ℂ) : ℂ :=
  (p : ℂ) * w.1 ^ (p - 1) * ((q : ℂ) * w.2 ^ (q - 1))

/-- The normalized sphere-coordinate electric field. -/
noncomputable def batemanSphereElectric (p q : ℕ) (w : ℂ × ℂ) : ℂ × ℂ :=
  (-conj (batemanSphereFactor p q w * w.2), conj (batemanSphereFactor p q w * w.1))

/-- The normalized sphere-coordinate magnetic field. -/
noncomputable def batemanSphereMagnetic (p q : ℕ) (w : ℂ × ℂ) : ℂ × ℂ :=
  (Complex.I * (batemanSphereElectric p q w).1, Complex.I * (batemanSphereElectric p q w).2)

/-- The two coordinates of the differential are their complex Cartesian
gradient contractions. -/
private theorem fderiv_batemanPairAt_apply (t x y z : ℝ) (u : Space) :
    fderiv ℝ (batemanPairAt t) (x, y, z) u =
      (dot3 (alphaGradient x y z t) (fun i => (batemanCartesianCoordinates u i : ℂ)),
       dot3 (betaGradient x y z t) (fun i => (batemanCartesianCoordinates u i : ℂ))) := by
  have ha : (fun s => (batemanPairAt t s).1) = batemanAlphaPower 1 t := by
    funext s
    simp [batemanAlphaPower]
  have hb : (fun s => (batemanPairAt t s).2) = batemanBetaPower 1 t := by
    funext s
    simp [batemanBetaPower]
  have hda := ((contDiff_batemanAlphaPower 1 t).differentiable (by simp) (x, y, z)).hasFDerivAt
  have hdb := ((contDiff_batemanBetaPower 1 t).differentiable (by simp) (x, y, z)).hasFDerivAt
  have hp : batemanPairAt t = fun s => (batemanAlphaPower 1 t s, batemanBetaPower 1 t s) :=
    funext fun s => Prod.ext (congrFun ha s) (congrFun hb s)
  rw [hp, (hda.prodMk hdb).fderiv]
  change (fderiv ℝ (batemanAlphaPower 1 t) (x, y, z) u,
    fderiv ℝ (batemanBetaPower 1 t) (x, y, z) u) = _
  have contract (D : Space →L[ℝ] ℂ) (g : Fin 3 → ℂ)
      (hg : ∀ j, D (batemanAxis j) = g j) :
      D u = dot3 g (fun i => (batemanCartesianCoordinates u i : ℂ)) := by
    conv_lhs => rw [← batemanCartesianBasis.sum_repr u]
    rw [map_sum]
    simp only [map_smul, batemanCartesianBasis_apply, hg, batemanCartesianBasis_repr,
      Complex.real_smul, Fin.sum_univ_three, dot3]
    have hcoord (i : Fin 3) : batemanCartesianCoordinates u i = ![u.1, u.2.1, u.2.2] i := rfl
    simp only [hcoord]
    ring
  apply Prod.ext
  · exact contract _ _ (fun j => by
      rw [fderiv_batemanAlphaPower_axis, alphaPowerGradient_eq]
      simp)
  · exact contract _ _ (fun j => by
      rw [fderiv_batemanBetaPower_axis, betaPowerGradient_eq]
      simp)

/-- The differential of the initial physical chart sends the powered
electric and magnetic fields to their normalized polynomial sphere fields
with the same positive multiplier. -/
theorem fderiv_batemanPairAt_initial_fields (p q : ℕ) (s : Space) :
    let w := batemanPairAt 0 s
    let k := batemanStereoScale s ^ 3
    fderiv ℝ (batemanPairAt 0) s (batemanElectricVector p q 0 s) =
        k • batemanSphereElectric p q w ∧
      fderiv ℝ (batemanPairAt 0) s (batemanMagneticVector p q 0 s) =
        k • batemanSphereMagnetic p q w := by
  rcases s with ⟨x, y, z⟩
  let a := rationalAlpha x y z 0
  let b := rationalBeta x y z 0
  let A := alphaGradient x y z 0
  let B := betaGradient x y z 0
  let F := rationalField x y z 0
  let P := rationalPowerField p q x y z 0
  let m := rationalPowerFactor p q x y z 0
  let d := x ^ 2 + y ^ 2 + z ^ 2 + 1
  let k := (2 / d) ^ 3
  have hP : P = fun j => m * F j := rationalPowerField_eq p q x y z 0
  have factor (g : Fin 3 → ℂ) : dot3 g P = m * dot3 g F := by
    rw [hP]
    unfold dot3
    ring
  have hAF : dot3 A F = 0 := by
    have h := cross3_dot3_left A B
    change dot3 A (cross3 A B) = 0
    unfold dot3 at *
    linear_combination h
  have hBF : dot3 B F = 0 := by
    have h := cross3_dot3_right A B
    change dot3 B (cross3 A B) = 0
    unfold dot3 at *
    linear_combination h
  have hA : dot3 A P = 0 := by rw [factor, hAF, mul_zero]
  have hB : dot3 B P = 0 := by rw [factor, hBF, mul_zero]
  have hcA : dot3 (fun j => conj (A j)) F = -16 * b / (d : ℂ) ^ 3 :=
    conj_alphaGradient_dot_field x y z
  have hcB : dot3 (fun j => conj (B j)) F = 16 * a / (d : ℂ) ^ 3 :=
    conj_betaGradient_dot_rationalField_zero_time x y z
  have hE₁ : dot3 A (fun j => ((P j).re : ℂ)) = (k : ℂ) * -conj (m * b) := by
    rw [field_dot_re P A hA, factor, hcA]
    simp only [map_div₀, map_neg, map_mul, map_pow, map_ofNat, Complex.conj_ofReal, k,
      Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  have hE₂ : dot3 B (fun j => ((P j).re : ℂ)) = (k : ℂ) * conj (m * a) := by
    rw [field_dot_re P B hB, factor, hcB]
    simp only [map_div₀, map_mul, map_pow, map_ofNat, Complex.conj_ofReal, k,
      Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  have hE : batemanCartesianCoordinates (batemanElectricVector p q 0 (x, y, z)) =
      fun j => (P j).re := LinearEquiv.apply_symm_apply _ _
  have hM : batemanCartesianCoordinates (batemanMagneticVector p q 0 (x, y, z)) =
      fun j => (P j).im := LinearEquiv.apply_symm_apply _ _
  constructor
  · rw [fderiv_batemanPairAt_apply, hE]
    change (dot3 A _, dot3 B _) = ((k : ℂ) * -conj (m * b), (k : ℂ) * conj (m * a))
    rw [hE₁, hE₂]
  · rw [fderiv_batemanPairAt_apply, hM]
    change (dot3 A _, dot3 B _) =
      ((k : ℂ) * (Complex.I * -conj (m * b)), (k : ℂ) * (Complex.I * conj (m * a)))
    rw [field_dot_im P A hA, field_dot_im P B hB, hE₁, hE₂]
    apply Prod.ext <;> dsimp only <;> ring

/-- The differential of the Bateman chart at a transported point gives
the same two sphere fields, with the stereographic multiplier divided
by the positive spatial ray Jacobian. -/
theorem fderiv_batemanPairAt_transported_fields (p q : ℕ) (t : ℝ) (s : Space) :
    let y := batemanRay t s
    let w := batemanPairAt t y
    let k := batemanStereoScale s ^ 3 / LinearMap.det (fderiv ℝ (batemanRay t) s).toLinearMap
    fderiv ℝ (batemanPairAt t) y (batemanElectricVector p q t y) =
        k • batemanSphereElectric p q w ∧
      fderiv ℝ (batemanPairAt t) y (batemanMagneticVector p q t y) =
        k • batemanSphereMagnetic p q w := by
  let y := batemanRay t s
  let D := fderiv ℝ (batemanRay t) s
  let L := fderiv ℝ (batemanPairAt t) y
  let J := LinearMap.det D.toLinearMap
  have hJ : 0 < J := det_bateman_ray_pos t s
  have hsmooth : ContDiff ℝ ⊤ (batemanPairAt t) := by
    have h := (contDiff_batemanAlphaPower 1 t).prodMk (contDiff_batemanBetaPower 1 t)
    simpa only [batemanAlphaPower, batemanBetaPower, pow_one, Prod.mk.eta] using h
  have hl := (hsmooth.differentiable (by simp) y).hasFDerivAt
  have hd := ((contDiff_bateman_ray t).differentiable (by simp) s).hasFDerivAt
  have hzero (r : Space) : initialBatemanPair r = batemanPairAt 0 r := by
    simpa only [batemanRay_zero] using (batemanPairAt_batemanRay 0 r).symm
  have hcomp : fderiv ℝ (batemanPairAt 0) s = L.comp D := by
    have h := (hl.comp s hd).fderiv
    change fderiv ℝ (fun r => batemanPairAt t (batemanRay t r)) s = L.comp D at h
    simpa only [batemanPairAt_batemanRay, hzero] using h
  obtain ⟨hE, hB⟩ := batemanRay_transports_vectors p q t s
  obtain ⟨hE₀, hB₀⟩ := fderiv_batemanPairAt_initial_fields p q s
  have normalize (u v : Space) (W : ℂ × ℂ)
      (hu : D u = J • v)
      (hW : fderiv ℝ (batemanPairAt 0) s u = batemanStereoScale s ^ 3 • W) :
      L v = (batemanStereoScale s ^ 3 / J) • W := by
    calc
      L v = J⁻¹ • (J • L v) := by rw [smul_smul, inv_mul_cancel₀ hJ.ne', one_smul]
      _ = J⁻¹ • fderiv ℝ (batemanPairAt 0) s u := by rw [hcomp, ContinuousLinearMap.comp_apply, hu, map_smul]
      _ = _ := by rw [hW, smul_smul, div_eq_mul_inv, mul_comm (J⁻¹)]
  change L (batemanElectricVector p q t y) =
      (batemanStereoScale s ^ 3 / J) • batemanSphereElectric p q (batemanPairAt t y) ∧
    L (batemanMagneticVector p q t y) =
      (batemanStereoScale s ^ 3 / J) • batemanSphereMagnetic p q (batemanPairAt t y)
  rw [(batemanPairAt_batemanRay t s).trans (hzero s)]
  exact ⟨normalize _ _ _ hE hE₀, normalize _ _ _ hB hB₀⟩

/-- Unit phases that fix the product label send the normalized electric
field by the same diagonal action as the sphere point. -/
theorem batemanSphereElectric_phase {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (u v : Circle) (h : (u : ℂ) ^ p * (v : ℂ) ^ q = 1) (w : ℂ × ℂ) :
    batemanSphereElectric p q ((u : ℂ) * w.1, (v : ℂ) * w.2) =
      ((u : ℂ) * (batemanSphereElectric p q w).1,
       (v : ℂ) * (batemanSphereElectric p q w).2) := by
  have cancelPhase {n : ℕ} (hn : 0 < n) (a : Circle) (b : ℂ)
      (hab : (a : ℂ) ^ n * b = 1) :
      conj ((a : ℂ) ^ (n - 1) * b) = a := by
    have ht : (a : ℂ) ^ (n - 1) * b = conj (a : ℂ) := by
      apply mul_left_cancel₀ (Circle.coe_ne_zero a)
      rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hn, hab, Complex.mul_conj', Circle.norm_coe]
      norm_num
    rw [ht]
    exact star_star (a : ℂ)
  have hu := cancelPhase hp u ((v : ℂ) ^ q) h
  have hv := cancelPhase hq v ((u : ℂ) ^ p) (by simpa only [mul_comm] using h)
  have mulA : (u : ℂ) ^ (p - 1) * (v : ℂ) ^ (q - 1) * (v : ℂ) =
      (u : ℂ) ^ (p - 1) * (v : ℂ) ^ q := by
    rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel hq]
  have mulB : (u : ℂ) ^ (p - 1) * (v : ℂ) ^ (q - 1) * (u : ℂ) =
      (v : ℂ) ^ (q - 1) * (u : ℂ) ^ p := by
    rw [mul_comm ((u : ℂ) ^ (p - 1)), mul_assoc, ← pow_succ, Nat.sub_add_cancel hp]
  apply Prod.ext
  · dsimp only [batemanSphereElectric, batemanSphereFactor]
    have hmul : (p : ℂ) * ((u : ℂ) * w.1) ^ (p - 1) *
        ((q : ℂ) * ((v : ℂ) * w.2) ^ (q - 1)) * ((v : ℂ) * w.2) =
        ((u : ℂ) ^ (p - 1) * (v : ℂ) ^ (q - 1) * (v : ℂ)) *
          ((p : ℂ) * w.1 ^ (p - 1) * ((q : ℂ) * w.2 ^ (q - 1)) * w.2) := by
      rw [mul_pow, mul_pow]
      ring
    rw [hmul, mulA, map_mul, hu, mul_neg]
  · dsimp only [batemanSphereElectric, batemanSphereFactor]
    have hmul : (p : ℂ) * ((u : ℂ) * w.1) ^ (p - 1) *
        ((q : ℂ) * ((v : ℂ) * w.2) ^ (q - 1)) * ((u : ℂ) * w.1) =
        ((u : ℂ) ^ (p - 1) * (v : ℂ) ^ (q - 1) * (u : ℂ)) *
          ((p : ℂ) * w.1 ^ (p - 1) * ((q : ℂ) * w.2 ^ (q - 1)) * w.1) := by
      rw [mul_pow, mul_pow]
      ring
    rw [hmul, mulB, map_mul, hv]

/-- The normalized magnetic field is equivariant under the same phases. -/
theorem batemanSphereMagnetic_phase {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (u v : Circle) (h : (u : ℂ) ^ p * (v : ℂ) ^ q = 1) (w : ℂ × ℂ) :
    batemanSphereMagnetic p q ((u : ℂ) * w.1, (v : ℂ) * w.2) =
      ((u : ℂ) * (batemanSphereMagnetic p q w).1,
       (v : ℂ) * (batemanSphereMagnetic p q w).2) := by
  unfold batemanSphereMagnetic
  rw [batemanSphereElectric_phase hp hq u v h w]
  apply Prod.ext <;> dsimp only <;> ring

/-- Along a normalized magnetic trajectory the first squared radius has
velocity `-2pq Im(α^p β^q)`. This is one component of the quotient motion. -/
theorem hasDerivAt_batemanSphereMagnetic_radius {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {w : ℝ → ℂ × ℂ} {s : ℝ}
    (hw : HasDerivAt w (batemanSphereMagnetic p q (w s)) s) :
    HasDerivAt (fun u => Complex.normSq (w u).1)
      (-2 * (p : ℝ) * (q : ℝ) * (((w s).1 ^ p * (w s).2 ^ q).im)) s := by
  let a := (w s).1
  let b := (w s).2
  let v := (batemanSphereMagnetic p q (w s)).1
  have hv : HasDerivAt (fun u => (w u).1) v s := hw.fst
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hv
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hv
  have hab : a * (batemanSphereFactor p q (w s) * b) =
      (p : ℂ) * (q : ℂ) * (a ^ p * b ^ q) := by
    change a * ((p : ℂ) * a ^ (p - 1) * ((q : ℂ) * b ^ (q - 1)) * b) = _
    rw [show a ^ p = a ^ (p - 1) * a by rw [← pow_succ, Nat.sub_add_cancel hp],
      show b ^ q = b ^ (q - 1) * b by rw [← pow_succ, Nat.sub_add_cancel hq]]
    ring
  have hg : conj a * v = -Complex.I * conj ((p : ℂ) * (q : ℂ) * (a ^ p * b ^ q)) := by
    change conj a * (Complex.I * -conj (batemanSphereFactor p q (w s) * b)) = _
    rw [← hab]
    simp only [map_mul]
    ring
  have heq : v.re * a.re + a.re * v.re + (v.im * a.im + a.im * v.im) =
      -2 * (p : ℝ) * (q : ℝ) * (a ^ p * b ^ q).im := by
    have h := congrArg Complex.re hg
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.neg_re,
      Complex.I_re, Complex.I_im, zero_mul, neg_mul, one_mul, sub_neg_eq_add,
      Complex.mul_im, Complex.natCast_re, Complex.natCast_im, mul_zero, zero_add, sub_zero] at h
    simp only [Complex.mul_im]
    linear_combination 2 * h
  have hsq := (hr.mul hr).add (hi.mul hi)
  change HasDerivAt (fun u => ((w u).1).re * ((w u).1).re + ((w u).1).im * ((w u).1).im)
    (v.re * a.re + a.re * v.re + (v.im * a.im + a.im * v.im)) s at hsq
  simpa only [Complex.normSq_apply, heq] using hsq

/-- The full derivative of the magnetic product label is purely imaginary. -/
theorem hasDerivAt_batemanSphereMagnetic_product {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {w : ℝ → ℂ × ℂ} {s : ℝ}
    (hw : HasDerivAt w (batemanSphereMagnetic p q (w s)) s) :
    HasDerivAt (fun u => (w u).1 ^ p * (w u).2 ^ q)
      (Complex.I * (((p : ℝ) * (q : ℝ) * Complex.normSq (w s).1 ^ (p - 1) *
        Complex.normSq (w s).2 ^ (q - 1) *
        ((q : ℝ) * Complex.normSq (w s).1 - (p : ℝ) * Complex.normSq (w s).2) : ℝ) : ℂ)) s := by
  let a := (w s).1
  let b := (w s).2
  let m := batemanSphereFactor p q (w s)
  let A := a ^ (p - 1)
  let B := b ^ (q - 1)
  let u := (batemanSphereMagnetic p q (w s)).1
  let v := (batemanSphereMagnetic p q (w s)).2
  have ha : a ^ p = A * a := by dsimp [A]; rw [← pow_succ, Nat.sub_add_cancel hp]
  have hb : b ^ q = B * b := by dsimp [B]; rw [← pow_succ, Nat.sub_add_cancel hq]
  have haNorm : a * conj a = (Complex.normSq a : ℂ) := by
    rw [Complex.mul_conj', Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hbNorm : b * conj b = (Complex.normSq b : ℂ) := by
    rw [Complex.mul_conj', Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  have hm : conj m * (A * B) = (p : ℂ) * (q : ℂ) *
      (Complex.normSq a : ℂ) ^ (p - 1) * (Complex.normSq b : ℂ) ^ (q - 1) := by
    calc
      conj m * (A * B) = (p : ℂ) * (q : ℂ) * (A * conj A) * (B * conj B) := by
        change conj ((p : ℂ) * A * ((q : ℂ) * B)) * (A * B) = _
        simp only [map_mul, map_natCast]
        ring
      _ = _ := by
        dsimp only [A, B]
        rw [map_pow, map_pow, ← mul_pow, ← mul_pow, haNorm, hbNorm]
  have hvel : (p : ℂ) * A * u * b ^ q + a ^ p * ((q : ℂ) * B * v) =
      Complex.I * ((p : ℂ) * (q : ℂ) * (Complex.normSq a : ℂ) ^ (p - 1) *
        (Complex.normSq b : ℂ) ^ (q - 1) *
        ((q : ℂ) * (Complex.normSq a : ℂ) - (p : ℂ) * (Complex.normSq b : ℂ))) := by
    calc
      _ = Complex.I * (conj m * (A * B)) * ((q : ℂ) * (a * conj a) - (p : ℂ) * (b * conj b)) := by
        change (p : ℂ) * A * (Complex.I * -conj (m * b)) * b ^ q +
          a ^ p * ((q : ℂ) * B * (Complex.I * conj (m * a))) = _
        rw [ha, hb]
        simp only [map_mul]
        ring
      _ = _ := by rw [hm, haNorm, hbNorm]; ring
  have hu : HasDerivAt (fun r => (w r).1) u s := hw.fst
  have hv : HasDerivAt (fun r => (w r).2) v s := hw.snd
  open Qatlib.Papers.KnotLight13.Bateman in
  have hder := (power_derivative _ _ _ p hu).mul (power_derivative _ _ _ q hv)
  change HasDerivAt (fun r => (w r).1 ^ p * (w r).2 ^ q)
    ((p : ℂ) * A * u * b ^ q + a ^ p * ((q : ℂ) * B * v)) s at hder
  let speed : ℝ := (p : ℝ) * (q : ℝ) * Complex.normSq a ^ (p - 1) *
    Complex.normSq b ^ (q - 1) * ((q : ℝ) * Complex.normSq a - (p : ℝ) * Complex.normSq b)
  have hcast : ((p : ℂ) * (q : ℂ) * (Complex.normSq a : ℂ) ^ (p - 1) *
      (Complex.normSq b : ℂ) ^ (q - 1) *
      ((q : ℂ) * (Complex.normSq a : ℂ) - (p : ℂ) * (Complex.normSq b : ℂ))) = (speed : ℂ) := by
    unfold speed
    push_cast
    rfl
  rw [hvel, hcast] at hder
  exact hder

/-- The imaginary part of the magnetic product label has velocity
proportional to `q |α|² - p |β|²`, with a positive factor off the axes. -/
theorem hasDerivAt_batemanSphereMagnetic_imaginary {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {w : ℝ → ℂ × ℂ} {s : ℝ}
    (hw : HasDerivAt w (batemanSphereMagnetic p q (w s)) s) :
    HasDerivAt (fun u => ((w u).1 ^ p * (w u).2 ^ q).im)
      ((p : ℝ) * (q : ℝ) * Complex.normSq (w s).1 ^ (p - 1) *
        Complex.normSq (w s).2 ^ (q - 1) *
        ((q : ℝ) * Complex.normSq (w s).1 - (p : ℝ) * Complex.normSq (w s).2)) s := by
  have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s
    (hasDerivAt_batemanSphereMagnetic_product hp hq hw)
  change HasDerivAt (fun r => ((w r).1 ^ p * (w r).2 ^ q).im) _ s at h
  simpa only [Complex.imCLM_apply, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, one_mul, zero_add] using h

/-- At an intermediate nonzero real level, the normalized magnetic
velocity is transverse to the circle fibers of the quotient by the
weighted phase action. In squared-radius and imaginary-product
coordinates, its projected derivative never vanishes. -/
theorem batemanSphereMagnetic_quotient_deriv_ne_zero
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {w : ℝ → ℂ × ℂ} {s : ℝ}
    (hw : HasDerivAt w (batemanSphereMagnetic p q (w s)) s)
    (hs : Complex.normSq (w s).1 + Complex.normSq (w s).2 = 1)
    (h₀ : ((w s).1 ^ p * (w s).2 ^ q).re ≠ 0)
    (hc : |((w s).1 ^ p * (w s).2 ^ q).re| < poweredPeakAmplitude p q) :
    deriv (fun u => (Complex.normSq (w u).1, ((w u).1 ^ p * (w u).2 ^ q).im)) s ≠ 0 := by
  let a := (w s).1
  let b := (w s).2
  let g := a ^ p * b ^ q
  have ha : a ≠ 0 := by
    intro ha
    exact h₀ (by change g.re = 0; simp [g, ha, zero_pow hp.ne'])
  have hb : b ≠ 0 := by
    intro hb
    exact h₀ (by change g.re = 0; simp [g, hb, zero_pow hq.ne'])
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hpos : 0 < (p : ℝ) * (q : ℝ) * Complex.normSq a ^ (p - 1) *
      Complex.normSq b ^ (q - 1) :=
    mul_pos (mul_pos (mul_pos hpR hqR) (pow_pos (Complex.normSq_pos.mpr ha) _))
      (pow_pos (Complex.normSq_pos.mpr hb) _)
  have hr := hasDerivAt_batemanSphereMagnetic_radius hp hq hw
  have hi := hasDerivAt_batemanSphereMagnetic_imaginary hp hq hw
  rw [(HasDerivAt.prodMk hr hi).deriv]
  intro hz
  have h₁ : -2 * (p : ℝ) * (q : ℝ) * g.im = 0 := congrArg Prod.fst hz
  have h₂ : (p : ℝ) * (q : ℝ) * Complex.normSq a ^ (p - 1) * Complex.normSq b ^ (q - 1) *
      ((q : ℝ) * Complex.normSq a - (p : ℝ) * Complex.normSq b) = 0 := congrArg Prod.snd hz
  have hIm : g.im = 0 := (mul_eq_zero.mp h₁).resolve_left (by positivity)
  have hbal := (mul_eq_zero.mp h₂).resolve_left hpos.ne'
  have hRad : Complex.normSq a = poweredPeakRadius p q := by
    rw [poweredPeakRadius, eq_div_iff (add_pos hpR hqR).ne']
    change Complex.normSq a + Complex.normSq b = 1 at hs
    linear_combination hbal + (p : ℝ) * hs
  have hNorm : Complex.normSq g = poweredPeakAmplitude p q ^ 2 :=
    (normSq_poweredProduct_eq_peak_iff hp hq hs).2 hRad
  have hSq : g.re ^ 2 < poweredPeakAmplitude p q ^ 2 := by
    simpa only [sq_abs] using pow_lt_pow_left₀ hc (abs_nonneg _) (by decide : (2 : ℕ) ≠ 0)
  rw [Complex.normSq_apply, hIm, mul_zero, add_zero, ← pow_two] at hNorm
  exact hSq.ne hNorm

end Qatlib.Papers.KnotLight13.TorusFamily
