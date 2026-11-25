/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanPhysicalCores
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanCoreLinks
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanSphereField

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Core velocity of the actual Bateman fields at the initial time

[Kedia2013TyingKnots], p. 150404-3,
[DOI](https://doi.org/10.1103/physrevlett.111.150404).
Along every extremal core circle the normalized sphere polynomial fields
are an exact constant complex multiple of the winding tangent of the
core parametrization. Chaining this algebraic identity with the
differential of the initial stereographic chart, which is injective
because it has a global Cartesian left inverse, proves that the actual
electric and magnetic vectors on a signed extremal core are a
nowhere-vanishing real multiple of the actual velocity of the core
circle. This is the substantive bridge feeding the periodic core field
lines; no closed-orbit statement is assumed anywhere.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Set
open scoped ComplexConjugate

local notation "Space" => ℝ × ℝ × ℝ

/-- The winding tangent of a torus circle in sphere coordinates: the
first complex coordinate turns `q` times and the second `-p` times. -/
noncomputable def batemanCoreSphereTangent (p q : ℕ) (z : ℂ × ℂ) : ℂ × ℂ :=
  (Complex.I * (q : ℂ) * z.1, -(Complex.I * (p : ℂ) * z.2))

/-- The constant complex rate of the normalized sphere magnetic field
along the extremal phase fiber with the given phase. -/
noncomputable def batemanCorePhaseRate (P Q : ℕ) (phase : Circle) : ℂ :=
  -((((P : ℝ) + Q) * poweredPeakAmplitude P Q : ℝ) * conj (phase : ℂ))

/-- The winding tangent never vanishes on an extremal sphere fiber,
because its first component is a nonzero multiple of the first
coordinate. -/
theorem batemanCoreSphereTangent_ne_zero {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {phase : Circle}
    {z : ℂ × ℂ} (hz : z ∈ poweredSphereCore p q phase) :
    batemanCoreSphereTangent p q z ≠ 0 := by
  intro h
  have h₁ : Complex.I * (q : ℂ) * z.1 = 0 := congrArg Prod.fst h
  have hnorm := (poweredSphereCore_norms hp hq hz).1
  have hz₁ : z.1 ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hnorm
    exact ((poweredCoreRadii_spec hp hq).1).ne' hnorm.symm
  rcases mul_eq_zero.mp h₁ with h | h
  · exact Complex.I_ne_zero
      ((mul_eq_zero.mp h).resolve_right fun hc => hq.ne (by exact_mod_cast hc.symm))
  · exact hz₁ h

/-- Scaling both exponents by the same nonnegative integer only
rescales the winding tangent of the core circle. -/
theorem batemanCoreSphereTangent_mul_exponents (p q d : ℕ) (z : ℂ × ℂ) :
    batemanCoreSphereTangent (p * d) (q * d) z = (d : ℂ) • batemanCoreSphereTangent p q z := by
  apply Prod.ext
  · dsimp only [batemanCoreSphereTangent, Prod.smul_def, smul_eq_mul]
    push_cast
    ring
  · dsimp only [batemanCoreSphereTangent, Prod.smul_def, smul_eq_mul]
    push_cast
    ring

/-- A nonzero complex number has a nonzero conjugate. -/
private theorem conj_ne_zero_of_ne_zero {z : ℂ} (hz : z ≠ 0) : conj z ≠ 0 := by
  intro h
  apply hz
  apply norm_eq_zero.mp
  rw [← Complex.norm_conj z, h, norm_zero]

/-- Bridge for the derivative value of a reciprocal power curve: the
quotient-rule value collapses to the reciprocal-times-rate form. -/
private theorem bridge_div_value {X W Y v c : ℂ} (hX : X ≠ 0) (hYW : Y * W = X) :
    ((0 : ℂ) * X - v * (c * Y * (Complex.I * W))) / X ^ 2 = -(Complex.I * c) * (v / X) := by
  rw [zero_mul, zero_sub, ← mul_div_assoc, div_eq_div_iff (pow_ne_zero 2 hX) hX]
  linear_combination (-(Complex.I * c * v * X)) * hYW

/-- The normalized sphere magnetic field on an extremal phase fiber is
the constant complex rate times the winding tangent. -/
theorem batemanSphereMagnetic_fiber_eq {P Q : ℕ} (hP : 0 < P) (hQ : 0 < Q) {phase : Circle}
    {z : ℂ × ℂ} (hz : z ∈ poweredSphereCore P Q phase) :
    batemanSphereMagnetic P Q z =
      batemanCorePhaseRate P Q phase • batemanCoreSphereTangent P Q z := by
  obtain ⟨ha, hb, hₐ, hᵦ⟩ := poweredCoreRadii_spec hP hQ
  obtain ⟨hnorms, hprod⟩ := id hz
  have hna : ‖z.1‖ = (poweredCoreRadii P Q).1 := (poweredSphereCore_norms hP hQ hz).1
  have hnb : ‖z.2‖ = (poweredCoreRadii P Q).2 := (poweredSphereCore_norms hP hQ hz).2
  have ha₀ : z.1 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hna
    exact ha.ne' hna.symm
  have hb₀ : z.2 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnb
    exact hb.ne' hnb.symm
  have hsplit1 : z.1 ^ P = z.1 ^ (P - 1) * z.1 := by rw [← pow_succ, Nat.sub_add_cancel hP]
  have hsplit2 : z.2 ^ Q = z.2 ^ (Q - 1) * z.2 := by rw [← pow_succ, Nat.sub_add_cancel hQ]
  rw [hsplit1, hsplit2] at hprod
  have hnsq1 : Complex.normSq z.1 = poweredPeakRadius P Q := by
    rw [Complex.normSq_eq_norm_sq, hna, hₐ]
  have hnsq2 : Complex.normSq z.2 = 1 - poweredPeakRadius P Q := by
    rw [Complex.normSq_eq_norm_sq, hnb, hᵦ]
  have hca : z.1 * conj z.1 = ((poweredPeakRadius P Q : ℝ) : ℂ) := by
    rw [Complex.mul_conj, hnsq1]
  have hcb : z.2 * conj z.2 = ((1 - poweredPeakRadius P Q : ℝ) : ℂ) := by
    rw [Complex.mul_conj, hnsq2]
  have hden1 : (((poweredPeakRadius P Q : ℝ) : ℂ) * ((P : ℂ) + (Q : ℂ))) = (P : ℂ) := by
    have h : ((poweredPeakRadius P Q) * ((P : ℝ) + Q)) = (P : ℝ) := by
      unfold poweredPeakRadius
      field_simp
    exact_mod_cast h
  have hden2 : ((((1 - poweredPeakRadius P Q : ℝ) : ℂ)) * ((P : ℂ) + (Q : ℂ))) = (Q : ℂ) := by
    have h : ((1 - poweredPeakRadius P Q) * ((P : ℝ) + Q)) = (Q : ℝ) := by
      unfold poweredPeakRadius
      field_simp; ring
    exact_mod_cast h
  have key1 : batemanSphereFactor P Q z * z.2 * z.1 =
      (P : ℂ) * (Q : ℂ) * (poweredPeakAmplitude P Q : ℂ) * (phase : ℂ) := by
    dsimp only [batemanSphereFactor]
    linear_combination ((P : ℂ) * (Q : ℂ)) * hprod
  have key2 : batemanSphereFactor P Q z * z.1 * z.2 =
      (P : ℂ) * (Q : ℂ) * (poweredPeakAmplitude P Q : ℂ) * (phase : ℂ) := by
    dsimp only [batemanSphereFactor]
    linear_combination ((P : ℂ) * (Q : ℂ)) * hprod
  apply Prod.ext
  · dsimp only [batemanSphereMagnetic, batemanSphereElectric, batemanCoreSphereTangent,
      batemanCorePhaseRate, Prod.smul_def, smul_eq_mul]
    refine (mul_right_cancel₀ (conj_ne_zero_of_ne_zero ha₀)) ?_
    rw [show (Complex.I * (-(conj (batemanSphereFactor P Q z * z.2)))) * conj z.1 =
        Complex.I * (-(conj (batemanSphereFactor P Q z * z.2) * conj z.1)) by ring,
      ← map_mul (starRingEnd ℂ), key1]
    simp only [map_mul, map_natCast, Complex.conj_ofReal]
    push_cast
    linear_combination
      (Complex.I * (conj (phase : ℂ) * (Q : ℂ) *
          (((P : ℂ) + Q) * (poweredPeakAmplitude P Q : ℂ)))) * hca +
      (Complex.I * (conj (phase : ℂ) * (Q : ℂ) *
        (poweredPeakAmplitude P Q : ℂ))) * hden1
  · dsimp only [batemanSphereMagnetic, batemanSphereElectric, batemanCoreSphereTangent,
      batemanCorePhaseRate, Prod.smul_def, smul_eq_mul]
    refine (mul_right_cancel₀ (conj_ne_zero_of_ne_zero hb₀)) ?_
    rw [show (Complex.I * (conj (batemanSphereFactor P Q z * z.1))) * conj z.2 =
        Complex.I * (conj (batemanSphereFactor P Q z * z.1) * conj z.2) by ring,
      ← map_mul (starRingEnd ℂ), key2]
    simp only [map_mul, map_natCast, Complex.conj_ofReal]
    push_cast
    linear_combination
      (-(Complex.I * (conj (phase : ℂ) * (P : ℂ) *
          (((P : ℂ) + Q) * (poweredPeakAmplitude P Q : ℂ))))) * hcb +
      (-(Complex.I * (conj (phase : ℂ) * (P : ℂ) *
        (poweredPeakAmplitude P Q : ℂ)))) * hden2

/-- The normalized sphere electric field on an extremal phase fiber is
minus the imaginary unit times the magnetic rate, times the winding
tangent. -/
theorem batemanSphereElectric_fiber_eq {P Q : ℕ} (hP : 0 < P) (hQ : 0 < Q) {phase : Circle}
    {z : ℂ × ℂ} (hz : z ∈ poweredSphereCore P Q phase) :
    batemanSphereElectric P Q z =
      (-Complex.I * batemanCorePhaseRate P Q phase) • batemanCoreSphereTangent P Q z := by
  have hmag := batemanSphereMagnetic_fiber_eq hP hQ hz
  have hrel : batemanSphereElectric P Q z = (-Complex.I) • batemanSphereMagnetic P Q z := by
    apply Prod.ext
    · unfold batemanSphereMagnetic batemanSphereElectric
      rw [Prod.smul_def, smul_eq_mul]
      linear_combination (-(conj (batemanSphereFactor P Q z * z.2))) * Complex.I_mul_I
    · unfold batemanSphereMagnetic batemanSphereElectric
      rw [Prod.smul_def, smul_eq_mul]
      linear_combination (conj (batemanSphereFactor P Q z * z.1)) * Complex.I_mul_I
  rw [hrel, hmag, smul_smul]

/-- The real parametrization of the sphere core through the circle
exponential. -/
noncomputable def poweredCoreSphereExp (p q : ℕ) (phase : Circle) (θ : ℝ) : ℂ × ℂ :=
  poweredCoreSphereParam p q phase (Circle.exp θ)

/-- The derivative of the circle exponential as a complex curve. -/
theorem hasDerivAt_circleExp_coe (θ : ℝ) :
    HasDerivAt (fun u => (Circle.exp u : ℂ)) (Complex.I * (Circle.exp θ : ℂ)) θ := by
  have hcoe : (fun u => (Circle.exp u : ℂ)) =
      fun u : ℝ => Complex.exp ((u : ℂ) * Complex.I) := by
    funext u
    exact Circle.coe_exp u
  rw [hcoe]
  have h1 : HasDerivAt (fun u : ℝ => (u : ℂ) * Complex.I) ((1 : ℂ) * Complex.I) θ :=
    (Complex.ofRealCLM.hasDerivAt).mul_const Complex.I
  have h := h1.cexp
  simp only [one_mul] at h
  refine h.congr_deriv ?_
  rw [Circle.coe_exp]
  ring

/-- The lifted core circle parametrization has the winding tangent as
its derivative. -/
theorem hasDerivAt_poweredCoreSphereExp {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (phase : Circle)
    (θ : ℝ) :
    HasDerivAt (poweredCoreSphereExp p q phase)
      (batemanCoreSphereTangent p q (poweredCoreSphereExp p q phase θ)) θ := by
  have hEne : (Circle.exp θ : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hpowq : HasDerivAt (fun u => (Circle.exp u : ℂ) ^ q)
      ((q : ℂ) * (Circle.exp θ : ℂ) ^ (q - 1) * (Complex.I * (Circle.exp θ : ℂ))) θ :=
    (hasDerivAt_circleExp_coe θ).pow q
  have hpowp : HasDerivAt (fun u => (Circle.exp u : ℂ) ^ p)
      ((p : ℂ) * (Circle.exp θ : ℂ) ^ (p - 1) * (Complex.I * (Circle.exp θ : ℂ))) θ :=
    (hasDerivAt_circleExp_coe θ).pow p
  have hEq : (Circle.exp θ : ℂ) ^ (q - 1) * (Circle.exp θ : ℂ) =
      (Circle.exp θ : ℂ) ^ q := by rw [← pow_succ, Nat.sub_add_cancel hq]
  have hEp : (Circle.exp θ : ℂ) ^ (p - 1) * (Circle.exp θ : ℂ) =
      (Circle.exp θ : ℂ) ^ p := by rw [← pow_succ, Nat.sub_add_cancel hp]
  have hcoe₁ : ((phase ^ Nat.gcdA p q : Circle) : ℂ) * (Circle.exp θ : ℂ) ^ q =
      ((phase ^ Nat.gcdA p q * Circle.exp θ ^ q : Circle) : ℂ) := by
    simp [Circle.coe_mul, Circle.coe_pow, Circle.coe_zpow]
  have hcoe₂ : ((phase ^ Nat.gcdB p q : Circle) : ℂ) / (Circle.exp θ : ℂ) ^ p =
      ((phase ^ Nat.gcdB p q / Circle.exp θ ^ p : Circle) : ℂ) := by
    simp [Circle.coe_div, Circle.coe_pow, Circle.coe_zpow]
  have h₁ : HasDerivAt (fun u : ℝ => ((phase ^ Nat.gcdA p q : Circle) : ℂ) *
      (Circle.exp u : ℂ) ^ q)
      (Complex.I * (q : ℂ) * (((phase ^ Nat.gcdA p q : Circle) : ℂ) *
        (Circle.exp θ : ℂ) ^ q)) θ := by
    refine (hpowq.const_mul ((phase ^ Nat.gcdA p q : Circle) : ℂ)).congr_deriv ?_
    linear_combination ((phase ^ Nat.gcdA p q : Circle) : ℂ) * (q : ℂ) * Complex.I * hEq
  have h₂ : HasDerivAt (fun u : ℝ => ((phase ^ Nat.gcdB p q : Circle) : ℂ) /
      (Circle.exp u : ℂ) ^ p)
      (((0 : ℂ) * (Circle.exp θ : ℂ) ^ p - ((phase ^ Nat.gcdB p q : Circle) : ℂ) *
        ((p : ℂ) * (Circle.exp θ : ℂ) ^ (p - 1) * (Complex.I * (Circle.exp θ : ℂ)))) /
        ((Circle.exp θ : ℂ) ^ p) ^ 2) θ :=
    (hasDerivAt_const θ ((phase ^ Nat.gcdB p q : Circle) : ℂ)).div hpowp
      (pow_ne_zero _ hEne)
  have h₂' : HasDerivAt (fun u : ℝ => ((phase ^ Nat.gcdB p q : Circle) : ℂ) /
      (Circle.exp u : ℂ) ^ p)
      (-(Complex.I * (p : ℂ)) * (((phase ^ Nat.gcdB p q : Circle) : ℂ) /
        (Circle.exp θ : ℂ) ^ p)) θ := by
    refine h₂.congr_deriv ?_
    exact bridge_div_value (pow_ne_zero _ hEne) hEp
  have hfinal₁ : HasDerivAt (fun u : ℝ => ((poweredCoreRadii p q).1 : ℂ) *
      ((phase ^ Nat.gcdA p q * Circle.exp u ^ q : Circle) : ℂ))
      (Complex.I * (q : ℂ) * (((poweredCoreRadii p q).1 : ℂ) *
        ((phase ^ Nat.gcdA p q * Circle.exp θ ^ q : Circle) : ℂ))) θ := by
    refine (h₁.const_mul ((poweredCoreRadii p q).1 : ℂ)).congr_deriv ?_
    rw [hcoe₁]
    ring
  have hfinal₂ : HasDerivAt (fun u : ℝ => ((poweredCoreRadii p q).2 : ℂ) *
      ((phase ^ Nat.gcdB p q / Circle.exp u ^ p : Circle) : ℂ))
      (-(Complex.I * (p : ℂ)) * (((poweredCoreRadii p q).2 : ℂ) *
        ((phase ^ Nat.gcdB p q / Circle.exp θ ^ p : Circle) : ℂ))) θ := by
    refine (h₂'.const_mul ((poweredCoreRadii p q).2 : ℂ)).congr_deriv ?_
    rw [hcoe₂]
    ring
  unfold poweredCoreSphereExp poweredCoreSphereParam poweredTorusPhaseParam
  refine (HasDerivAt.prodMk hfinal₁ hfinal₂).congr_deriv ?_
  apply Prod.ext
  · dsimp only [batemanCoreSphereTangent]
  · dsimp only [batemanCoreSphereTangent]
    ring

/-- The lifted core circle parametrization lands on the sphere fiber of
its phase. -/
theorem poweredCoreSphereExp_mem {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (phase : Circle) (θ : ℝ) :
    poweredCoreSphereExp p q phase θ ∈ poweredSphereCore p q phase :=
  poweredCoreSphereParam_mem hp hq hpq phase (Circle.exp θ)

/-- The initial Cartesian chart is differentiable away from its pole. -/
private theorem differentiableAt_initialCartesianPoint {z : ℂ × ℂ} (hz : z.1.re < 1) :
    DifferentiableAt ℝ initialCartesianPoint z := by
  unfold initialCartesianPoint
  have hd : 1 - z.1.re ≠ 0 := (sub_pos.mpr hz).ne'
  fun_prop (disch := exact hd)

/-- The initial Cartesian chart has a derivative at every point of the
sphere fiber, since the fiber avoids the pole. -/
theorem hasFDerivAt_initialCartesianPoint_of_mem {P Q : ℕ} (hP : 0 < P) (hQ : 0 < Q)
    {phase : Circle} {z : ℂ × ℂ} (hz : z ∈ poweredSphereCore P Q phase) :
    HasFDerivAt initialCartesianPoint (fderiv ℝ initialCartesianPoint z) z :=
  (differentiableAt_initialCartesianPoint (poweredSphereCore_re_lt_one hP hQ hz)).hasFDerivAt

/-- The physical core circle on the initial slice, parametrized by the
real line through the circle exponential. -/
noncomputable def poweredPhysicalCoreExp (p q : ℕ) (phase : Circle) (θ : ℝ) : Space :=
  poweredPhysicalCoreParam p q 0 phase (Circle.exp θ)

/-- On the initial slice the parametrized core is the stereographic
inverse of the sphere circle. -/
theorem poweredPhysicalCoreExp_eq (p q : ℕ) (phase : Circle) (θ : ℝ) :
    poweredPhysicalCoreExp p q phase θ =
      initialCartesianPoint (poweredCoreSphereExp p q phase θ) := by
  unfold poweredPhysicalCoreExp poweredPhysicalCoreParam poweredCoreSphereExp
  rw [batemanRay_zero]

/-- The actual velocity of the physical core circle: the differential of
the stereographic inverse applied to the winding tangent. -/
noncomputable def batemanCoreVelocity (p q : ℕ) (phase : Circle) (θ : ℝ) : Space :=
  fderiv ℝ initialCartesianPoint (poweredCoreSphereExp p q phase θ)
    (batemanCoreSphereTangent p q (poweredCoreSphereExp p q phase θ))

/-- The lifted physical core circle moves with the core velocity. -/
theorem hasDerivAt_poweredPhysicalCoreExp {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (phase : Circle) (θ : ℝ) :
    HasDerivAt (poweredPhysicalCoreExp p q phase) (batemanCoreVelocity p q phase θ) θ := by
  have hI := hasFDerivAt_initialCartesianPoint_of_mem hp hq
    (poweredCoreSphereExp_mem hp hq hpq phase θ)
  have hfun : (poweredPhysicalCoreExp p q phase) =
      fun u => initialCartesianPoint (poweredCoreSphereExp p q phase u) :=
    funext (poweredPhysicalCoreExp_eq p q phase)
  rw [hfun]
  exact hI.comp_hasDerivAt θ (hasDerivAt_poweredCoreSphereExp hp hq phase θ)

/-- Taking the initial Bateman coordinates of the lifted core circle
returns the sphere circle. -/
theorem batemanPairAt_poweredPhysicalCoreExp {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (phase : Circle) (θ : ℝ) :
    batemanPairAt 0 (poweredPhysicalCoreExp p q phase θ) =
      poweredCoreSphereExp p q phase θ := by
  have hzero (s : Space) : initialBatemanPair s = batemanPairAt 0 s := by
    simpa only [batemanRay_zero] using (batemanPairAt_batemanRay 0 s).symm
  rw [poweredPhysicalCoreExp_eq p q phase θ, ← hzero]
  refine initialBatemanPair_initialCartesianPoint _ ?_ ?_
  · simpa only [poweredCoreSphereExp, Complex.normSq_eq_norm_sq] using
      (poweredCoreSphereExp_mem hp hq hpq phase θ).1
  · exact poweredSphereCore_re_lt_one hp hq (poweredCoreSphereExp_mem hp hq hpq phase θ)

/-- The differential of the initial Bateman chart carries the core
velocity to the winding tangent of the sphere circle. -/
theorem fderiv_batemanPairAt_zero_coreVelocity {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (phase : Circle) (θ : ℝ) :
    fderiv ℝ (batemanPairAt 0) (poweredPhysicalCoreExp p q phase θ)
      (batemanCoreVelocity p q phase θ) =
      batemanCoreSphereTangent p q (poweredCoreSphereExp p q phase θ) := by
  have hsmooth : ContDiff ℝ ⊤ (batemanPairAt 0) := by
    have h := (contDiff_batemanAlphaPower 1 0).prodMk (contDiff_batemanBetaPower 1 0)
    simpa only [batemanAlphaPower, batemanBetaPower, pow_one, Prod.mk.eta] using h
  have hcomp : HasDerivAt (fun u => batemanPairAt 0 (poweredPhysicalCoreExp p q phase u))
      (fderiv ℝ (batemanPairAt 0) (poweredPhysicalCoreExp p q phase θ)
        (batemanCoreVelocity p q phase θ)) θ :=
    ((hsmooth.differentiable (by simp)
      (poweredPhysicalCoreExp p q phase θ)).hasFDerivAt.comp_hasDerivAt θ
      (hasDerivAt_poweredPhysicalCoreExp hp hq hpq phase θ))
  have hid : (fun u => batemanPairAt 0 (poweredPhysicalCoreExp p q phase u)) =
      poweredCoreSphereExp p q phase :=
    funext fun u => batemanPairAt_poweredPhysicalCoreExp hp hq hpq phase u
  rw [hid] at hcomp
  exact (hcomp.deriv).symm.trans (hasDerivAt_poweredCoreSphereExp hp hq phase θ).deriv

/-- The initial Bateman chart followed by its Cartesian inverse is the
identity on the whole initial physical slice. -/
theorem initialCartesianPoint_batemanPairAt_zero (s : Space) :
    initialCartesianPoint (batemanPairAt 0 s) = s := by
  have h := initialCartesianPoint_batemanPairAt_batemanRay 0 s
  rw [batemanRay_zero] at h
  exact h

/-- The differential of the initial Bateman chart is injective at every
point of the initial slice, being a factor of the identity. -/
theorem fderiv_batemanPairAt_zero_injective (s : Space) :
    Function.Injective (fderiv ℝ (batemanPairAt 0) s) := by
  have hfun : (fun u => initialCartesianPoint (batemanPairAt 0 u)) = id :=
    funext initialCartesianPoint_batemanPairAt_zero
  have hid : HasFDerivAt (fun u => initialCartesianPoint (batemanPairAt 0 u))
      (ContinuousLinearMap.id ℝ Space) s := by
    rw [hfun]
    exact hasFDerivAt_id s
  have hidf : fderiv ℝ (fun u => initialCartesianPoint (batemanPairAt 0 u)) s =
      ContinuousLinearMap.id ℝ Space := hid.fderiv
  have hχ : HasFDerivAt (batemanPairAt 0) (fderiv ℝ (batemanPairAt 0) s) s := by
    have hsmooth : ContDiff ℝ ⊤ (batemanPairAt 0) := by
      have h := (contDiff_batemanAlphaPower 1 0).prodMk (contDiff_batemanBetaPower 1 0)
      simpa only [batemanAlphaPower, batemanBetaPower, pow_one, Prod.mk.eta] using h
    exact ((hsmooth.differentiable (by simp)) s).hasFDerivAt
  have hι : HasFDerivAt initialCartesianPoint
      (fderiv ℝ initialCartesianPoint (batemanPairAt 0 s)) (batemanPairAt 0 s) :=
    (differentiableAt_initialCartesianPoint (rationalAlpha_re_lt_one s.1 s.2.1 s.2.2 0)).hasFDerivAt
  have hsplit : fderiv ℝ (fun u => initialCartesianPoint (batemanPairAt 0 u)) s =
      (fderiv ℝ initialCartesianPoint (batemanPairAt 0 s)).comp (fderiv ℝ (batemanPairAt 0) s) :=
    (hι.comp s hχ).fderiv
  rw [hidf] at hsplit
  intro u₁ u₂ h
  have key (u : Space) : u =
      fderiv ℝ initialCartesianPoint (batemanPairAt 0 s) (fderiv ℝ (batemanPairAt 0) s u) := by
    have hthis := congrArg (fun L : Space →L[ℝ] Space => L u) hsplit
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_id',
      ContinuousLinearMap.id_apply] using hthis
  have k1 := key u₁
  have k2 := key u₂
  rw [h] at k1
  exact k1.trans k2.symm

/-- The core velocity of the physical core circle never vanishes. -/
theorem batemanCoreVelocity_ne_zero {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (phase : Circle) (θ : ℝ) :
    batemanCoreVelocity p q phase θ ≠ 0 := by
  intro h
  have h1 : batemanCoreSphereTangent p q (poweredCoreSphereExp p q phase θ) = 0 := by
    rw [← fderiv_batemanPairAt_zero_coreVelocity hp hq hpq phase θ, h, map_zero]
  exact batemanCoreSphereTangent_ne_zero hp hq (poweredCoreSphereExp_mem hp hq hpq phase θ) h1

/-- The signed constant factor of the physical magnetic rate on a real
phase core. -/
noncomputable def batemanCoreMagneticFactor (P Q : ℕ) (phase : Circle) : ℝ :=
  -(((P : ℝ) + Q) * poweredPeakAmplitude P Q * (phase : ℂ).re)

/-- The signed constant factor of the physical electric rate on a purely
imaginary phase core. -/
noncomputable def batemanCoreElectricFactor (P Q : ℕ) (phase : Circle) : ℝ :=
  ((P : ℝ) + Q) * poweredPeakAmplitude P Q * (phase : ℂ).im

/-- On a real phase core the complex sphere rate is the real magnetic
factor. -/
theorem batemanCorePhaseRate_of_im_zero {P Q : ℕ} {phase : Circle}
    (hphase : (phase : ℂ).im = 0) :
    batemanCorePhaseRate P Q phase = (batemanCoreMagneticFactor P Q phase : ℂ) := by
  have hconj : conj (phase : ℂ) = ((phase : ℂ).re : ℂ) := by
    apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im, hphase]
  unfold batemanCorePhaseRate batemanCoreMagneticFactor
  push_cast [hconj]
  ring

/-- On a purely imaginary phase core minus the imaginary unit times the
complex sphere rate is the real electric factor. -/
theorem neg_im_mul_batemanCorePhaseRate_of_re_zero {P Q : ℕ} {phase : Circle}
    (hphase : (phase : ℂ).re = 0) :
    -Complex.I * batemanCorePhaseRate P Q phase = (batemanCoreElectricFactor P Q phase : ℂ) := by
  have him : (phase : ℂ).im ≠ 0 := by
    intro h
    have hn := Circle.normSq_coe phase
    rw [Complex.normSq_apply, hphase, h] at hn
    norm_num at hn
  have hconj : conj (phase : ℂ) = -(((phase : ℂ).im : ℂ)) * Complex.I := by
    apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im, hphase]
  unfold batemanCorePhaseRate batemanCoreElectricFactor
  rw [hconj]
  push_cast
  linear_combination
    (-((P : ℂ) + Q) * (poweredPeakAmplitude P Q : ℂ) * ((phase : ℂ).im : ℂ)) *
      Complex.I_mul_I

/-- A real scalar acting on a complex pair acts through its cast. -/
theorem real_smul_eq_complex_smul (k : ℝ) (t : ℂ × ℂ) : k • t = (k : ℂ) • t := by
  apply Prod.ext <;> simp [Complex.real_smul]

/-- The membership of a component core circle in the fiber of the full
phase: raising the reduced product label to the `d`-th power gives the
label of the scaled exponents. -/
theorem poweredCoreSphereExp_mul_mem {p q d : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (hd : 0 < d) {phase ζ : Circle} (hζ : ζ ^ d = phase) (θ : ℝ) :
    poweredCoreSphereExp p q ζ θ ∈ poweredSphereCore (p * d) (q * d) phase := by
  obtain ⟨h1, h2⟩ := poweredCoreSphereExp_mem hp hq hpq ζ θ
  refine ⟨h1, ?_⟩
  have hsplit : ∀ A B : ℂ, A ^ (p * d) * B ^ (q * d) = (A ^ p * B ^ q) ^ d := by
    intro A B
    rw [mul_pow, pow_mul, pow_mul]
  rw [hsplit, h2, mul_pow, ← Complex.ofReal_pow,
    ← poweredPeakAmplitude_mul_exponents hp hq hd, ← Circle.coe_pow, hζ]

/-- **The main magnetic bridge.** Along a component core circle, the
actual magnetic vector with scaled exponents on the initial slice is a
real multiple of the actual core velocity, the factor being the
stereographic scale cubed times a nowhere-zero signed constant. No
closed-orbit statement enters the hypotheses. -/
theorem batemanMagneticVector_coreExp_eq {p q d : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (hd : 0 < d) {phase ζ : Circle} (hζ : ζ ^ d = phase)
    (hphase : (phase : ℂ).im = 0) (θ : ℝ) :
    batemanMagneticVector (p * d) (q * d) 0 (poweredPhysicalCoreExp p q ζ θ) =
      (batemanStereoScale (poweredPhysicalCoreExp p q ζ θ) ^ 3 *
        (d * batemanCoreMagneticFactor (p * d) (q * d) phase)) •
        batemanCoreVelocity p q ζ θ := by
  have hchart : batemanPairAt 0 (poweredPhysicalCoreExp p q ζ θ) =
      poweredCoreSphereExp p q ζ θ :=
    batemanPairAt_poweredPhysicalCoreExp hp hq hpq ζ θ
  have hmem := poweredCoreSphereExp_mul_mem hp hq hpq hd hζ θ
  obtain ⟨-, hB⟩ := fderiv_batemanPairAt_initial_fields (p * d) (q * d)
    (poweredPhysicalCoreExp p q ζ θ)
  rw [hchart] at hB
  have hfib := batemanSphereMagnetic_fiber_eq (Nat.mul_pos hp hd) (Nat.mul_pos hq hd) hmem
  have hrate : batemanCorePhaseRate (p * d) (q * d) phase =
      (batemanCoreMagneticFactor (p * d) (q * d) phase : ℂ) :=
    batemanCorePhaseRate_of_im_zero hphase
  have htan : batemanCoreSphereTangent (p * d) (q * d) (poweredCoreSphereExp p q ζ θ) =
      ((d : ℝ) : ℂ) • batemanCoreSphereTangent p q (poweredCoreSphereExp p q ζ θ) := by
    rw [batemanCoreSphereTangent_mul_exponents]
    push_cast
    rfl
  have hLB : fderiv ℝ (batemanPairAt 0) (poweredPhysicalCoreExp p q ζ θ)
      (batemanMagneticVector (p * d) (q * d) 0 (poweredPhysicalCoreExp p q ζ θ)) =
      ((((batemanStereoScale (poweredPhysicalCoreExp p q ζ θ) ^ 3 *
        (d * batemanCoreMagneticFactor (p * d) (q * d) phase) : ℝ) : ℂ))) •
      batemanCoreSphereTangent p q (poweredCoreSphereExp p q ζ θ) := by
    rw [hB, hfib, hrate, htan, real_smul_eq_complex_smul, smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  have hRB : fderiv ℝ (batemanPairAt 0) (poweredPhysicalCoreExp p q ζ θ)
      ((batemanStereoScale (poweredPhysicalCoreExp p q ζ θ) ^ 3 *
        (d * batemanCoreMagneticFactor (p * d) (q * d) phase)) •
        batemanCoreVelocity p q ζ θ) =
      ((((batemanStereoScale (poweredPhysicalCoreExp p q ζ θ) ^ 3 *
        (d * batemanCoreMagneticFactor (p * d) (q * d) phase) : ℝ) : ℂ))) •
      batemanCoreSphereTangent p q (poweredCoreSphereExp p q ζ θ) := by
    rw [map_smul, fderiv_batemanPairAt_zero_coreVelocity hp hq hpq ζ θ,
      real_smul_eq_complex_smul]
  exact fderiv_batemanPairAt_zero_injective _ (hLB.trans hRB.symm)

/-- **The main electric bridge.** Along a component core circle, the
actual electric vector with scaled exponents on the initial slice is a
real multiple of the actual core velocity, with its own signed
constant. -/
theorem batemanElectricVector_coreExp_eq {p q d : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (hd : 0 < d) {phase ζ : Circle} (hζ : ζ ^ d = phase)
    (hphase : (phase : ℂ).re = 0) (θ : ℝ) :
    batemanElectricVector (p * d) (q * d) 0 (poweredPhysicalCoreExp p q ζ θ) =
      (batemanStereoScale (poweredPhysicalCoreExp p q ζ θ) ^ 3 *
        (d * batemanCoreElectricFactor (p * d) (q * d) phase)) •
        batemanCoreVelocity p q ζ θ := by
  have hchart : batemanPairAt 0 (poweredPhysicalCoreExp p q ζ θ) =
      poweredCoreSphereExp p q ζ θ :=
    batemanPairAt_poweredPhysicalCoreExp hp hq hpq ζ θ
  have hmem := poweredCoreSphereExp_mul_mem hp hq hpq hd hζ θ
  obtain ⟨hE, -⟩ := fderiv_batemanPairAt_initial_fields (p * d) (q * d)
    (poweredPhysicalCoreExp p q ζ θ)
  rw [hchart] at hE
  have hfib := batemanSphereElectric_fiber_eq (Nat.mul_pos hp hd) (Nat.mul_pos hq hd) hmem
  have hrate : -Complex.I * batemanCorePhaseRate (p * d) (q * d) phase =
      (batemanCoreElectricFactor (p * d) (q * d) phase : ℂ) :=
    neg_im_mul_batemanCorePhaseRate_of_re_zero hphase
  have htan : batemanCoreSphereTangent (p * d) (q * d) (poweredCoreSphereExp p q ζ θ) =
      ((d : ℝ) : ℂ) • batemanCoreSphereTangent p q (poweredCoreSphereExp p q ζ θ) := by
    rw [batemanCoreSphereTangent_mul_exponents]
    push_cast
    rfl
  have hLB : fderiv ℝ (batemanPairAt 0) (poweredPhysicalCoreExp p q ζ θ)
      (batemanElectricVector (p * d) (q * d) 0 (poweredPhysicalCoreExp p q ζ θ)) =
      ((((batemanStereoScale (poweredPhysicalCoreExp p q ζ θ) ^ 3 *
        (d * batemanCoreElectricFactor (p * d) (q * d) phase) : ℝ) : ℂ))) •
      batemanCoreSphereTangent p q (poweredCoreSphereExp p q ζ θ) := by
    rw [hE, hfib, hrate, htan, real_smul_eq_complex_smul, smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  have hRB : fderiv ℝ (batemanPairAt 0) (poweredPhysicalCoreExp p q ζ θ)
      ((batemanStereoScale (poweredPhysicalCoreExp p q ζ θ) ^ 3 *
        (d * batemanCoreElectricFactor (p * d) (q * d) phase)) •
        batemanCoreVelocity p q ζ θ) =
      ((((batemanStereoScale (poweredPhysicalCoreExp p q ζ θ) ^ 3 *
        (d * batemanCoreElectricFactor (p * d) (q * d) phase) : ℝ) : ℂ))) •
      batemanCoreSphereTangent p q (poweredCoreSphereExp p q ζ θ) := by
    rw [map_smul, fderiv_batemanPairAt_zero_coreVelocity hp hq hpq ζ θ,
      real_smul_eq_complex_smul]
  exact fderiv_batemanPairAt_zero_injective _ (hLB.trans hRB.symm)

/-- A unit phase with vanishing imaginary part has real part of
absolute value one. -/
theorem abs_re_eq_one_of_im_zero {phase : Circle} (hphase : (phase : ℂ).im = 0) :
    |(phase : ℂ).re| = 1 := by
  have hn : (phase : ℂ).re * (phase : ℂ).re = 1 := by
    have h := Circle.normSq_coe phase
    rw [Complex.normSq_apply, hphase, mul_zero, add_zero] at h
    exact h
  have h2 : |(phase : ℂ).re| ^ 2 = 1 := by
    rw [pow_two, ← abs_mul, hn, abs_of_pos zero_lt_one]
  rcases sq_eq_one_iff.mp h2 with h3 | h3
  · exact h3
  · exact absurd (abs_nonneg ((phase : ℂ).re)) (by rw [h3]; norm_num)

/-- A unit phase with vanishing real part has imaginary part of
absolute value one. -/
theorem abs_im_eq_one_of_re_zero {phase : Circle} (hphase : (phase : ℂ).re = 0) :
    |(phase : ℂ).im| = 1 := by
  have hn : (phase : ℂ).im * (phase : ℂ).im = 1 := by
    have h := Circle.normSq_coe phase
    rw [Complex.normSq_apply, hphase, mul_zero, zero_add] at h
    exact h
  have h2 : |(phase : ℂ).im| ^ 2 = 1 := by
    rw [pow_two, ← abs_mul, hn, abs_of_pos zero_lt_one]
  rcases sq_eq_one_iff.mp h2 with h3 | h3
  · exact h3
  · exact absurd (abs_nonneg ((phase : ℂ).im)) (by rw [h3]; norm_num)

/-- The signed magnetic factor never vanishes on a real phase core. -/
theorem batemanCoreMagneticFactor_ne_zero {P Q : ℕ} (hP : 0 < P) (hQ : 0 < Q) {phase : Circle}
    (hphase : (phase : ℂ).im = 0) : batemanCoreMagneticFactor P Q phase ≠ 0 := by
  have habs : |(phase : ℂ).re| = 1 := abs_re_eq_one_of_im_zero hphase
  have hre : (phase : ℂ).re ≠ 0 := by
    intro h
    rw [h, abs_zero] at habs
    exact one_ne_zero habs.symm
  unfold batemanCoreMagneticFactor
  intro h
  rw [neg_eq_zero] at h
  have hsum : ((P : ℝ) + Q) ≠ 0 := by exact_mod_cast (add_pos hP hQ).ne'
  have hL : ((P : ℝ) + Q) * poweredPeakAmplitude P Q ≠ 0 := by
    intro hc
    rcases mul_eq_zero.mp hc with hc' | hc'
    · exact hsum hc'
    · exact (poweredPeakAmplitude_pos hP hQ).ne' hc'
  exact hre ((mul_eq_zero.mp h).resolve_left hL)

/-- The signed electric factor never vanishes on an imaginary phase
core. -/
theorem batemanCoreElectricFactor_ne_zero {P Q : ℕ} (hP : 0 < P) (hQ : 0 < Q) {phase : Circle}
    (hphase : (phase : ℂ).re = 0) : batemanCoreElectricFactor P Q phase ≠ 0 := by
  have habs : |(phase : ℂ).im| = 1 := abs_im_eq_one_of_re_zero hphase
  have him : (phase : ℂ).im ≠ 0 := by
    intro h
    rw [h, abs_zero] at habs
    exact one_ne_zero habs.symm
  unfold batemanCoreElectricFactor
  intro h
  have hsum : ((P : ℝ) + Q) ≠ 0 := by exact_mod_cast (add_pos hP hQ).ne'
  have hL : ((P : ℝ) + Q) * poweredPeakAmplitude P Q ≠ 0 := by
    intro hc
    rcases mul_eq_zero.mp hc with hc' | hc'
    · exact hsum hc'
    · exact (poweredPeakAmplitude_pos hP hQ).ne' hc'
  exact him ((mul_eq_zero.mp h).resolve_left hL)

/-- The lifted physical core circle is continuous. -/
theorem continuous_poweredPhysicalCoreExp {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (phase : Circle) :
    Continuous (poweredPhysicalCoreExp p q phase) := by
  have hc : Continuous (poweredCoreSphereExp p q phase) :=
    (continuous_poweredCoreSphereParam p q phase).comp Circle.exp.continuous
  have hd : Continuous (fun θ => 1 - (poweredCoreSphereExp p q phase θ).1.re) :=
    continuous_const.sub (Complex.continuous_re.comp hc.fst)
  have hne (θ : ℝ) : 1 - (poweredCoreSphereExp p q phase θ).1.re ≠ 0 :=
    (sub_pos.mpr (poweredSphereCore_re_lt_one hp hq
      (poweredCoreSphereExp_mem hp hq hpq phase θ))).ne'
  rw [funext fun θ => poweredPhysicalCoreExp_eq p q phase θ]
  exact (((Complex.continuous_re.comp hc.snd).div hd hne).prodMk
    (((Complex.continuous_im.comp hc.snd).neg.div hd hne).prodMk
      ((Complex.continuous_im.comp hc.fst).div hd hne)))

/-- The lifted physical core circle is periodic with the full circle
period. -/
theorem periodic_poweredPhysicalCoreExp (p q : ℕ) (phase : Circle) :
    Function.Periodic (poweredPhysicalCoreExp p q phase) (2 * Real.pi) :=
  fun θ => by
  simp only [poweredPhysicalCoreExp, Circle.periodic_exp θ]

/-- The lifted physical core circle is injective on each half-open lap
of length the full circle period. -/
theorem injOn_poweredPhysicalCoreExp {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (phase : Circle) :
    Set.InjOn (poweredPhysicalCoreExp p q phase) (Set.Ico 0 (2 * Real.pi)) := by
  intro a ha b hb hab
  have hinj := (poweredPhysicalCoreParam_bijective hp hq hpq 0 phase).1
  have hc : Circle.exp a = Circle.exp b := hinj hab
  exact Circle.exp_injOn_Ico (sub_zero (2 * Real.pi)).le ha hb hc

end Qatlib.Papers.KnotLight13.TorusFamily
