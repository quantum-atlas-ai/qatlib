/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.CayleyBudget

/-!
# A finite dyadic coefficient adapter from spin and derivative samples

The source returns rational coordinates, without a unit or tangency test on
those approximations. Imaginary projection implements the cross product.
The source precision is selected by integer ceil-log, not real comparison.
-/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Abbreviation for Rational Spin Sample in the Hopf Atlas construction. -/
abbrev RationalSpinSample := (Fin 3 → ℚ) × (Fin 3 → ℚ)

/-- Definition of rational Spin Quaternion in the Hopf Atlas construction. -/
def rationalSpinQuaternion (s : Fin 3 → ℚ) : Quaternion ℚ := ⟨0,s 0,s 1,s 2⟩

/-- Definition of nearest Dyadic Numerator in the Hopf Atlas construction. -/
def nearestDyadicNumerator (a : ℚ) (p : ℕ) : ℤ := Int.floor (a*(2^p : ℚ)+1/2)

/-- Definition of spin Coefficient Overhead in the Hopf Atlas construction. -/
def spinCoefficientOverhead (M : ℚ) : ℕ := Nat.clog 2 (Nat.ceil (16*(M+2)))

/-- Definition of coefficient Source Query in the Hopf Atlas construction. -/
def coefficientSourceQuery (M : ℚ) (label : ℚ × ℕ) : ℚ × ℕ :=
  (label.1,label.2+spinCoefficientOverhead M)

/-- Definition of rational Horizontal Sample in the Hopf Atlas construction. -/
def rationalHorizontalSample (a : RationalSpinSample) : Quaternion ℚ :=
  (-1/2 : ℚ) • (rationalSpinQuaternion a.1*rationalSpinQuaternion a.2).im

/-- Definition of rounded Horizontal Sample in the Hopf Atlas construction. -/
def roundedHorizontalSample (a : RationalSpinSample) (p : ℕ) : Fin 3 → ℤ :=
  let k := rationalHorizontalSample a
  fun j => nearestDyadicNumerator (![k.imI,k.imJ,k.imK] j) p

/-- Definition of spin Coefficient Oracle in the Hopf Atlas construction. -/
def spinCoefficientOracle (M : ℚ) (source : ℚ × ℕ → RationalSpinSample) (label : ℚ × ℕ) : Fin 3 → ℤ :=
  roundedHorizontalSample (source (coefficientSourceQuery M label)) label.2

/-- Original `nearestDyadicNumerator_error` guarantee for the `SpinCoefficient` construction; the complete source hypotheses are retained. -/
theorem nearestDyadicNumerator_error (a : ℚ) (p : ℕ) :
    |(nearestDyadicNumerator a p : ℚ)/(2^p : ℚ)-a| ≤ (2^p : ℚ)⁻¹/2 := by
  have hp : (0 : ℚ)<2^p := by positivity
  have hlo := Int.floor_le (a*(2^p : ℚ)+1/2)
  have hhi := Int.lt_floor_add_one (a*(2^p : ℚ)+1/2)
  have hd : (nearestDyadicNumerator a p : ℚ)/(2^p : ℚ)-a=
      ((nearestDyadicNumerator a p : ℚ)-a*(2^p : ℚ))/(2^p : ℚ) := by field_simp
  rw [hd,abs_div,abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  have hc : ((2^p : ℚ)⁻¹/2)*(2^p : ℚ)=1/2 := by field_simp
  rw [hc]
  apply abs_le.mpr
  dsimp [nearestDyadicNumerator]
  constructor <;> linarith

/-- Original `spinCoefficientOverhead_bound` guarantee for the `SpinCoefficient` construction; the complete source hypotheses are retained. -/
theorem spinCoefficientOverhead_bound (M : ℚ) (hM : 0 ≤ M) (p : ℕ) :
    2*(2^(p+spinCoefficientOverhead M) : ℚ)⁻¹ ≤ (2^p : ℚ)⁻¹/(8*(M+2)) := by
  have hpow : Nat.ceil (16*(M+2)) ≤ 2^spinCoefficientOverhead M := Nat.le_pow_clog (by decide) _
  have hm : 16*(M+2) ≤ (2^spinCoefficientOverhead M : ℚ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hpow)
  have hp : (0 : ℚ)<2^p := by positivity
  have ho : (0 : ℚ)<2^spinCoefficientOverhead M := by positivity
  have hd : (0 : ℚ)<8*(M+2) := by positivity
  rw [pow_add,mul_inv_rev]
  apply (le_div_iff₀ hd).mpr
  field_simp [hp.ne',ho.ne']
  nlinarith

noncomputable section
open scoped Quaternion RealInnerProductSpace

/-- Definition of rational Quaternion Cast in the Hopf Atlas construction. -/
def rationalQuaternionCast : Quaternion ℚ →+* ℍ where
  toFun q := ⟨(q.re : ℝ),(q.imI : ℝ),(q.imJ : ℝ),(q.imK : ℝ)⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp [sub_eq_add_neg]

/-- Original `quaternion_im_norm_le` guarantee for the `SpinCoefficient` construction; the complete source hypotheses are retained. -/
theorem quaternion_im_norm_le (q : ℍ) : ‖q.im‖ ≤ ‖q‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [pow_two,← Quaternion.normSq_eq_norm_mul_self,Quaternion.normSq_def']
  simp only [Quaternion.re_im,Quaternion.imI_im,Quaternion.imJ_im,Quaternion.imK_im,zero_mul,zero_add]
  nlinarith [sq_nonneg q.re]

/-- Seven quarters exceeds sqrt(3); retaining this slack allows rounding plus
source error to fit in the requested dyadic Euclidean tolerance. -/
theorem pure_coordinate_norm_le (q : ℍ) (hq : q.re=0) (eta : ℝ) (he : 0 ≤ eta)
    (hi : |q.imI| ≤ eta) (hj : |q.imJ| ≤ eta) (hk : |q.imK| ≤ eta) : ‖q‖ ≤ 7*eta/4 := by
  have hi2 : q.imI^2 ≤ eta^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) he).mpr hi
  have hj2 : q.imJ^2 ≤ eta^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) he).mpr hj
  have hk2 : q.imK^2 ≤ eta^2 := by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) he).mpr hk
  have hn : ‖q‖^2=q.imI^2+q.imJ^2+q.imK^2 := by
    rw [pow_two,← Quaternion.normSq_eq_norm_mul_self,Quaternion.normSq_def',hq]
    ring
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  nlinarith [sq_nonneg eta]

/-- Original `rationalHorizontalSample_cast` guarantee for the `SpinCoefficient` construction; the complete source hypotheses are retained. -/
theorem rationalHorizontalSample_cast (a : RationalSpinSample) :
    rationalQuaternionCast (rationalHorizontalSample a)=
      (horizontalCoefficient (rationalQuaternionCast (rationalSpinQuaternion a.1))
        (rationalQuaternionCast (rationalSpinQuaternion a.2))).im := by
  ext <;> simp [rationalHorizontalSample,rationalQuaternionCast,horizontalCoefficient,sub_eq_add_neg]

/-- Original `dyadic_rounding_error` guarantee for the `SpinCoefficient` construction; the complete source hypotheses are retained. -/
theorem dyadic_rounding_error (a : Quaternion ℚ) (ha : a.re=0) (p : ℕ) :
    ‖dyadicCoefficient p (fun j => nearestDyadicNumerator (![a.imI,a.imJ,a.imK] j) p)-
      rationalQuaternionCast a‖ ≤ 7*(2^p : ℝ)⁻¹/8 := by
  have hround (r : ℚ) : |((nearestDyadicNumerator r p : ℤ) : ℝ)/(2^p : ℝ)-(r : ℝ)| ≤ (2^p : ℝ)⁻¹/2 := by
    have h : ((|(nearestDyadicNumerator r p : ℚ)/(2^p : ℚ)-r| : ℚ) : ℝ) ≤ (((2^p : ℚ)⁻¹/2 : ℚ) : ℝ) :=
      Rat.cast_le.mpr (nearestDyadicNumerator_error r p)
    push_cast at h
    exact h
  have h := pure_coordinate_norm_le
    (dyadicCoefficient p (fun j => nearestDyadicNumerator (![a.imI,a.imJ,a.imK] j) p)-rationalQuaternionCast a)
    (by simp [dyadicCoefficient,rationalQuaternionCast,ha]) ((2^p : ℝ)⁻¹/2) (by positivity)
    (by simpa [dyadicCoefficient,rationalQuaternionCast,div_eq_mul_inv,mul_comm] using hround a.imI)
    (by simpa [dyadicCoefficient,rationalQuaternionCast,div_eq_mul_inv,mul_comm] using hround a.imJ)
    (by simpa [dyadicCoefficient,rationalQuaternionCast,div_eq_mul_inv,mul_comm] using hround a.imK)
  linarith

/-- Original `horizontal_sample_error` guarantee for the `SpinCoefficient` construction; the complete source hypotheses are retained. -/
theorem horizontal_sample_error (a d s ds : ℍ) (hs : ‖s‖=1)
    (hp : (horizontalCoefficient s ds).re=0) (eta M : ℝ) (he : 0 ≤ eta) (he1 : eta ≤ 1)
    (hd : ‖ds‖ ≤ M) (ha : ‖a-s‖ ≤ eta) (hda : ‖d-ds‖ ≤ eta) :
    ‖(horizontalCoefficient a d).im-horizontalCoefficient s ds‖ ≤ eta*(M+2) := by
  have han : ‖a‖ ≤ 1+eta := by
    have h := (norm_le_norm_sub_add a s).trans (add_le_add ha hs.le)
    linarith
  have hprod : ‖a*d-s*ds‖ ≤ eta*(M+2) := by
    have hid : a*d-s*ds=(a-s)*ds+a*(d-ds) := by noncomm_ring
    calc
      _ ≤ ‖(a-s)*ds‖+‖a*(d-ds)‖ := by rw [hid]; exact norm_add_le _ _
      _ = ‖a-s‖*‖ds‖+‖a‖*‖d-ds‖ := by rw [norm_mul,norm_mul]
      _ ≤ eta*M+(1+eta)*eta := add_le_add
        (mul_le_mul ha hd (norm_nonneg _) he)
        (mul_le_mul han hda (norm_nonneg _) (by positivity))
      _ ≤ eta*(M+2) := by nlinarith
  have him : (horizontalCoefficient s ds).im=horizontalCoefficient s ds := by
    ext <;> simp [hp]
  calc
    _ = ‖(horizontalCoefficient a d-horizontalCoefficient s ds).im‖ := by rw [Quaternion.im_sub,him]
    _ ≤ ‖horizontalCoefficient a d-horizontalCoefficient s ds‖ := quaternion_im_norm_le _
    _ = (1/2 : ℝ)*‖a*d-s*ds‖ := by
      rw [horizontalCoefficient,horizontalCoefficient,← smul_sub,norm_smul]
      norm_num
    _ ≤ eta*(M+2) := by nlinarith [norm_nonneg (a*d-s*ds)]

/-- Only coordinate accuracy of the source spin and its derivative is assumed.
No exact tangency or unit identity is imposed on rational approximations. -/
theorem spinCoefficientOracle_error (M : ℚ) (hM : 0 ≤ M)
    (source : ℚ × ℕ → RationalSpinSample) (t : ℚ) (p : ℕ) (s ds : ℍ)
    (hsre : s.re=0) (hdsre : ds.re=0) (hs : ‖s‖=1) (hd : ‖ds‖ ≤ (M : ℝ))
    (hp : (horizontalCoefficient s ds).re=0)
    (ha : ∀ j, |((source (coefficientSourceQuery M (t,p))).1 j : ℝ)-(![s.imI,s.imJ,s.imK] j)| ≤
      (2^(p+spinCoefficientOverhead M) : ℝ)⁻¹)
    (hda : ∀ j, |((source (coefficientSourceQuery M (t,p))).2 j : ℝ)-(![ds.imI,ds.imJ,ds.imK] j)| ≤
      (2^(p+spinCoefficientOverhead M) : ℝ)⁻¹) :
    ‖dyadicCoefficient p (spinCoefficientOracle M source (t,p))-horizontalCoefficient s ds‖ ≤ (2^p : ℝ)⁻¹ := by
  let a := source (coefficientSourceQuery M (t,p))
  let e : ℝ := (2^p : ℝ)⁻¹
  let eta : ℝ := 2*(2^(p+spinCoefficientOverhead M) : ℝ)⁻¹
  have hM' : (0 : ℝ) ≤ M := by exact_mod_cast hM
  have he : 0 ≤ eta := by positivity
  have heps : e ≤ 1 := by
    apply (inv_le_one₀ (by positivity)).mpr
    exact one_le_pow₀ (by norm_num)
  have hpre : eta ≤ e/(8*((M : ℝ)+2)) := by
    have h : ((2*(2^(p+spinCoefficientOverhead M) : ℚ)⁻¹ : ℚ) : ℝ) ≤
        (((2^p : ℚ)⁻¹/(8*(M+2)) : ℚ) : ℝ) := Rat.cast_le.mpr (spinCoefficientOverhead_bound M hM p)
    push_cast at h
    exact h
  have hsmall : eta*((M : ℝ)+2) ≤ e/8 := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ)<8*((M : ℝ)+2))).mp hpre
    nlinarith
  have he1 : eta ≤ 1 := by nlinarith [mul_nonneg he hM']
  have ha' : ‖rationalQuaternionCast (rationalSpinQuaternion a.1)-s‖ ≤ eta := by
    have h := pure_coordinate_norm_le (rationalQuaternionCast (rationalSpinQuaternion a.1)-s)
      (by simp [rationalQuaternionCast,rationalSpinQuaternion,hsre])
      ((2^(p+spinCoefficientOverhead M) : ℝ)⁻¹) (by positivity) (ha 0) (ha 1) (ha 2)
    change ‖rationalQuaternionCast (rationalSpinQuaternion a.1)-s‖ ≤ _ at h
    dsimp [eta]
    linarith
  have hda' : ‖rationalQuaternionCast (rationalSpinQuaternion a.2)-ds‖ ≤ eta := by
    have h := pure_coordinate_norm_le (rationalQuaternionCast (rationalSpinQuaternion a.2)-ds)
      (by simp [rationalQuaternionCast,rationalSpinQuaternion,hdsre])
      ((2^(p+spinCoefficientOverhead M) : ℝ)⁻¹) (by positivity) (hda 0) (hda 1) (hda 2)
    change ‖rationalQuaternionCast (rationalSpinQuaternion a.2)-ds‖ ≤ _ at h
    dsimp [eta]
    linarith
  have hm := horizontal_sample_error _ _ s ds hs hp eta (M : ℝ) he he1 hd ha' hda'
  rw [← rationalHorizontalSample_cast] at hm
  have hr := dyadic_rounding_error (rationalHorizontalSample a) (by simp [rationalHorizontalSample]) p
  calc
    _ ≤ ‖dyadicCoefficient p (spinCoefficientOracle M source (t,p))-rationalQuaternionCast (rationalHorizontalSample a)‖+
        ‖rationalQuaternionCast (rationalHorizontalSample a)-horizontalCoefficient s ds‖ := by
      simpa only [dist_eq_norm] using dist_triangle
        (dyadicCoefficient p (spinCoefficientOracle M source (t,p)))
        (rationalQuaternionCast (rationalHorizontalSample a)) (horizontalCoefficient s ds)
    _ ≤ 7*e/8+eta*((M : ℝ)+2) := add_le_add hr hm
    _ ≤ e := by linarith

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
