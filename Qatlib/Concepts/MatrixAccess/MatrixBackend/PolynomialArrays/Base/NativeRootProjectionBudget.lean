/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootIntegerPolynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeSourceBitPrecision
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootIntegerList
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.FieldTheory.Separable

set_option backward.isDefEq.respectTransparency false

/-! Literal projection/Sturm proposer inclusion budget for CFD.
Actual integer coefficients supply derivative envelopes. The main consumer
uses a separable factor and covered real/imaginary intervals at the literal
cap; it does NOT prove Yun/Sturm generation, whole verifier acceptance,
interpreter refinement, fees, or full CFD G1--G4. Generic helpers stay private.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open Polynomial
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Gaussian
open Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput
open scoped BigOperators
/-! Private generation-side component. No source rootProjectionCap or Sturm completeness
is assumed proved here. The analytic premises are NOT acceptance predicates. -/
open Polynomial
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Gaussian

/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionInternal_integer_coordinate_complete` under the displayed hypotheses. -/
private theorem rootProjectionInternal_integer_coordinate_complete (n : ℕ) (v w : GaussianIntegerFraction) (r : ℚ)
    (hE : 0 < v.denominator) (hF : 0 < w.denominator)
    (h : (n : ℝ) * (|(gaussianPointValue v).re| + |(gaussianPointValue v).im|) ≤
      (r : ℝ) * max |(gaussianPointValue w).re| |(gaussianPointValue w).im|) :
    rootIntegerCoordinateBound n v w r := by
  have he : (0 : ℝ) < v.denominator := by exact_mod_cast hE
  have hf : (0 : ℝ) < w.denominator := by exact_mod_cast hF
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hr : (r.num : ℝ) / (r.den : ℝ) = (r : ℝ) := by exact_mod_cast r.num_div_den
  rw [rootIntegerValue_l1 v hE, rootIntegerValue_linf w hF, ← hr] at h
  have hdiv : ((n : ℝ) * (|(v.numerator.1 : ℝ)| + |(v.numerator.2 : ℝ)|)) /
      (v.denominator : ℝ) ≤
      ((r.num : ℝ) * max |(w.numerator.1 : ℝ)| |(w.numerator.2 : ℝ)|) /
        ((r.den : ℝ) * (w.denominator : ℝ)) := by
    convert h using 1 <;> ring
  have hraw := (div_le_div_iff₀ he (mul_pos hd hf)).mp hdiv
  have hraw' : (n : ℝ) * (|(v.numerator.1 : ℝ)| + |(v.numerator.2 : ℝ)|) *
      (w.denominator : ℝ) * (r.den : ℝ) ≤
      (r.num : ℝ) * max |(w.numerator.1 : ℝ)| |(w.numerator.2 : ℝ)| *
        (v.denominator : ℝ) := by nlinarith only [hraw]
  dsimp only [rootIntegerCoordinateBound]
  exact_mod_cast hraw'

/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionInternal_nearby_root_coordinate` under the displayed hypotheses. -/
private theorem rootProjectionInternal_nearby_root_coordinate (f : ℂ[X]) (z c : ℂ) (A M e r : ℝ)
    (hm : 0 < f.natDegree) (hA : 0 < A) (hM : 0 ≤ M) (he : 0 ≤ e)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hz : f.eval z = 0) (hc : ‖c-z‖ ≤ e)
    (hprime : A ≤ ‖f.derivative.eval z‖)
    (hfirst : ∀ w ∈ Metric.closedBall z e, ‖f.derivative.eval w‖ ≤ M)
    (hsecond : ∀ w ∈ Metric.closedBall z e, ‖f.derivative.derivative.eval w‖ ≤ M)
    (hbudget : 8 * (f.natDegree : ℝ) * M * e ≤ r * A) :
    (f.natDegree : ℝ) * (|(f.eval c).re| + |(f.eval c).im|) ≤
        r * max |(f.derivative.eval c).re| |(f.derivative.eval c).im| ∧
      0 < max |(f.derivative.eval c).re| |(f.derivative.eval c).im| := by
  have hzc : z ∈ Metric.closedBall z e := Metric.mem_closedBall_self he
  have hcc : c ∈ Metric.closedBall z e := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hc
  have hfval := (convex_closedBall z e).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun w _ => (f.hasDerivAt w).hasDerivWithinAt) hfirst hzc hcc
  have hfder := (convex_closedBall z e).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun w _ => (f.derivative.hasDerivAt w).hasDerivWithinAt) hsecond hzc hcc
  have hvalue : ‖f.eval c‖ ≤ M*e := by
    rw [hz, sub_zero] at hfval
    exact hfval.trans (mul_le_mul_of_nonneg_left hc hM)
  have hderdiff : ‖f.derivative.eval c-f.derivative.eval z‖ ≤ M*e :=
    hfder.trans (mul_le_mul_of_nonneg_left hc hM)
  have hm1 : (1 : ℝ) ≤ f.natDegree := by exact_mod_cast hm
  have hMe : 0 ≤ M*e := mul_nonneg hM he
  have hbudget' : 8*(M*e) ≤ r*A := by nlinarith [mul_nonneg (sub_nonneg.mpr hm1) hMe]
  have hsmall : M*e ≤ A/8 := by nlinarith [mul_le_mul_of_nonneg_right hr1 hA.le]
  have hderlow : A/2 ≤ ‖f.derivative.eval c‖ := by
    have ht := norm_sub_norm_le (f.derivative.eval z) (f.derivative.eval c)
    rw [norm_sub_rev] at ht
    linarith
  have hlinf : A/4 ≤ max |(f.derivative.eval c).re| |(f.derivative.eval c).im| := by
    have hn := Complex.norm_le_abs_re_add_abs_im (f.derivative.eval c)
    have h1 := le_max_left |(f.derivative.eval c).re| |(f.derivative.eval c).im|
    have h2 := le_max_right |(f.derivative.eval c).re| |(f.derivative.eval c).im|
    linarith
  have hl1 : |(f.eval c).re| + |(f.eval c).im| ≤ 2*M*e := by
    have h1 := Complex.abs_re_le_norm (f.eval c)
    have h2 := Complex.abs_im_le_norm (f.eval c)
    linarith
  refine ⟨?_, lt_of_lt_of_le (by linarith : 0 < A/4) hlinf⟩
  have hv := mul_le_mul_of_nonneg_left hl1 (Nat.cast_nonneg f.natDegree : (0 : ℝ) ≤ _)
  have hp := mul_le_mul_of_nonneg_left hlinf hr
  nlinarith only [hv, hp, hbudget]

/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionInternal_nearby_root_actual_horner` under the displayed hypotheses. -/
private theorem rootProjectionInternal_nearby_root_actual_horner (n : ℕ) (a : Fin (n+2) → ℤ)
    (ha : a (Fin.last (n+1)) ≠ 0) (z : ℂ) (c : ℚ×ℚ) (A M e : ℝ) (r : ℚ)
    (hA : 0 < A) (hM : 0 ≤ M) (he : 0 ≤ e) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hz : (rootIntegerPolynomial a).eval z = 0)
    (hc : ‖rootRationalCoordinate c-z‖ ≤ e)
    (hprime : A ≤ ‖(rootIntegerPolynomial a).derivative.eval z‖)
    (hfirst : ∀ w ∈ Metric.closedBall z e,
      ‖(rootIntegerPolynomial a).derivative.eval w‖ ≤ M)
    (hsecond : ∀ w ∈ Metric.closedBall z e,
      ‖(rootIntegerPolynomial a).derivative.derivative.eval w‖ ≤ M)
    (hbudget : 8 * ((n+1 : ℕ) : ℝ) * M * e ≤ (r : ℝ) * A) :
    rootIntegerCoordinateBound (n+1)
      (rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c) (List.ofFn a))
      (rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c)
        (List.ofFn (rootIntegerDerivative n a))) r ∧
    0 < max
      |(rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c)
        (List.ofFn (rootIntegerDerivative n a))).numerator.1|
      |(rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c)
        (List.ofFn (rootIntegerDerivative n a))).numerator.2| := by
  have hd := rootIntegerPolynomial_natDegree a ha
  have hp := rootProjectionInternal_nearby_root_coordinate (rootIntegerPolynomial a) z (rootRationalCoordinate c)
    A M e r (by omega) hA hM he (by exact_mod_cast hr) (by exact_mod_cast hr1)
    hz hc hprime hfirst hsecond (by simpa only [hd] using hbudget)
  let v := rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c) (List.ofFn a)
  let w := rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c)
    (List.ofFn (rootIntegerDerivative n a))
  have hE : 0 < v.denominator :=
    rootCompactHorner_denominator_pos _ _ _ (rootSharedDenominator_pos c)
  have hF : 0 < w.denominator :=
    rootCompactHorner_denominator_pos _ _ _ (rootSharedDenominator_pos c)
  have hv : gaussianPointValue v = (rootIntegerPolynomial a).eval (rootRationalCoordinate c) :=
    rootIntegerPolynomial_horner a c
  have hw : gaussianPointValue w =
      (rootIntegerPolynomial a).derivative.eval (rootRationalCoordinate c) := by
    rw [rootIntegerPolynomial_derivative]
    exact rootIntegerPolynomial_horner (rootIntegerDerivative n a) c
  refine ⟨rootProjectionInternal_integer_coordinate_complete (n+1) v w r hE hF ?_, ?_⟩
  · simpa only [hv, hw, hd] using hp.1
  · have hpos : (0 : ℝ) < max |(gaussianPointValue w).re| |(gaussianPointValue w).im| := by
      simpa only [hw] using hp.2
    rw [rootIntegerValue_linf w hF] at hpos
    have hdpos : (0 : ℝ) < w.denominator := by exact_mod_cast hF
    have hnum : (0 : ℝ) < max |(w.numerator.1 : ℝ)| |(w.numerator.2 : ℝ)| :=
      (div_pos_iff_of_pos_right hdpos).mp hpos
    change (0 : ℤ) < max |w.numerator.1| |w.numerator.2|
    exact_mod_cast hnum

/-! Literal source precision controller. Generated contexts, their heights,
Sturm correctness and radial promises still require separate proofs. -/
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-- Data and invariants for Root Projection Context in the native root projection budget model. -/
structure RootProjectionContext where
  factor : List ℤ
  exponent : ℕ
  xProjection : List ℤ
  yProjection : List ℤ

/-- Construction for root Projection List Max in the native root projection budget model. -/
private def rootProjectionListMax (xs : List ℕ) : ℕ := xs.foldl max 0
/-- Construction for root Projection Degree in the native root projection budget model. -/
def rootProjectionDegree (f : List ℤ) : ℕ := f.length-1
/-- Construction for root Projection Height in the native root projection budget model. -/
def rootProjectionHeight (f : List ℤ) : ℕ := rootProjectionListMax (f.map (fun a => a.natAbs.size))
/-- Construction for root Projection AExponent in the native root projection budget model. -/
def rootProjectionAExponent (c : RootProjectionContext) : ℕ :=
  rootProjectionDegree c.factor * rootProjectionDegree c.factor * (rootProjectionHeight c.factor+2) * (rootProjectionDegree c.factor-1)
/-- Construction for root Projection MExponent in the native root projection budget model. -/
def rootProjectionMExponent (c : RootProjectionContext) : ℕ :=
  3*sourceCeilLog2 (rootProjectionDegree c.factor)+rootProjectionHeight c.factor+
    rootProjectionDegree c.factor*(rootProjectionHeight c.factor+2)
/-- Construction for root Projection Separation Exponent in the native root projection budget model. -/
def rootProjectionSeparationExponent (f : List ℤ) : ℕ :=
  rootProjectionDegree f * rootProjectionDegree f * (rootProjectionHeight f+rootProjectionDegree f*(rootProjectionHeight f+2)+2)
/-- Construction for root Projection Context Terms in the native root projection budget model. -/
def rootProjectionContextTerms (c : RootProjectionContext) : List ℕ :=
  [rootProjectionAExponent c+rootProjectionMExponent c+sourceCeilLog2 (8*rootProjectionDegree c.factor)+4,
   rootProjectionSeparationExponent c.xProjection+5, rootProjectionSeparationExponent c.yProjection+5]
/-- Construction for root Projection Terms in the native root projection budget model. -/
def rootProjectionTerms (contexts : List RootProjectionContext) (bits : ℕ) (gap : ℚ) : List ℕ :=
  [bits+4,sourceCeilLog2 (1/gap)+4] ++ contexts.flatMap rootProjectionContextTerms
/-- Construction for root Projection Cap in the native root projection budget model. -/
def rootProjectionCap (contexts : List RootProjectionContext) (bits : ℕ) (gap : ℚ) : ℕ :=
  max (2*bits+16) (2*(rootProjectionListMax (rootProjectionTerms contexts bits gap)+2))
/-- Construction for root Projection Half in the native root projection budget model. -/
def rootProjectionHalf (contexts : List RootProjectionContext) (bits : ℕ) (gap : ℚ) : ℕ := rootProjectionCap contexts bits gap/2
/-- Construction for root Projection Radius in the native root projection budget model. -/
def rootProjectionRadius (contexts : List RootProjectionContext) (bits : ℕ) (gap : ℚ) : ℚ :=
  1/(2 : ℚ)^rootProjectionHalf contexts bits gap
/-- Construction for root Projection Midpoint Error in the native root projection budget model. -/
def rootProjectionMidpointError (contexts : List RootProjectionContext) (bits : ℕ) (gap : ℚ) : ℚ :=
  1/(2 : ℚ)^rootProjectionCap contexts bits gap

/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionInternal_fold_max_initial` under the displayed hypotheses. -/
private theorem rootProjectionInternal_fold_max_initial (xs : List ℕ) (a : ℕ) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => exact (le_max_left a x).trans (ih (max a x))
/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionInternal_capFoldMaxMember` under the displayed hypotheses. -/
private theorem rootProjectionInternal_capFoldMaxMember (xs : List ℕ) (a x : ℕ) (hx : x ∈ xs) :
    x ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with h | h
    · subst y
      exact (le_max_right a x).trans (rootProjectionInternal_fold_max_initial ys (max a x))
    · exact ih (max a y) h

/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionInternal_half_ge_term` under the displayed hypotheses. -/
private theorem rootProjectionInternal_half_ge_term (contexts : List RootProjectionContext) (bits t : ℕ) (gap : ℚ)
    (ht : t ∈ rootProjectionTerms contexts bits gap) : t+2 ≤ rootProjectionHalf contexts bits gap := by
  have hm := rootProjectionInternal_capFoldMaxMember (rootProjectionTerms contexts bits gap) 0 t ht
  have hc := le_max_right (2*bits+16) (2*(rootProjectionListMax (rootProjectionTerms contexts bits gap)+2))
  change t+2 ≤ rootProjectionCap contexts bits gap/2
  unfold rootProjectionCap
  change t ≤ rootProjectionListMax (rootProjectionTerms contexts bits gap) at hm
  omega

/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionCap_even` under the displayed hypotheses. -/
theorem rootProjectionCap_even (contexts : List RootProjectionContext) (bits : ℕ) (gap : ℚ) :
    rootProjectionCap contexts bits gap = 2*rootProjectionHalf contexts bits gap := by
  unfold rootProjectionCap rootProjectionHalf rootProjectionCap
  omega

/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionInternal_half_ge_bits` under the displayed hypotheses. -/
private theorem rootProjectionInternal_half_ge_bits (contexts : List RootProjectionContext) (bits : ℕ) (gap : ℚ) :
    bits+8 ≤ rootProjectionHalf contexts bits gap := by
  have hc := le_max_left (2*bits+16) (2*(rootProjectionListMax (rootProjectionTerms contexts bits gap)+2))
  change bits+8 ≤ rootProjectionCap contexts bits gap/2
  unfold rootProjectionCap
  omega

/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionInternal_midpoint_square` under the displayed hypotheses. -/
private theorem rootProjectionInternal_midpoint_square (contexts : List RootProjectionContext) (bits : ℕ) (gap : ℚ) :
    rootProjectionMidpointError contexts bits gap = rootProjectionRadius contexts bits gap ^ 2 := by
  unfold rootProjectionMidpointError rootProjectionRadius
  rw [rootProjectionCap_even, Nat.mul_comm 2 (rootProjectionHalf contexts bits gap), pow_mul]
  simp only [one_div, inv_pow]

/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionCap_radius_budgets` under the displayed hypotheses. -/
theorem rootProjectionCap_radius_budgets (contexts : List RootProjectionContext) (bits : ℕ) (gap : ℚ)
    (hg : 0 < gap) :
    0 < rootProjectionRadius contexts bits gap ∧ rootProjectionRadius contexts bits gap ≤ 1 ∧
      rootProjectionRadius contexts bits gap ≤ (1/(2 : ℚ)^bits)/256 ∧
      rootProjectionRadius contexts bits gap ≤ gap/64 := by
  have hb := rootProjectionInternal_half_ge_bits contexts bits gap
  have hp : (2 : ℚ)^(bits+8) ≤ 2^rootProjectionHalf contexts bits gap :=
    pow_le_pow_right₀ (by norm_num) hb
  have he := sourceCeilLog2_envelope (1/gap) (by positivity)
  have ht : sourceCeilLog2 (1/gap)+4 ∈ rootProjectionTerms contexts bits gap := by
    simp [rootProjectionTerms]
  have hs := rootProjectionInternal_half_ge_term contexts bits _ gap ht
  have hgp : (2 : ℚ)^(sourceCeilLog2 (1/gap)+6) ≤ 2^rootProjectionHalf contexts bits gap :=
    pow_le_pow_right₀ (by norm_num) hs
  have hbig : 64/gap ≤ (2 : ℚ)^rootProjectionHalf contexts bits gap := by
    calc
      _ = 64*(1/gap) := by ring
      _ ≤ 64*(2 : ℚ)^sourceCeilLog2 (1/gap) :=
        mul_le_mul_of_nonneg_left he (by norm_num)
      _ = (2 : ℚ)^(sourceCeilLog2 (1/gap)+6) := by rw [pow_add]; norm_num; ring
      _ ≤ _ := hgp
  have hrb : rootProjectionRadius contexts bits gap ≤ (1/(2 : ℚ)^bits)/256 := by
    unfold rootProjectionRadius
    calc
      _ ≤ 1/(2 : ℚ)^(bits+8) := one_div_le_one_div_of_le (by positivity) hp
      _ = _ := by rw [pow_add]; norm_num; ring
  have hrg : rootProjectionRadius contexts bits gap ≤ gap/64 := by
    unfold rootProjectionRadius
    apply (div_le_iff₀ (by positivity)).mpr
    have hx := (div_le_iff₀ hg).mp hbig
    nlinarith only [hx]
  refine ⟨by unfold rootProjectionRadius; positivity, ?_, hrb, hrg⟩
  unfold rootProjectionRadius
  exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))

/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionInternal_cap_analytic_budget` under the displayed hypotheses. -/
private theorem rootProjectionInternal_cap_analytic_budget (contexts : List RootProjectionContext) (bits : ℕ) (gap : ℚ)
    (c : RootProjectionContext) (hc : c ∈ contexts) (hm : 0 < rootProjectionDegree c.factor) :
    8*(rootProjectionDegree c.factor : ℚ)*(2 : ℚ)^rootProjectionMExponent c * rootProjectionMidpointError contexts bits gap ≤
      rootProjectionRadius contexts bits gap * (1/(2 : ℚ)^rootProjectionAExponent c) := by
  have ht : rootProjectionAExponent c+rootProjectionMExponent c+sourceCeilLog2 (8*rootProjectionDegree c.factor)+4 ∈
      rootProjectionTerms contexts bits gap := by
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    exact ⟨c, hc, by simp [rootProjectionContextTerms]⟩
  have hs := rootProjectionInternal_half_ge_term contexts bits _ gap ht
  have hpower : (2 : ℚ)^(rootProjectionAExponent c+rootProjectionMExponent c+sourceCeilLog2 (8*rootProjectionDegree c.factor)) ≤
      2^rootProjectionHalf contexts bits gap := pow_le_pow_right₀ (by norm_num) (by omega)
  have hmQ : (0 : ℚ) < rootProjectionDegree c.factor := by exact_mod_cast hm
  have he := sourceCeilLog2_envelope (8*rootProjectionDegree c.factor) (by positivity)
  have hprod : 8*(rootProjectionDegree c.factor : ℚ)*(2 : ℚ)^rootProjectionMExponent c * 2^rootProjectionAExponent c ≤
      2^rootProjectionHalf contexts bits gap := by
    calc
      _ ≤ (2 : ℚ)^rootProjectionAExponent c * 2^rootProjectionMExponent c * 2^sourceCeilLog2 (8*rootProjectionDegree c.factor) := by
        have hx := mul_le_mul_of_nonneg_left he
          (by positivity : (0 : ℚ) ≤ (2 : ℚ)^rootProjectionAExponent c * 2^rootProjectionMExponent c)
        nlinarith only [hx]
      _ = (2 : ℚ)^(rootProjectionAExponent c+rootProjectionMExponent c+sourceCeilLog2 (8*rootProjectionDegree c.factor)) := by
        rw [pow_add, pow_add]
      _ ≤ _ := hpower
  rw [rootProjectionInternal_midpoint_square]
  unfold rootProjectionRadius
  have hp : (0 : ℚ) < (2 : ℚ)^rootProjectionHalf contexts bits gap := by positivity
  have ha : (0 : ℚ) < (2 : ℚ)^rootProjectionAExponent c := by positivity
  calc
    _ = (8*(rootProjectionDegree c.factor : ℚ)*(2 : ℚ)^rootProjectionMExponent c) /
        ((2 : ℚ)^rootProjectionHalf contexts bits gap)^2 := by ring
    _ ≤ 1/((2 : ℚ)^rootProjectionHalf contexts bits gap * 2^rootProjectionAExponent c) := by
      apply (div_le_div_iff₀ (pow_pos hp 2) (mul_pos hp ha)).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hprod hp.le]
    _ = _ := by field_simp


/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionInternal_cap_actual_horner` under the displayed hypotheses. -/
private theorem rootProjectionInternal_cap_actual_horner (contexts : List RootProjectionContext) (bits : ℕ) (gap : ℚ)
    (hg : 0 < gap) (ctx : RootProjectionContext) (hctx : ctx ∈ contexts)
    (n : ℕ) (a : Fin (n+2) → ℤ) (ha : a (Fin.last (n+1)) ≠ 0)
    (hfactor : ctx.factor = List.ofFn a) (z : ℂ) (c : ℚ×ℚ)
    (hz : (rootIntegerPolynomial a).eval z = 0)
    (hc : ‖rootRationalCoordinate c-z‖ ≤ (rootProjectionMidpointError contexts bits gap : ℝ))
    (hprime : 1/(2 : ℝ)^rootProjectionAExponent ctx ≤ ‖(rootIntegerPolynomial a).derivative.eval z‖)
    (hfirst : ∀ w ∈ Metric.closedBall z (rootProjectionMidpointError contexts bits gap : ℝ),
      ‖(rootIntegerPolynomial a).derivative.eval w‖ ≤ (2 : ℝ)^rootProjectionMExponent ctx)
    (hsecond : ∀ w ∈ Metric.closedBall z (rootProjectionMidpointError contexts bits gap : ℝ),
      ‖(rootIntegerPolynomial a).derivative.derivative.eval w‖ ≤ (2 : ℝ)^rootProjectionMExponent ctx) :
    rootIntegerCoordinateBound (n+1)
      (rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c) (List.ofFn a))
      (rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c)
        (List.ofFn (rootIntegerDerivative n a))) (rootProjectionRadius contexts bits gap) ∧
    0 < max
      |(rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c)
        (List.ofFn (rootIntegerDerivative n a))).numerator.1|
      |(rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c)
        (List.ofFn (rootIntegerDerivative n a))).numerator.2| := by
  have hd : rootProjectionDegree ctx.factor = n+1 := by simp [rootProjectionDegree,hfactor]
  have hb := rootProjectionInternal_cap_analytic_budget contexts bits gap ctx hctx (by omega)
  have hb' : 8*((n+1 : ℕ) : ℝ)*(2 : ℝ)^rootProjectionMExponent ctx *
      (rootProjectionMidpointError contexts bits gap : ℝ) ≤
      (rootProjectionRadius contexts bits gap : ℝ)*(1/(2 : ℝ)^rootProjectionAExponent ctx) := by
    rw [hd] at hb
    have hbR := (Rat.cast_le (K := ℝ)).mpr hb
    push_cast at hbR
    simpa only [Nat.cast_add, Nat.cast_one] using hbR
  have hr := rootProjectionCap_radius_budgets contexts bits gap hg
  exact rootProjectionInternal_nearby_root_actual_horner n a ha z c (1/(2 : ℝ)^rootProjectionAExponent ctx)
    ((2 : ℝ)^rootProjectionMExponent ctx) (rootProjectionMidpointError contexts bits gap) (rootProjectionRadius contexts bits gap)
    (by positivity) (by positivity) (by unfold rootProjectionMidpointError; positivity)
    hr.1.le hr.2.1 hz hc hprime hfirst hsecond hb'

/-! Private alternative to a separate pairwise root-separation proof for
the derivative lower bound. Nonzero INTEGER resultant remains a premise. -/
open Polynomial

/-- The estimate `rootProjectionInternal_norm_product_bound` retains the actual parameter, input-error and normalization budgets. -/
private theorem rootProjectionInternal_norm_product_bound (s : Multiset ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hs : ∀ x ∈ s, ‖x‖ ≤ M) : ‖s.prod‖ ≤ M^s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons x xs ih =>
    rw [Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ]
    have hx := hs x (Multiset.mem_cons_self x xs)
    have hr := ih (fun y hy => hs y (Multiset.mem_cons_of_mem hy))
    nlinarith [mul_le_mul hx hr (norm_nonneg xs.prod) hM]

/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionInternal_integer_resultant_derivative_lower` under the displayed hypotheses. -/
private theorem rootProjectionInternal_integer_resultant_derivative_lower (p : ℤ[X]) (hp : 0 < p.natDegree)
    (hres : p.resultant p.derivative p.natDegree (p.natDegree-1) ≠ 0)
    (B M : ℝ) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hlead : ‖(p.map (Int.castRingHom ℂ)).leadingCoeff‖ ≤ B)
    (hupper : ∀ w ∈ (p.map (Int.castRingHom ℂ)).roots,
      ‖(p.map (Int.castRingHom ℂ)).derivative.eval w‖ ≤ M)
    (z : ℂ) (hz : (p.map (Int.castRingHom ℂ)).eval z = 0) :
    1 ≤ B^(p.natDegree-1)*M^(p.natDegree-1)*
      ‖(p.map (Int.castRingHom ℂ)).derivative.eval z‖ := by
  classical
  let f := p.map (Int.castRingHom ℂ)
  let R := p.resultant p.derivative p.natDegree (p.natDegree-1)
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have hd : f.natDegree = p.natDegree := Polynomial.natDegree_map_eq_of_injective hinj p
  have hf0 : f ≠ 0 := by intro h; simp [h] at hd; omega
  have hf : f.Splits := IsAlgClosed.splits f
  have hcard : f.roots.card = p.natDegree := hf.natDegree_eq_card_roots.symm.trans hd
  have hmem : z ∈ f.roots := (Polynomial.mem_roots hf0).mpr hz
  have herase : (f.roots.erase z).card = p.natDegree-1 := by
    rw [Multiset.card_erase_of_mem hmem,hcard]
    exact Nat.pred_eq_sub_one
  have hresmap : f.resultant f.derivative p.natDegree (p.natDegree-1) = (R : ℂ) := by
    dsimp only [f,R]
    rw [Polynomial.derivative_map, Polynomial.resultant_map_map]
    rfl
  have hfac : (R : ℂ) = f.leadingCoeff^(p.natDegree-1) *
      (f.roots.map f.derivative.eval).prod := by
    rw [← hresmap, ← hd]
    exact Polynomial.resultant_eq_prod_eval f f.derivative (f.natDegree-1)
      (Polynomial.natDegree_derivative_le f) hf
  have hint : (1 : ℝ) ≤ ‖(R : ℂ)‖ := by
    have hr : (1 : ℝ) ≤ |(R : ℝ)| := by exact_mod_cast Int.one_le_abs hres
    simpa only [Complex.norm_intCast, Int.norm_eq_abs, Int.cast_abs] using hr
  have htail : ‖((f.roots.erase z).map f.derivative.eval).prod‖ ≤ M^(p.natDegree-1) := by
    have h := rootProjectionInternal_norm_product_bound ((f.roots.erase z).map f.derivative.eval) M hM ?_
    · simpa only [Multiset.card_map,herase] using h
    · intro w hw
      obtain ⟨u,hu,rfl⟩ := Multiset.mem_map.mp hw
      exact hupper u (Multiset.mem_of_mem_erase hu)
  have hnorm : ‖(R : ℂ)‖ = ‖f.leadingCoeff‖^(p.natDegree-1) *
      ‖f.derivative.eval z‖ * ‖((f.roots.erase z).map f.derivative.eval).prod‖ := by
    conv_lhs => rw [hfac, ← Multiset.cons_erase hmem, Multiset.map_cons, Multiset.prod_cons]
    simp only [norm_mul,norm_pow]
    ring
  calc
    1 ≤ ‖(R : ℂ)‖ := hint
    _ = _ := hnorm
    _ ≤ B^(p.natDegree-1) * ‖f.derivative.eval z‖ * M^(p.natDegree-1) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg _) hlead _) (norm_nonneg _)
      · exact htail
      · exact norm_nonneg _
      · positivity
    _ = _ := by ring

/-! Private source-rootProjectionHeight supplier. Bounds come from the actual integer
coefficient list; no derivative upper answer is an input. -/
open Polynomial
open scoped BigOperators
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput

/-- The estimate `rootProjectionInternal_eval_bound` retains the actual parameter, input-error and normalization budgets. -/
private theorem rootProjectionInternal_eval_bound (p : ℂ[X]) (m : ℕ) (C R : ℝ) (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hd : p.natDegree < m) (hcoeff : ∀ i < m, ‖p.coeff i‖ ≤ C)
    (w : ℂ) (hw : ‖w‖ ≤ R) : ‖p.eval w‖ ≤ (m : ℝ)*C*R^m := by
  rw [Polynomial.eval_eq_sum_range' hd]
  calc
    _ ≤ ∑ i ∈ Finset.range m, ‖p.coeff i*w^i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ Finset.range m, C*R^m := by
      apply Finset.sum_le_sum
      intro i hi
      have him : i < m := Finset.mem_range.mp hi
      rw [norm_mul,norm_pow]
      apply mul_le_mul (hcoeff i him)
      · exact (pow_le_pow_left₀ (norm_nonneg _) hw i).trans
          (pow_le_pow_right₀ hR him.le)
      · positivity
      · exact hC
    _ = _ := by simp; ring

/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionInternal_derivatives_from_coefficients` under the displayed hypotheses. -/
private theorem rootProjectionInternal_derivatives_from_coefficients (p : ℂ[X]) (m : ℕ) (hm : 0 < m)
    (hd : p.natDegree = m) (B R : ℝ) (hB : 0 ≤ B) (hR : 1 ≤ R)
    (hcoeff : ∀ i, ‖p.coeff i‖ ≤ B) (w : ℂ) (hw : ‖w‖ ≤ R) :
    ‖p.derivative.eval w‖ ≤ (m : ℝ)^3*B*R^m ∧
      ‖p.derivative.derivative.eval w‖ ≤ (m : ℝ)^3*B*R^m := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hdeg : p.derivative.natDegree < m := by
    simpa only [hd] using Polynomial.natDegree_derivative_lt (p := p) (by omega)
  have hdeg2 : p.derivative.derivative.natDegree < m :=
    (Polynomial.natDegree_derivative_le p.derivative).trans_lt (by omega)
  have hfirst : ∀ i < m, ‖p.derivative.coeff i‖ ≤ (m : ℝ)*B := by
    intro i hi
    rw [Polynomial.coeff_derivative,norm_mul]
    have hii : ((i+1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hi
    have hn : ‖((i+1 : ℕ) : ℂ)‖ = ((i+1 : ℕ) : ℝ) := Complex.norm_natCast (i+1)
    rw [← Nat.cast_add_one, hn]
    have hh := mul_le_mul (hcoeff (i+1)) hii (by positivity) hB
    nlinarith only [hh]
  have hsecond : ∀ i < m, ‖p.derivative.derivative.coeff i‖ ≤ (m : ℝ)^2*B := by
    intro i _hi
    rw [Polynomial.coeff_derivative,Polynomial.coeff_derivative]
    by_cases hi : i+2 ≤ m
    · have h1 : ((i+1 : ℕ) : ℝ) ≤ m := by exact_mod_cast (by omega : i+1 ≤ m)
      have h2 : ((i+2 : ℕ) : ℝ) ≤ m := by exact_mod_cast hi
      simp only [norm_mul, ← Nat.cast_add_one, Complex.norm_natCast]
      have hh := mul_le_mul (hcoeff (i+2)) h2 (by positivity) hB
      have hh' := mul_le_mul hh h1 (by positivity) (by positivity : (0 : ℝ) ≤ B*m)
      nlinarith only [hh']
    · have hz : p.coeff (i+1+1) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hz,zero_mul,zero_mul,norm_zero]
      positivity
  have hf := rootProjectionInternal_eval_bound p.derivative m ((m : ℝ)*B) R (by positivity) hR hdeg hfirst w hw
  have hs := rootProjectionInternal_eval_bound p.derivative.derivative m ((m : ℝ)^2*B) R
    (by positivity) hR hdeg2 hsecond w hw
  refine ⟨?_, by nlinarith only [hs]⟩
  have hmp : (m : ℝ)^2 ≤ (m : ℝ)^3 := by nlinarith [sq_nonneg ((m : ℝ)-1)]
  have hmul := mul_le_mul_of_nonneg_right hmp (by positivity : (0 : ℝ) ≤ B*R^m)
  nlinarith only [hf,hmul]

/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionInternal_heightFoldMaxMember` under the displayed hypotheses. -/
private theorem rootProjectionInternal_heightFoldMaxMember (xs : List ℕ) (a x : ℕ) (hx : x ∈ xs) :
    x ≤ xs.foldl max a := by
  have init : ∀ (ys : List ℕ) (b : ℕ), b ≤ ys.foldl max b := by
    intro ys
    induction ys with
    | nil => intro b; rfl
    | cons y ys ih => intro b; exact (le_max_left b y).trans (ih (max b y))
  induction xs generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with h | h
    · subst y; exact (le_max_right a x).trans (init ys (max a x))
    · exact ih (max a y) h

/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionInternal_coefficient_from_height` under the displayed hypotheses. -/
private theorem rootProjectionInternal_coefficient_from_height (cs : List ℤ) (k : ℕ) :
    ‖(rootIntegerListPolynomial cs).coeff k‖ ≤ (2 : ℝ)^rootProjectionHeight cs := by
  have hsize : (cs.getD k 0).natAbs.size ≤ rootProjectionHeight cs := by
    by_cases hk : k < cs.length
    · have hm : cs.getD k 0 ∈ cs := by
        simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,Option.getD_some] using
          List.getElem_mem hk
      exact rootProjectionInternal_heightFoldMaxMember _ 0 _ (List.mem_map.mpr ⟨_,hm,rfl⟩)
    · simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_none (by omega : cs.length ≤ k),
        Option.getD_none,Int.natAbs_zero,Nat.size_zero]
      exact Nat.zero_le _
  have hn : (cs.getD k 0).natAbs ≤ 2^rootProjectionHeight cs :=
    (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) hsize)
  rw [rootIntegerListPolynomial_coeff,Complex.norm_intCast]
  simpa only [Int.norm_eq_abs, Nat.cast_natAbs, Int.cast_abs, Nat.cast_pow, Nat.cast_ofNat] using
    (show ((cs.getD k 0).natAbs : ℝ) ≤ (2 : ℝ)^rootProjectionHeight cs by exact_mod_cast hn)

/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionInternal_source_M_envelope` under the displayed hypotheses. -/
private theorem rootProjectionInternal_source_M_envelope (ctx : RootProjectionContext) (hm : 0 < rootProjectionDegree ctx.factor) :
    (rootProjectionDegree ctx.factor : ℝ)^3*(2 : ℝ)^rootProjectionHeight ctx.factor*
      (3*(2 : ℝ)^rootProjectionHeight ctx.factor)^rootProjectionDegree ctx.factor ≤ (2 : ℝ)^rootProjectionMExponent ctx := by
  let m := rootProjectionDegree ctx.factor
  let ell := rootProjectionHeight ctx.factor
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hlogQ := sourceCeilLog2_envelope (m : ℚ) hmQ
  have hlog : (m : ℝ) ≤ (2 : ℝ)^sourceCeilLog2 (m : ℚ) := by exact_mod_cast hlogQ
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ m) hlog 3
  have hr : 3*(2 : ℝ)^ell ≤ 2^(ell+2) := by rw [pow_add]; norm_num; nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) ell]
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 3*(2 : ℝ)^ell) hr m
  calc
    _ ≤ ((2 : ℝ)^sourceCeilLog2 (m : ℚ))^3 * 2^ell * (2^(ell+2))^m := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hp (by positivity)) hpow
        (by positivity) (by positivity)
    _ = _ := by
      dsimp only [rootProjectionMExponent,m,ell]
      rw [← pow_mul,← pow_mul,← pow_add,← pow_add]
      congr 1
      ring

/-- The estimate `rootProjectionInternal_root_bound` retains the actual parameter, input-error and normalization budgets. -/
private theorem rootProjectionInternal_root_bound (p : ℂ[X]) (hp : p ≠ 0) (B : ℝ) (hB : 1 ≤ B)
    (hcoeff : ∀ i, ‖p.coeff i‖ ≤ B) (hlead : 1 ≤ ‖p.leadingCoeff‖)
    (z : ℂ) (hz : p.eval z = 0) : ‖z‖ ≤ 2*B := by
  let b : NNReal := ⟨B,by linarith⟩
  have hs : (Finset.range p.natDegree).sup (fun i => ‖p.coeff i‖₊) ≤ b := by
    apply Finset.sup_le
    intro i _
    exact_mod_cast hcoeff i
  have hl : (1 : NNReal) ≤ ‖p.leadingCoeff‖₊ := by exact_mod_cast hlead
  have hlp : (0 : NNReal) < ‖p.leadingCoeff‖₊ := lt_of_lt_of_le zero_lt_one hl
  have hq : (Finset.range p.natDegree).sup (fun i => ‖p.coeff i‖₊) /
      ‖p.leadingCoeff‖₊ ≤ b := by
    apply (div_le_iff₀ hlp).mpr
    exact hs.trans (by simpa using mul_le_mul_of_nonneg_left hl (zero_le : (0 : NNReal) ≤ b))
  have hcb : p.cauchyBound ≤ b+1 := by
    dsimp only [Polynomial.cauchyBound]
    exact add_le_add hq (le_refl 1)
  have hr := (Polynomial.IsRoot.norm_lt_cauchyBound hp hz).trans_le hcb
  have hrR : ‖z‖ < B+1 := by exact_mod_cast hr
  linarith

/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionInternal_actual_leading_lower` under the displayed hypotheses. -/
private theorem rootProjectionInternal_actual_leading_lower (n : ℕ) (a : Fin (n+2) → ℤ)
    (ha : a (Fin.last (n+1)) ≠ 0) : 1 ≤ ‖(rootIntegerPolynomial a).leadingCoeff‖ := by
  have hd := rootIntegerPolynomial_natDegree a ha
  have hl : (rootIntegerPolynomial a).leadingCoeff = (a (Fin.last (n+1)) : ℂ) := by
    rw [Polynomial.leadingCoeff,hd,rootIntegerPolynomial_coeff,dite_eq_left (by omega)]
    rfl
  rw [hl,Complex.norm_intCast]
  have h := Int.one_le_abs ha
  exact_mod_cast h

/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionFactor_local_derivatives` under the displayed hypotheses. -/
theorem rootProjectionFactor_local_derivatives (ctx : RootProjectionContext) (n : ℕ) (a : Fin (n+2) → ℤ)
    (hfactor : ctx.factor = List.ofFn a) (ha : a (Fin.last (n+1)) ≠ 0)
    (z : ℂ) (hz : (rootIntegerPolynomial a).eval z = 0) (e : ℝ) (he : e ≤ 1) :
    ∀ w ∈ Metric.closedBall z e,
      ‖(rootIntegerPolynomial a).derivative.eval w‖ ≤ (2 : ℝ)^rootProjectionMExponent ctx ∧
        ‖(rootIntegerPolynomial a).derivative.derivative.eval w‖ ≤ (2 : ℝ)^rootProjectionMExponent ctx := by
  let B : ℝ := (2 : ℝ)^rootProjectionHeight ctx.factor
  let m := rootProjectionDegree ctx.factor
  have hm : m = n+1 := by simp [m,rootProjectionDegree,hfactor]
  have hB : 1 ≤ B := one_le_pow₀ (by norm_num)
  have hcoeff : ∀ i, ‖(rootIntegerPolynomial a).coeff i‖ ≤ B := by
    intro i
    change ‖(rootIntegerPolynomial a).coeff i‖ ≤ (2 : ℝ)^rootProjectionHeight ctx.factor
    rw [← rootIntegerListPolynomial_ofFn a, ← hfactor]
    exact rootProjectionInternal_coefficient_from_height ctx.factor i
  have hd : (rootIntegerPolynomial a).natDegree = m := (rootIntegerPolynomial_natDegree a ha).trans hm.symm
  have hp : rootIntegerPolynomial a ≠ 0 := by intro h; simp [h] at hd; omega
  have hroot := rootProjectionInternal_root_bound (rootIntegerPolynomial a) hp B hB hcoeff (rootProjectionInternal_actual_leading_lower n a ha) z hz
  intro w hw
  have hdist : ‖w-z‖ ≤ e := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hw
  have hwR : ‖w‖ ≤ 3*B := by
    have ht' : ‖w‖ ≤ ‖w-z‖+‖z‖ := by simpa only [sub_add_cancel] using norm_add_le (w-z) z
    linarith
  have h := rootProjectionInternal_derivatives_from_coefficients (rootIntegerPolynomial a) m (by omega) hd B (3*B)
    (by linarith) (by linarith) hcoeff w hwR
  have henv := rootProjectionInternal_source_M_envelope ctx (by omega)
  exact ⟨h.1.trans henv,h.2.trans henv⟩

/-! Source Aexp from integral resultant and actual coefficient heights.
The generated factor must still be shown to have nonzero resultant. -/
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput

/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionInternal_ceil_nat_le_of_power` under the displayed hypotheses. -/
private theorem rootProjectionInternal_ceil_nat_le_of_power (m k : ℕ) (hm : 0 < m) (hk : m ≤ 2^k) :
    sourceCeilLog2 (m : ℚ) ≤ k := by
  let v := m.size-1
  have hsize : 0 < m.size := Nat.size_pos.mpr hm
  have hlow : 2^v ≤ m := Nat.lt_size.mp (by dsimp [v]; omega)
  have hv : v ≤ k := by
    by_contra! h
    have hpow := Nat.pow_lt_pow_right (by decide : 1 < 2) h
    omega
  unfold sourceCeilLog2
  dsimp only
  split_ifs with h
  · have h' : (2 : ℚ)^v < (m : ℚ) := by simpa [v] using h
    have hvlt : v < k := by
      by_contra! hnot
      have he : v = k := by omega
      rw [he] at h'
      have hkQ : (m : ℚ) ≤ (2 : ℚ)^k := by exact_mod_cast hk
      exact (not_lt_of_ge hkQ) h'
    simpa only [Rat.num_natCast,Rat.den_natCast,Int.natAbs_natCast,Nat.size_one] using
      (by omega : v+1 ≤ k)
  · simpa only [Rat.num_natCast,Rat.den_natCast,Int.natAbs_natCast,Nat.size_one,Nat.add_zero] using hv

/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionInternal_ceil_nat_le_pred` under the displayed hypotheses. -/
private theorem rootProjectionInternal_ceil_nat_le_pred (m : ℕ) (hm : 0 < m) :
    sourceCeilLog2 (m : ℚ) ≤ m-1 := by
  apply rootProjectionInternal_ceil_nat_le_of_power m (m-1) hm
  have h := (m-1).lt_two_pow_self
  omega

/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionInternal_source_exponent_budget` under the displayed hypotheses. -/
private theorem rootProjectionInternal_source_exponent_budget (ctx : RootProjectionContext) (hm : 0 < rootProjectionDegree ctx.factor) :
    (rootProjectionHeight ctx.factor+rootProjectionMExponent ctx)*(rootProjectionDegree ctx.factor-1) ≤ rootProjectionAExponent ctx := by
  let m := rootProjectionDegree ctx.factor
  let ell := rootProjectionHeight ctx.factor
  have hlog := rootProjectionInternal_ceil_nat_le_pred m hm
  by_cases hm1 : m = 1
  · have hz : rootProjectionDegree ctx.factor-1 = 0 := by change m-1 = 0; omega
    simp only [rootProjectionAExponent,hz,Nat.mul_zero]
    exact Nat.le_refl 0
  · have hm2 : 2 ≤ m := by omega
    have hdiff : ell+(3*sourceCeilLog2 (m : ℚ)+ell+m*(ell+2)) ≤ m*m*(ell+2) := by
      have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
      have hlR : (sourceCeilLog2 (m : ℚ) : ℝ)+1 ≤ m := by
        exact_mod_cast (by omega : sourceCeilLog2 (m : ℚ)+1 ≤ m)
      have hpoly : (0 : ℝ) ≤ ((m : ℝ)-2)*((m : ℝ)+1)*(ell : ℝ) := by positivity
      have hmpos : (0 : ℝ) ≤ ((m : ℝ)-1)*(2*(m : ℝ)-3) :=
        mul_nonneg (by linarith) (by linarith)
      have hdR : (ell : ℝ)+(3*(sourceCeilLog2 (m : ℚ) : ℝ)+ell+(m : ℝ)*(ell+2)) ≤
          (m : ℝ)*m*(ell+2) := by nlinarith only [hlR,hpoly,hmpos]
      exact_mod_cast hdR
    have hmul := Nat.mul_le_mul_right (m-1) hdiff
    simpa only [rootProjectionAExponent,rootProjectionMExponent,m,ell] using hmul

/-! Actual coefficient list supplies BOTH analytic envelopes used at rootProjectionCap.
Separable generated factors and covered midpoint coordinates remain inputs;
this is not a Yun/Sturm or whole-proposer success theorem. -/
open Polynomial
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-- Construction for root Projection Internal factor Polynomial in the native root projection budget model. -/
private def rootProjectionInternal_factorPolynomial (ctx : RootProjectionContext) : ℤ[X] := ⟨⟨ctx.factor.toFinsupp⟩⟩

/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionInternal_factor_map` under the displayed hypotheses. -/
private theorem rootProjectionInternal_factor_map (ctx : RootProjectionContext) (n : ℕ) (a : Fin (n+2) → ℤ)
    (hfactor : ctx.factor = List.ofFn a) :
    (rootProjectionInternal_factorPolynomial ctx).map (Int.castRingHom ℂ) = rootIntegerPolynomial a := by
  change rootIntegerListPolynomial ctx.factor = rootIntegerPolynomial a
  rw [hfactor,rootIntegerListPolynomial_ofFn]

/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionInternal_factor_resultant_nonzero` under the displayed hypotheses. -/
private theorem rootProjectionInternal_factor_resultant_nonzero (ctx : RootProjectionContext) (n : ℕ) (a : Fin (n+2) → ℤ)
    (hfactor : ctx.factor = List.ofFn a) (ha : a (Fin.last (n+1)) ≠ 0)
    (hsep : (rootIntegerPolynomial a).Separable) :
    (rootProjectionInternal_factorPolynomial ctx).resultant (rootProjectionInternal_factorPolynomial ctx).derivative
      (rootProjectionInternal_factorPolynomial ctx).natDegree ((rootProjectionInternal_factorPolynomial ctx).natDegree-1) ≠ 0 := by
  let p := rootProjectionInternal_factorPolynomial ctx
  let f := p.map (Int.castRingHom ℂ)
  have hf : f = rootIntegerPolynomial a := rootProjectionInternal_factor_map ctx n a hfactor
  have hnd : f.natDegree = p.natDegree := Polynomial.natDegree_map_eq_of_injective Int.cast_injective p
  have hdpos : 0 < f.natDegree := by rw [hf,rootIntegerPolynomial_natDegree a ha]; omega
  have hder : f.derivative.natDegree = f.natDegree-1 :=
    Polynomial.natDegree_eq_of_degree_eq_some (Polynomial.degree_derivative hdpos.ne')
  have hNZ : f.resultant f.derivative ≠ 0 :=
    Polynomial.resultant_ne_zero f f.derivative (by simpa only [hf,Polynomial.Separable] using hsep)
  intro hzero
  apply hNZ
  rw [hder,hnd]
  dsimp only [f]
  rw [Polynomial.derivative_map,Polynomial.resultant_map_map]
  change ((rootProjectionInternal_factorPolynomial ctx).resultant (rootProjectionInternal_factorPolynomial ctx).derivative
    (rootProjectionInternal_factorPolynomial ctx).natDegree ((rootProjectionInternal_factorPolynomial ctx).natDegree-1) : ℂ) = 0
  rw [hzero,Int.cast_zero]

/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionFactor_derivative_lower` under the displayed hypotheses. -/
theorem rootProjectionFactor_derivative_lower (ctx : RootProjectionContext) (n : ℕ) (a : Fin (n+2) → ℤ)
    (hfactor : ctx.factor = List.ofFn a) (ha : a (Fin.last (n+1)) ≠ 0)
    (hsep : (rootIntegerPolynomial a).Separable)
    (z : ℂ) (hz : (rootIntegerPolynomial a).eval z = 0) :
    1/(2 : ℝ)^rootProjectionAExponent ctx ≤ ‖(rootIntegerPolynomial a).derivative.eval z‖ := by
  let p := rootProjectionInternal_factorPolynomial ctx
  let B : ℝ := (2 : ℝ)^rootProjectionHeight ctx.factor
  let M : ℝ := (2 : ℝ)^rootProjectionMExponent ctx
  have hf : p.map (Int.castRingHom ℂ) = rootIntegerPolynomial a := rootProjectionInternal_factor_map ctx n a hfactor
  have hd : p.natDegree = n+1 := by
    have h := Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℂ) Int.cast_injective p
    rw [hf,rootIntegerPolynomial_natDegree a ha] at h
    exact h.symm
  have hm : rootProjectionDegree ctx.factor = n+1 := by simp [rootProjectionDegree,hfactor]
  have hp : 0 < p.natDegree := by omega
  have hres := rootProjectionInternal_factor_resultant_nonzero ctx n a hfactor ha hsep
  have hlead : ‖(p.map (Int.castRingHom ℂ)).leadingCoeff‖ ≤ B := by
    rw [hf,Polynomial.leadingCoeff]
    change ‖(rootIntegerPolynomial a).coeff (rootIntegerPolynomial a).natDegree‖ ≤
      (2 : ℝ)^rootProjectionHeight ctx.factor
    rw [← rootIntegerListPolynomial_ofFn a, ← hfactor]
    exact rootProjectionInternal_coefficient_from_height ctx.factor _
  have hupper : ∀ w ∈ (p.map (Int.castRingHom ℂ)).roots,
      ‖(p.map (Int.castRingHom ℂ)).derivative.eval w‖ ≤ M := by
    intro w hw
    have hnz : rootIntegerPolynomial a ≠ 0 := by
      intro h
      have hdeg := rootIntegerPolynomial_natDegree a ha
      rw [h,Polynomial.natDegree_zero] at hdeg
      omega
    have hroot : (rootIntegerPolynomial a).eval w = 0 :=
      (Polynomial.mem_roots hnz).mp (by simpa only [hf] using hw)
    have hu := rootProjectionFactor_local_derivatives ctx n a hfactor ha w hroot 0 (by norm_num)
      w (Metric.mem_closedBall_self (le_refl 0))
    simpa only [hf] using hu.1
  have hbound := rootProjectionInternal_integer_resultant_derivative_lower p hp hres B M (by positivity) (by positivity)
    hlead hupper z (by simpa only [hf] using hz)
  have hexp := rootProjectionInternal_source_exponent_budget ctx (by omega)
  have hpower : B^(p.natDegree-1)*M^(p.natDegree-1) ≤ (2 : ℝ)^rootProjectionAExponent ctx := by
    calc
      _ = (2 : ℝ)^((rootProjectionHeight ctx.factor+rootProjectionMExponent ctx)*(rootProjectionDegree ctx.factor-1)) := by
        dsimp only [B,M]
        rw [← pow_mul,← pow_mul,← pow_add,hd,hm]
        congr 1
        ring
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) hexp
  have htmp := mul_le_mul_of_nonneg_right hpower
    (norm_nonneg ((p.map (Int.castRingHom ℂ)).derivative.eval z))
  have hnorm : 1 ≤ (2 : ℝ)^rootProjectionAExponent ctx * ‖(rootIntegerPolynomial a).derivative.eval z‖ := by
    simpa only [hf] using hbound.trans htmp
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^rootProjectionAExponent ctx)).mpr
  simpa only [mul_comm] using hnorm

/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionInternal_cap_horner_without_analytic_answers` under the displayed hypotheses. -/
private theorem rootProjectionInternal_cap_horner_without_analytic_answers (contexts : List RootProjectionContext) (bits : ℕ) (gap : ℚ)
    (hg : 0 < gap) (ctx : RootProjectionContext) (hctx : ctx ∈ contexts)
    (n : ℕ) (a : Fin (n+2) → ℤ) (ha : a (Fin.last (n+1)) ≠ 0)
    (hfactor : ctx.factor = List.ofFn a) (hsep : (rootIntegerPolynomial a).Separable)
    (z : ℂ) (hz : (rootIntegerPolynomial a).eval z = 0) (c : ℚ×ℚ)
    (hc : ‖rootRationalCoordinate c-z‖ ≤ (rootProjectionMidpointError contexts bits gap : ℝ)) :
    rootIntegerCoordinateBound (n+1)
      (rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c) (List.ofFn a))
      (rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c)
        (List.ofFn (rootIntegerDerivative n a))) (rootProjectionRadius contexts bits gap) ∧
    0 < max
      |(rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c)
        (List.ofFn (rootIntegerDerivative n a))).numerator.1|
      |(rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c)
        (List.ofFn (rootIntegerDerivative n a))).numerator.2| := by
  have hr := rootProjectionCap_radius_budgets contexts bits gap hg
  have hrad : (rootProjectionRadius contexts bits gap : ℝ) ≤ 1 := by exact_mod_cast hr.2.1
  have hr0 : (0 : ℝ) ≤ (rootProjectionRadius contexts bits gap : ℝ) := by exact_mod_cast hr.1.le
  have he : (rootProjectionMidpointError contexts bits gap : ℝ) ≤ 1 := by
    rw [rootProjectionInternal_midpoint_square]
    push_cast
    nlinarith
  have hu := rootProjectionFactor_local_derivatives ctx n a hfactor ha z hz (rootProjectionMidpointError contexts bits gap) he
  exact rootProjectionInternal_cap_actual_horner contexts bits gap hg ctx hctx n a ha hfactor z c hz hc
    (rootProjectionFactor_derivative_lower ctx n a hfactor ha hsep z hz)
    (fun w hw => (hu w hw).1) (fun w hw => (hu w hw).2)

/-! The actual Cartesian interval-midpoint rootProjectionCenter at the literal rootProjectionCap.
Interval coverage/width and generated-factor separability are still pending
Sturm/Yun obligations; no complete-proposer success is claimed here. -/
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-- At the source cap, a midpoint-close center passes the actual integer Horner test.
The same factor supplies its derivative bounds internally. -/
theorem rootProjectionCap_near_horner (contexts : List RootProjectionContext) (bits : ℕ) (gap : ℚ)
    (hg : 0 < gap) (ctx : RootProjectionContext) (hctx : ctx ∈ contexts)
    (n : ℕ) (a : Fin (n+2) → ℤ) (ha : a (Fin.last (n+1)) ≠ 0)
    (hfactor : ctx.factor = List.ofFn a) (hsep : (rootIntegerPolynomial a).Separable)
    (z : ℂ) (hz : (rootIntegerPolynomial a).eval z = 0) (c : ℚ×ℚ)
    (hc : ‖rootRationalCoordinate c-z‖ ≤ (rootProjectionMidpointError contexts bits gap : ℝ)) :
    rootIntegerCoordinateBound (n+1)
      (rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c) (List.ofFn a))
      (rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c)
        (List.ofFn (rootIntegerDerivative n a))) (rootProjectionRadius contexts bits gap) ∧
    0 < max
      |(rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c)
        (List.ofFn (rootIntegerDerivative n a))).numerator.1|
      |(rootCompactHorner (rootSharedNumerator c) (rootSharedDenominator c)
        (List.ofFn (rootIntegerDerivative n a))).numerator.2| :=
  rootProjectionInternal_cap_horner_without_analytic_answers contexts bits gap hg ctx hctx n a ha hfactor hsep z hz c hc

/-- Construction for root Projection Center in the native root projection budget model. -/
def rootProjectionCenter (ax bx ay byy : ℚ) : ℚ×ℚ := ((ax+bx)/2,(ay+byy)/2)

/-- The estimate `rootProjectionInternal_midpoint_error` retains the actual parameter, input-error and normalization budgets. -/
private theorem rootProjectionInternal_midpoint_error (ax bx ay byy e : ℚ) (z : ℂ)
    (hax : (ax : ℝ) ≤ z.re) (hbx : z.re ≤ (bx : ℝ))
    (hay : (ay : ℝ) ≤ z.im) (hby : z.im ≤ (byy : ℝ))
    (hx : bx-ax ≤ e) (hy : byy-ay ≤ e) :
    ‖rootRationalCoordinate (rootProjectionCenter ax bx ay byy)-z‖ ≤ (e : ℝ) := by
  have hxR : (bx : ℝ)-(ax : ℝ) ≤ (e : ℝ) := by exact_mod_cast hx
  have hyR : (byy : ℝ)-(ay : ℝ) ≤ (e : ℝ) := by exact_mod_cast hy
  have hr : |((ax : ℝ)+bx)/2-z.re| ≤ (e : ℝ)/2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hi : |((ay : ℝ)+byy)/2-z.im| ≤ (e : ℝ)/2 := abs_le.mpr ⟨by linarith,by linarith⟩
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  change |(((ax+bx)/2 : ℚ) : ℝ)-z.re|+|(((ay+byy)/2 : ℚ) : ℝ)-z.im| ≤ (e : ℝ)
  push_cast
  linarith

/-- The finite construction in `NativeRootProjectionBudget` satisfies `rootProjectionCap_candidate_passes` under the displayed hypotheses. -/
theorem rootProjectionCap_candidate_passes (contexts : List RootProjectionContext) (bits : ℕ) (gap : ℚ)
    (hg : 0 < gap) (ctx : RootProjectionContext) (hctx : ctx ∈ contexts)
    (n : ℕ) (a : Fin (n+2) → ℤ) (ha : a (Fin.last (n+1)) ≠ 0)
    (hfactor : ctx.factor = List.ofFn a) (hsep : (rootIntegerPolynomial a).Separable)
    (z : ℂ) (hz : (rootIntegerPolynomial a).eval z = 0)
    (ax bx ay byy : ℚ)
    (hax : (ax : ℝ) ≤ z.re) (hbx : z.re ≤ (bx : ℝ))
    (hay : (ay : ℝ) ≤ z.im) (hby : z.im ≤ (byy : ℝ))
    (hx : bx-ax ≤ rootProjectionMidpointError contexts bits gap)
    (hy : byy-ay ≤ rootProjectionMidpointError contexts bits gap) :
    rootIntegerCoordinateBound (n+1)
      (rootCompactHorner (rootSharedNumerator (rootProjectionCenter ax bx ay byy))
        (rootSharedDenominator (rootProjectionCenter ax bx ay byy)) (List.ofFn a))
      (rootCompactHorner (rootSharedNumerator (rootProjectionCenter ax bx ay byy))
        (rootSharedDenominator (rootProjectionCenter ax bx ay byy))
        (List.ofFn (rootIntegerDerivative n a))) (rootProjectionRadius contexts bits gap) ∧
    0 < max
      |(rootCompactHorner (rootSharedNumerator (rootProjectionCenter ax bx ay byy))
        (rootSharedDenominator (rootProjectionCenter ax bx ay byy))
        (List.ofFn (rootIntegerDerivative n a))).numerator.1|
      |(rootCompactHorner (rootSharedNumerator (rootProjectionCenter ax bx ay byy))
        (rootSharedDenominator (rootProjectionCenter ax bx ay byy))
        (List.ofFn (rootIntegerDerivative n a))).numerator.2| :=
  rootProjectionInternal_cap_horner_without_analytic_answers contexts bits gap hg ctx hctx n a ha hfactor hsep z hz
    (rootProjectionCenter ax bx ay byy) (rootProjectionInternal_midpoint_error ax bx ay byy _ z hax hbx hay hby hx hy)

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
