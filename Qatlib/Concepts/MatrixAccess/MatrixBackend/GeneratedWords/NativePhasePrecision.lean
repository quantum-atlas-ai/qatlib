/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeSqrtInterval
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

/-! Output-value model of neumann_shift_parameters.phase_parameters: the
actual integer-root midpoint, sign/max normalization and rational Cayley data.
The universal bound includes zero and both sign branches. It does not certify
the whole Python interpreter, preparation stream or classical bit time. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib

/-- Construction for real Cayley in the native phase precision model. -/
private def realCayley (t : ℝ) : ℂ := ⟨(1-t^2)/(1+t^2),2*t/(1+t^2)⟩

/-- The finite construction in `NativePhasePrecision` satisfies `realCayley_norm` under the displayed hypotheses. -/
private theorem realCayley_norm (t : ℝ) : ‖realCayley t‖=1 := by
  have ht : 1+t^2≠0 := by positivity
  have hs : ‖realCayley t‖^2=1 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    dsimp [realCayley]
    field_simp [ht]
    ring
  nlinarith [norm_nonneg (realCayley t)]

/-- The finite construction in `NativePhasePrecision` satisfies `realCayley_chord` under the displayed hypotheses. -/
private theorem realCayley_chord (s t : ℝ) : ‖realCayley s-realCayley t‖≤2*|s-t| := by
  have hs : 1+s^2≠0 := by positivity
  have ht : 1+t^2≠0 := by positivity
  have he : ‖realCayley s-realCayley t‖^2*((1+s^2)*(1+t^2))=4*(s-t)^2 := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp only [Complex.sub_re,Complex.sub_im]
    dsimp [realCayley]
    field_simp [hs,ht]
    ring
  have hd : 1≤(1+s^2)*(1+t^2) := by nlinarith [sq_nonneg s,sq_nonneg t,mul_nonneg (sq_nonneg s) (sq_nonneg t)]
  have hb : ‖realCayley s-realCayley t‖^2≤4*(s-t)^2 := by
    nlinarith [mul_nonneg (sq_nonneg ‖realCayley s-realCayley t‖) (sub_nonneg.mpr hd)]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0≤2*|s-t|)).mp
  simpa only [mul_pow,show (2 : ℝ)^2=4 by norm_num,sq_abs] using hb

/-- The finite construction in `NativePhasePrecision` satisfies `rationalCayley_value` under the displayed hypotheses. -/
private theorem rationalCayley_value (t : ℚ) : gaussianRatComplex (cayleyRat t)=realCayley (t : ℝ) := by
  have hc : ((cayleyRat t).1 : ℝ)=(1-(t : ℝ)^2)/(1+(t : ℝ)^2) := by
    dsimp [cayleyRat]; push_cast; rfl
  have hs : ((cayleyRat t).2 : ℝ)=2*(t : ℝ)/(1+(t : ℝ)^2) := by
    dsimp [cayleyRat]; push_cast; rfl
  unfold gaussianRatComplex
  rw [←Complex.ofReal_ratCast ((cayleyRat t).1),←Complex.ofReal_ratCast ((cayleyRat t).2),hc,hs]
  exact Complex.re_add_im (realCayley (t : ℝ))


/-- Construction for phase Root Midpoint in the native phase precision model. -/
private def phaseRootMidpoint (x y : ℚ) (p : ℕ) : ℚ :=
  let b := nativeSqrtInterval (x*x+y*y) (p+4)
  (b.1+b.2.1)/2

/-- Construction for normalized Phase Pair in the native phase precision model. -/
private def normalizedPhasePair (x y : ℚ) (p : ℕ) : GaussianRat :=
  cayleyRat (y/(phaseRootMidpoint x y p+x))

/-- The finite construction in `NativePhasePrecision` satisfies `realCayley_ratio` under the displayed hypotheses. -/
private theorem realCayley_ratio (x y R : ℝ) (hx : 0≤x) (hR : 0<R)
    (hR2 : R^2=x^2+y^2) : realCayley (y/(R+x))=⟨x/R,y/R⟩ := by
  have hd : R+x≠0 := by positivity
  have hplus : 1+(y/(R+x))^2=2*R/(R+x) := by
    field_simp [hd]
    nlinarith
  have hminus : 1-(y/(R+x))^2=2*x/(R+x) := by
    field_simp [hd]
    nlinarith
  apply Complex.ext
  · change (1-(y/(R+x))^2)/(1+(y/(R+x))^2)=x/R
    rw [hplus,hminus]
    field_simp [hd,hR.ne']
  · change (2*(y/(R+x)))/(1+(y/(R+x))^2)=y/R
    rw [hplus]
    field_simp [hd,hR.ne']

/-- The finite construction in `NativePhasePrecision` satisfies `gaussianRatComplex_div_real` under the displayed hypotheses. -/
private theorem gaussianRatComplex_div_real (x y : ℚ) (R : ℝ) :
    gaussianRatComplex (x,y)/(R : ℂ)=⟨(x : ℝ)/R,(y : ℝ)/R⟩ := by
  have hz : gaussianRatComplex (x,y)=((x : ℝ) : ℂ)+((y : ℝ) : ℂ)*Complex.I := by
    dsimp [gaussianRatComplex]
  calc
    _ = (((x : ℝ) : ℂ)/(R : ℂ))+(((y : ℝ) : ℂ)/(R : ℂ))*Complex.I := by rw [hz]; ring
    _ = (((x : ℝ)/R : ℝ) : ℂ)+(((y : ℝ)/R : ℝ) : ℂ)*Complex.I := by rw [←Complex.ofReal_div,←Complex.ofReal_div]
    _ = _ := Complex.re_add_im (Complex.mk ((x : ℝ)/R) ((y : ℝ)/R))

/-- The finite construction in `NativePhasePrecision` satisfies `phase_halfangle_difference` under the displayed hypotheses. -/
private theorem phase_halfangle_difference (y m R x : ℝ) (hy : |y|≤1)
    (hm : 1≤ m) (hR : 1≤R) (hx : 0≤x) :
    |y/(m+x)-y/(R+x)|≤|m-R| := by
  have hm0 : 0< m+x := by linarith
  have hR0 : 0<R+x := by linarith
  have hd : 1≤(m+x)*(R+x) := by nlinarith [mul_nonneg (by linarith : 0≤ m+x-1) (by linarith : 0≤R+x-1)]
  have he : y/(m+x)-y/(R+x)=y*(R-m)/((m+x)*(R+x)) := by field_simp [hm0.ne',hR0.ne']; ring
  rw [he,abs_div,abs_mul,abs_of_pos (mul_pos hm0 hR0),abs_sub_comm R m]
  apply (div_le_iff₀ (mul_pos hm0 hR0)).mpr
  exact (mul_le_mul_of_nonneg_right hy (abs_nonneg _)).trans
    (by nlinarith [mul_nonneg (abs_nonneg (m-R)) (sub_nonneg.mpr hd)])

/-- The estimate `normalizedPhasePair_error` retains the actual parameter, input-error and normalization budgets. -/
private theorem normalizedPhasePair_error (x y : ℚ) (p : ℕ)
    (hx : 0≤x) (hy : |y|≤1) (hq : 1≤x*x+y*y) :
    ‖gaussianRatComplex (normalizedPhasePair x y p)-
      gaussianRatComplex (x,y)/(Real.sqrt ((x*x+y*y : ℚ) : ℝ) : ℂ)‖≤1/(16*(2 : ℝ)^p) := by
  let q := x*x+y*y
  let R := Real.sqrt (q : ℝ)
  let m := phaseRootMidpoint x y p
  have hq0 : 0≤q := by dsimp [q]; positivity
  obtain ⟨hl,hh,_,herr⟩ := nativeSqrtInterval_real q (p+4) hq0
  obtain ⟨_,horder,_,_,_,_⟩ := nativeSqrtInterval_rational q (p+4) hq0
  have hl1 : 1≤(nativeSqrtInterval q (p+4)).1 := nativeSqrtInterval_lower_one q (p+4) hq
  have hm : 1≤ m := by dsimp [m,phaseRootMidpoint]; linarith
  have hmR : (1 : ℝ)≤ m := by exact_mod_cast hm
  have hRR : 1≤R := by
    have hqr : (1 : ℝ)≤q := by exact_mod_cast hq
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hqr
  have hR2 : R^2=(x : ℝ)^2+(y : ℝ)^2 := by
    dsimp [R]
    rw [Real.sq_sqrt (show (0 : ℝ)≤q by exact_mod_cast hq0)]
    dsimp [q]
    push_cast
    ring
  have hxR : (0 : ℝ)≤x := by exact_mod_cast hx
  have hyR : |(y : ℝ)|≤1 := by exact_mod_cast hy
  have hid : gaussianRatComplex (x,y)/(R : ℂ)=realCayley ((y : ℝ)/(R+(x : ℝ))) := by
    rw [realCayley_ratio (x : ℝ) (y : ℝ) R hxR (by linarith) hR2]
    exact gaussianRatComplex_div_real x y R
  have hmid : |(m : ℝ)-R|≤1/(32*(2 : ℝ)^p) := by
    change |(m : ℝ)-R|≤_ at herr
    have he : (1 : ℝ)/(2*2^(p+4))=1/(32*2^p) := by rw [pow_add]; norm_num; ring
    rw [he] at herr
    exact herr
  have harg : ((y/(m+x) : ℚ) : ℝ)=(y : ℝ)/((m : ℝ)+(x : ℝ)) := by push_cast; rfl
  change ‖gaussianRatComplex (cayleyRat (y/(m+x)))-gaussianRatComplex (x,y)/(R : ℂ)‖≤_
  rw [rationalCayley_value,harg,hid]
  calc
    _ ≤ 2*|(y : ℝ)/((m : ℝ)+(x : ℝ))-(y : ℝ)/(R+(x : ℝ))| := realCayley_chord _ _
    _ ≤ 2*|(m : ℝ)-R| := mul_le_mul_of_nonneg_left (phase_halfangle_difference _ _ _ _ hyR hmR hRR hxR) (by norm_num)
    _ ≤ 2*(1/(32*(2 : ℝ)^p)) := mul_le_mul_of_nonneg_left hmid (by norm_num)
    _ = _ := by ring

/-- The finite construction in `NativePhasePrecision` satisfies `gaussianRatComplex_norm` under the displayed hypotheses. -/
private theorem gaussianRatComplex_norm (x y : ℚ) :
    ‖gaussianRatComplex (x,y)‖=Real.sqrt ((x*x+y*y : ℚ) : ℝ) := by
  have hz : gaussianRatComplex (x,y)=Complex.mk (x : ℝ) (y : ℝ) := by
    simpa only [Complex.ofReal_one,div_one] using gaussianRatComplex_div_real x y 1
  rw [hz,Complex.norm_eq_sqrt_sq_add_sq]
  congr 1
  push_cast
  ring

/-- The finite construction in `NativePhasePrecision` satisfies `gaussianRatComplex_div_pair` under the displayed hypotheses. -/
private theorem gaussianRatComplex_div_pair (x y m : ℚ) :
    gaussianRatComplex (x/m,y/m)=gaussianRatComplex (x,y)/(m : ℂ) := by
  dsimp [gaussianRatComplex]
  push_cast
  ring

/-- The finite construction in `NativePhasePrecision` satisfies `gaussianRatComplex_unit_scale` under the displayed hypotheses. -/
private theorem gaussianRatComplex_unit_scale (x y m : ℚ) (hm : 0< m) :
    gaussianRatComplex (x/m,y/m)/(‖gaussianRatComplex (x/m,y/m)‖ : ℂ)=
      gaussianRatComplex (x,y)/(‖gaussianRatComplex (x,y)‖ : ℂ) := by
  have hmR : (0 : ℝ)< m := by exact_mod_cast hm
  have hmC : (m : ℂ)≠0 := by exact_mod_cast hm.ne'
  have hnormm : ‖(m : ℂ)‖=(m : ℝ) := by
    rw [←Complex.ofReal_ratCast m,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hmR]
  rw [gaussianRatComplex_div_pair,norm_div,hnormm]
  have hden : ((‖gaussianRatComplex (x,y)‖/(m : ℝ) : ℝ) : ℂ)=
      (‖gaussianRatComplex (x,y)‖ : ℂ)/(m : ℂ) := by
    rw [Complex.ofReal_div,Complex.ofReal_ratCast m]
  rw [hden]
  by_cases hz : (‖gaussianRatComplex (x,y)‖ : ℂ)=0
  · simp [hz]
  · field_simp [hmC,hz]

/-- Construction for positive Phase Pair in the native phase precision model. -/
private def positivePhasePair (x y : ℚ) (p : ℕ) : GaussianRat :=
  let m := max |x| |y|
  normalizedPhasePair (x/m) (y/m) p

/-- The estimate `positivePhasePair_error` retains the actual parameter, input-error and normalization budgets. -/
private theorem positivePhasePair_error (x y : ℚ) (p : ℕ) (hx : 0≤x) (hnz : x≠0 ∨ y≠0) :
    ‖gaussianRatComplex (positivePhasePair x y p)-
      gaussianRatComplex (x,y)/(‖gaussianRatComplex (x,y)‖ : ℂ)‖≤1/(16*(2 : ℝ)^p) := by
  let m := max |x| |y|
  have hm : 0< m := by
    rcases hnz with hx' | hy'
    · exact (abs_pos.mpr hx').trans_le (le_max_left _ _)
    · exact (abs_pos.mpr hy').trans_le (le_max_right _ _)
  have hnx : 0≤x/m := div_nonneg hx hm.le
  have hny : |y/m|≤1 := by
    rw [abs_div,abs_of_pos hm]
    apply (div_le_iff₀ hm).mpr
    simpa only [one_mul] using le_max_right |x| |y|
  have hm2 : m^2≤x^2+y^2 := by
    dsimp [m]
    rcases le_total |x| |y| with hxy | hyx
    · rw [max_eq_right hxy,sq_abs]
      nlinarith [sq_nonneg x]
    · rw [max_eq_left hyx,sq_abs]
      nlinarith [sq_nonneg y]
  have hnq : 1≤(x/m)*(x/m)+(y/m)*(y/m) := by
    have he : (x/m)*(x/m)+(y/m)*(y/m)=(x^2+y^2)/m^2 := by ring
    rw [he]
    exact (le_div_iff₀ (sq_pos_of_pos hm)).mpr (by simpa only [one_mul] using hm2)
  have he := normalizedPhasePair_error (x/m) (y/m) p hnx hny hnq
  rw [←gaussianRatComplex_norm,gaussianRatComplex_unit_scale x y m hm] at he
  exact he

/-- Construction for native Phase Pair in the native phase precision model. -/
def nativePhasePair (x y : ℚ) (p : ℕ) : GaussianRat :=
  if x=0 ∧ y=0 then (1,0)
  else if x<0 then
    let v := positivePhasePair (-x) (-y) p
    (-v.1,-v.2)
  else positivePhasePair x y p

/-- Construction for native Phase Target in the native phase precision model. -/
def nativePhaseTarget (x y : ℚ) : ℂ :=
  if x=0 ∧ y=0 then 1 else gaussianRatComplex (x,y)/(‖gaussianRatComplex (x,y)‖ : ℂ)

/-- The finite construction in `NativePhasePrecision` satisfies `gaussianRatComplex_neg_pair` under the displayed hypotheses. -/
private theorem gaussianRatComplex_neg_pair (v : GaussianRat) :
    gaussianRatComplex (-v.1,-v.2)=-gaussianRatComplex v := by
  dsimp [gaussianRatComplex]
  push_cast
  ring

/-- The estimate `nativePhasePair_error` retains the actual parameter, input-error and normalization budgets. -/
theorem nativePhasePair_error (x y : ℚ) (p : ℕ) :
    ‖gaussianRatComplex (nativePhasePair x y p)-nativePhaseTarget x y‖≤1/(16*(2 : ℝ)^p) := by
  by_cases hz : x=0 ∧ y=0
  · simp [nativePhasePair,nativePhaseTarget,hz,gaussianRatComplex]
  · unfold nativePhasePair nativePhaseTarget
    rw [ite_eq_right hz,ite_eq_right hz]
    by_cases hx : x<0
    · rw [ite_eq_left hx]
      have he := positivePhasePair_error (-x) (-y) p (by linarith) (Or.inl (by linarith))
      have hn : gaussianRatComplex (-x,-y)=-gaussianRatComplex (x,y) := gaussianRatComplex_neg_pair (x,y)
      rw [hn,norm_neg,neg_div] at he
      rw [gaussianRatComplex_neg_pair]
      have heq : -gaussianRatComplex (positivePhasePair (-x) (-y) p)-
          gaussianRatComplex (x,y)/(‖gaussianRatComplex (x,y)‖ : ℂ)=
          -(gaussianRatComplex (positivePhasePair (-x) (-y) p)+gaussianRatComplex (x,y)/(‖gaussianRatComplex (x,y)‖ : ℂ)) := by ring
      rw [heq,norm_neg]
      simpa only [sub_neg_eq_add] using he
    · rw [ite_eq_right hx]
      exact positivePhasePair_error x y p (le_of_not_gt hx) (by tauto)

/-- The finite construction in `NativePhasePrecision` satisfies `nativePhasePair_norm` under the displayed hypotheses. -/
theorem nativePhasePair_norm (x y : ℚ) (p : ℕ) : ‖gaussianRatComplex (nativePhasePair x y p)‖=1 := by
  have hn (x y : ℚ) : ‖gaussianRatComplex (positivePhasePair x y p)‖=1 := by
    unfold positivePhasePair normalizedPhasePair
    exact (rational_cayley_unit_phase_and_angle _).1
  unfold nativePhasePair
  split_ifs with hz hx
  · simp [gaussianRatComplex]
  · rw [gaussianRatComplex_neg_pair,norm_neg]
    exact hn _ _
  · exact hn _ _

/-- The finite construction in `NativePhasePrecision` satisfies `nativePhasePair_circle` under the displayed hypotheses. -/
theorem nativePhasePair_circle (x y : ℚ) (p : ℕ) :
    (nativePhasePair x y p).1*(nativePhasePair x y p).1+
      (nativePhasePair x y p).2*(nativePhasePair x y p).2=1 := by
  have hn (x y : ℚ) : (positivePhasePair x y p).1*(positivePhasePair x y p).1+
      (positivePhasePair x y p).2*(positivePhasePair x y p).2=1 := by
    unfold positivePhasePair normalizedPhasePair
    exact (Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle.half _).norm
  unfold nativePhasePair
  split_ifs with hz hx
  · norm_num
  · dsimp only
    have hh := hn (-x) (-y)
    nlinarith
  · exact hn x y

/-- Construction for native Phase Circle in the native phase precision model. -/
def nativePhaseCircle (x y : ℚ) (p : ℕ) : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle :=
  ⟨(nativePhasePair x y p).1,(nativePhasePair x y p).2,nativePhasePair_circle x y p⟩

/-- The estimate `nativePhaseCircle_error` retains the actual parameter, input-error and normalization budgets. -/
theorem nativePhaseCircle_error (x y : ℚ) (p : ℕ) :
    ‖gaussianRatComplex ((nativePhaseCircle x y p).c,(nativePhaseCircle x y p).s)-nativePhaseTarget x y‖≤
      1/(16*(2 : ℝ)^p) := nativePhasePair_error x y p

/-- The rational half-angle datum can be compared with an arbitrary real
ideal half-angle without installing the ideal value in the program. -/
theorem nativeHalfCircle_error (q : ℚ) (t : ℝ) :
    ‖gaussianRatComplex (cayleyRat q)-
      (Complex.mk ((1-t^2)/(1+t^2)) (2*t/(1+t^2)))‖≤2*|(q : ℝ)-t| := by
  rw [rationalCayley_value]
  exact realCayley_chord _ _

/-- The coordinate residual used by finite scalar certificates is controlled
by the same actual phase value. -/
theorem nativePhaseCircle_coordinate_error (x y : ℚ) (p : ℕ) :
    let d := gaussianRatComplex ((nativePhaseCircle x y p).c,(nativePhaseCircle x y p).s)-nativePhaseTarget x y
    |d.re|+|d.im|≤1/(8*(2 : ℝ)^p) := by
  intro d
  have hr := Complex.abs_re_le_norm d
  have hi := Complex.abs_im_le_norm d
  have hn := nativePhaseCircle_error x y p
  change ‖d‖≤_ at hn
  have he : (1 : ℝ)/(8*2^p)=2*(1/(16*2^p)) := by ring
  rw [he]
  linarith
end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
