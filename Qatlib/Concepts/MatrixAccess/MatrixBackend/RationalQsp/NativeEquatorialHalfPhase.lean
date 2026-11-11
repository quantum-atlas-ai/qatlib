/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativePhaseOutputRounding
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

/-! A finite rational half phase for an equatorial projector coordinate.
This converts supplied unit Gaussian equatorial data; it does not implement
Haah's completion/factorization or provide a half-angle signal oracle. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords

open Qatlib.Concepts.NativeNumerics.PhaseSynthesis

/-- The finite construction in `NativeEquatorialHalfPhase` satisfies `nativePhaseTarget_norm` under the displayed hypotheses. -/
theorem nativePhaseTarget_norm (x y : ℚ) : ‖nativePhaseTarget x y‖=1 := by
  by_cases hz : x=0 ∧ y=0
  · simp [nativePhaseTarget,hz]
  · have hn : gaussianRatComplex (x,y)≠0 := by
      intro h
      have hr := congrArg Complex.re h
      have hi := congrArg Complex.im h
      simp [gaussianRatComplex] at hr hi
      exact hz ⟨by exact_mod_cast hr,by exact_mod_cast hi⟩
    simp [nativePhaseTarget,hz,Complex.norm_real,ne_of_gt (norm_pos_iff.mpr hn)]

/-- The finite construction in `NativeEquatorialHalfPhase` satisfies `positive_half_phase_square` under the displayed hypotheses. -/
private theorem positive_half_phase_square (x y : ℚ) (hx : 0≤x)
    (hq : x*x+y*y=1) :
    (nativePhaseTarget (1+x) y)^2=gaussianRatComplex (x,y) := by
  have hxR : (0 : ℝ)≤x := by exact_mod_cast hx
  have hqR : (x : ℝ)*(x : ℝ)+(y : ℝ)*(y : ℝ)=1 := by exact_mod_cast hq
  let v := gaussianRatComplex (1+x,y)
  have hv : ‖v‖^2=2*(1+(x : ℝ)) := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    simp [v,gaussianRatComplex,Complex.mul_re,Complex.mul_im]

    nlinarith
  have hvC : (‖v‖ : ℂ)^2=((2*(1+(x : ℝ)) : ℝ) : ℂ) := by exact_mod_cast hv
  have hid : v^2=((2*(1+(x : ℝ)) : ℝ) : ℂ)*gaussianRatComplex (x,y) := by
    apply Complex.ext
    · simp [v,gaussianRatComplex,pow_two,Complex.mul_re]

      nlinarith
    · simp [v,gaussianRatComplex,pow_two,Complex.mul_im]

      ring
  have hnz : ¬(1+x=0 ∧ y=0) := by intro h; linarith [h.1]
  rw [nativePhaseTarget,ite_eq_right hnz]
  change (v/(‖v‖ : ℂ))^2=_
  rw [div_pow,hvC,hid]
  have hd : ((2*(1+(x : ℝ)) : ℝ) : ℂ)≠0 := by
    exact_mod_cast (by positivity : (2*(1+(x : ℝ)) : ℝ)≠0)
  exact mul_div_cancel_left₀ _ hd

/-- Construction for native Equatorial Half Target in the native equatorial half phase model. -/
def nativeEquatorialHalfTarget (q : GaussianRat) : ℂ :=
  if q.1<0 then Complex.I*nativePhaseTarget (1-q.1) (-q.2)
  else nativePhaseTarget (1+q.1) q.2

/-- Construction for native Equatorial Half Phase in the native equatorial half phase model. -/
def nativeEquatorialHalfPhase (q : GaussianRat) (p : ℕ) : GaussianRat :=
  if q.1<0 then gmul (0,1) (nativePhasePair (1-q.1) (-q.2) p)
  else nativePhasePair (1+q.1) q.2 p

/-- The finite construction in `NativeEquatorialHalfPhase` satisfies `nativeEquatorialHalfTarget_norm` under the displayed hypotheses. -/
theorem nativeEquatorialHalfTarget_norm (q : GaussianRat) :
    ‖nativeEquatorialHalfTarget q‖=1 := by
  unfold nativeEquatorialHalfTarget
  split_ifs <;> simp [nativePhaseTarget_norm]

/-- The finite construction in `NativeEquatorialHalfPhase` satisfies `nativeEquatorialHalfTarget_square` under the displayed hypotheses. -/
theorem nativeEquatorialHalfTarget_square (q : GaussianRat)
    (hq : q.1*q.1+q.2*q.2=1) :
    (nativeEquatorialHalfTarget q)^2=gaussianRatComplex q := by
  unfold nativeEquatorialHalfTarget
  split_ifs with hx
  · rw [mul_pow,Complex.I_sq]
    have hh := positive_half_phase_square (-q.1) (-q.2) (by linarith) (by nlinarith [hq])
    have he : 1-q.1=1+(-q.1) := by ring
    rw [he,hh]
    simp [gaussianRatComplex]

    ring
  · exact positive_half_phase_square q.1 q.2 (le_of_not_gt hx) hq

/-- The finite construction in `NativeEquatorialHalfPhase` satisfies `nativeEquatorialHalfPhase_norm` under the displayed hypotheses. -/
theorem nativeEquatorialHalfPhase_norm (q : GaussianRat) (p : ℕ) :
    ‖gaussianRatComplex (nativeEquatorialHalfPhase q p)‖=1 := by
  unfold nativeEquatorialHalfPhase
  split_ifs
  · rw [complex_gmul,norm_mul,nativePhasePair_norm]
    norm_num [gaussianRatComplex]
  · exact nativePhasePair_norm _ _ _

/-- The estimate `nativeEquatorialHalfPhase_error` retains the actual parameter, input-error and normalization budgets. -/
theorem nativeEquatorialHalfPhase_error (q : GaussianRat) (p : ℕ) :
    ‖gaussianRatComplex (nativeEquatorialHalfPhase q p)-nativeEquatorialHalfTarget q‖≤
      1/(16*(2 : ℝ)^p) := by
  unfold nativeEquatorialHalfPhase nativeEquatorialHalfTarget
  split_ifs
  · rw [complex_gmul]
    have hi : gaussianRatComplex ((0,1) : GaussianRat)=Complex.I := by norm_num [gaussianRatComplex]
    rw [hi,←mul_sub,norm_mul,Complex.norm_I,one_mul]
    exact nativePhasePair_error _ _ _
  · exact nativePhasePair_error _ _ _

/-- The actual rational output has a unit square that approximates the supplied
equatorial coordinate, including q=-1 and both sign charts without division
by 1+Re(q) near zero. -/
theorem nativeEquatorialHalfPhase_square_error (q : GaussianRat) (p : ℕ)
    (hq : q.1*q.1+q.2*q.2=1) :
    ‖(gaussianRatComplex (nativeEquatorialHalfPhase q p))^2-gaussianRatComplex q‖≤
      1/(8*(2 : ℝ)^p) := by
  have h := phase_power_error _ _ _ (nativeEquatorialHalfPhase_norm q p)
    (nativeEquatorialHalfTarget_norm q) (nativeEquatorialHalfPhase_error q p) 2
  rw [nativeEquatorialHalfTarget_square q hq] at h
  norm_num only [Nat.cast_ofNat] at h
  convert h using 1; ring

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
