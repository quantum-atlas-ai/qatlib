/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.RationalFlow.PhaseSamples

/-! # The finite rational phase-log execution and its real-angle semantics -/

set_option autoImplicit false
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Abbreviation for Rational Circle Sample in the Hopf Atlas construction. -/
abbrev RationalCircleSample := ℚ × ℚ

/-- Definition of phase Ratio Re in the Hopf Atlas construction. -/
def phaseRatioRe (previous current : RationalCircleSample) : ℚ := current.1*previous.1+current.2*previous.2
/-- Definition of phase Ratio Im in the Hopf Atlas construction. -/
def phaseRatioIm (previous current : RationalCircleSample) : ℚ := current.2*previous.1-current.1*previous.2

/-- Definition of rational Phase Step in the Hopf Atlas construction. -/
def rationalPhaseStep (previous current : RationalCircleSample) (tolerance : ℚ) : Option RationalScalarResult :=
  let re := phaseRatioRe previous current
  let im := phaseRatioIm previous current
  if 0<re ∧ |im/re| ≤ (1/2 : ℚ) then some (rationalArctan (im/re) tolerance) else none

/-- Data and hypotheses for Phase Log State in the Hopf Atlas construction. -/
structure PhaseLogState where
  previous : RationalCircleSample
  value : ℚ
  arithmeticError : ℚ
  terms : ℕ
  deriving Repr, DecidableEq

/-- Definition of rational Phase Prefix in the Hopf Atlas construction. -/
def rationalPhasePrefix (tolerance : ℚ) (samples : ℕ → RationalCircleSample) : ℕ → Option PhaseLogState
  | 0 => some ⟨(1,0),0,0,0⟩
  | n+1 =>
    match rationalPhasePrefix tolerance samples n with
    | none => none
    | some state =>
      let current := samples (n+1)
      match rationalPhaseStep state.previous current tolerance with
      | none => none
      | some increment => some ⟨current,state.value+increment.value,
          state.arithmeticError+increment.error,state.terms+increment.terms⟩

/-- Definition of phase Log Steps in the Hopf Atlas construction. -/
def phaseLogSteps (endpoint bound : ℚ) : ℕ := max 1 (Nat.ceil (8*endpoint*bound))
/-- Definition of phase Log Precision in the Hopf Atlas construction. -/
def phaseLogPrecision (tolerance : ℚ) : ℕ := max 6 (Nat.clog 2 (Nat.ceil (8/tolerance)))

/-- Definition of phase Log Samples in the Hopf Atlas construction. -/
def phaseLogSamples (oracle : ℚ × ℕ → RationalCircleSample) (endpoint : ℚ) (steps precision : ℕ)
    (j : ℕ) : RationalCircleSample :=
  if j=0 then (1,0) else oracle (endpoint*((j : ℚ)/(steps : ℚ)),precision)

/-- Data and hypotheses for Rational Phase Log Result in the Hopf Atlas construction. -/
structure RationalPhaseLogResult where
  value : ℚ
  arithmeticError : ℚ
  errorBound : ℚ
  steps : ℕ
  precision : ℕ
  terms : ℕ
  deriving Repr, DecidableEq

/-- Definition of rational Phase Log in the Hopf Atlas construction. -/
def rationalPhaseLog (oracle : ℚ × ℕ → RationalCircleSample) (endpoint bound tolerance : ℚ) :
    Option RationalPhaseLogResult :=
  let steps := phaseLogSteps endpoint bound
  let b := phaseLogPrecision tolerance
  (rationalPhasePrefix (tolerance/(2*(steps : ℚ))) (phaseLogSamples oracle endpoint steps b) steps).map
    (fun r => ⟨r.value,r.arithmeticError,2*(2^b : ℚ)⁻¹+r.arithmeticError,steps,b,r.terms⟩)

/-- Original `phaseLogSteps_pos` guarantee for the `PhaseLogProgram` construction; the complete source hypotheses are retained. -/
theorem phaseLogSteps_pos (endpoint bound : ℚ) : 0<phaseLogSteps endpoint bound :=
  Nat.lt_of_lt_of_le (by decide) (le_max_left _ _)

/-- Original `phaseLogSteps_bound` guarantee for the `PhaseLogProgram` construction; the complete source hypotheses are retained. -/
theorem phaseLogSteps_bound (endpoint bound : ℚ) : 8*endpoint*bound ≤ (phaseLogSteps endpoint bound : ℚ) :=
  (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 1 (Nat.ceil (8*endpoint*bound))))

/-- Original `phaseLogPrecision_budget` guarantee for the `PhaseLogProgram` construction; the complete source hypotheses are retained. -/
theorem phaseLogPrecision_budget (tau : ℚ) (ht : 0<tau) : (2^phaseLogPrecision tau : ℚ)⁻¹ ≤ tau/8 := by
  have hp : Nat.ceil (8/tau) ≤ 2^phaseLogPrecision tau :=
    (Nat.clog_le_iff_le_pow (by decide)).mp (le_max_right _ _)
  have h : 8/tau ≤ (2^phaseLogPrecision tau : ℚ) := (Nat.le_ceil _).trans (by exact_mod_cast hp)
  apply (inv_le_iff_one_le_mul₀ (by positivity : (0 : ℚ)<2^phaseLogPrecision tau)).mpr
  have hh := (div_le_iff₀ ht).mp h
  nlinarith

/-- Original `phaseLogPrecision_small` guarantee for the `PhaseLogProgram` construction; the complete source hypotheses are retained. -/
theorem phaseLogPrecision_small (tau : ℚ) : (2^phaseLogPrecision tau : ℚ)⁻¹ ≤ (1/64 : ℚ) := by
  have hp : (64 : ℚ) ≤ 2^phaseLogPrecision tau := by
    exact_mod_cast Nat.pow_le_pow_right (by decide : 0<2) (le_max_left 6 (Nat.clog 2 (Nat.ceil (8/tau))))
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℚ)<64) hp

noncomputable section
open scoped ComplexConjugate

/-- Definition of rational Circle Cast in the Hopf Atlas construction. -/
def rationalCircleCast (a : RationalCircleSample) : ℂ := ⟨(a.1 : ℝ),(a.2 : ℝ)⟩

/-- Original `rationalCircleCast_ratio_re` guarantee for the `PhaseLogProgram` construction; the complete source hypotheses are retained. -/
theorem rationalCircleCast_ratio_re (previous current : RationalCircleSample) :
    (phaseRatioRe previous current : ℝ)=(rationalCircleCast current*conj (rationalCircleCast previous)).re := by
  simp [phaseRatioRe,rationalCircleCast]

/-- Original `rationalCircleCast_ratio_im` guarantee for the `PhaseLogProgram` construction; the complete source hypotheses are retained. -/
theorem rationalCircleCast_ratio_im (previous current : RationalCircleSample) :
    (phaseRatioIm previous current : ℝ)=(rationalCircleCast current*conj (rationalCircleCast previous)).im := by
  simp [phaseRatioIm,rationalCircleCast]
  ring

/-- Original `rationalCircleCast_one` guarantee for the `PhaseLogProgram` construction; the complete source hypotheses are retained. -/
@[simp] theorem rationalCircleCast_one : rationalCircleCast (1,0)=1 := by
  apply Complex.ext <;> norm_num [rationalCircleCast]

/-- Original `rationalPhaseStep_spec` guarantee for the `PhaseLogProgram` construction; the complete source hypotheses are retained. -/
theorem rationalPhaseStep_spec (previous current : RationalCircleSample) (theta0 theta1 e : ℝ)
    (tau : ℚ) (htau : 0<tau) (he : 0 ≤ e) (he64 : e ≤ 1/64) (hstep : |theta1-theta0| ≤ 1/8)
    (hp : ‖rationalCircleCast previous-complexPhase theta0‖ ≤ e)
    (hc : ‖rationalCircleCast current-complexPhase theta1‖ ≤ e) :
    ∃ r, rationalPhaseStep previous current tau=some r ∧
      |(r.value : ℝ)-((theta1-theta0)+sampleAngleError (rationalCircleCast current) theta1-
        sampleAngleError (rationalCircleCast previous) theta0)| ≤ (r.error : ℝ) ∧
      r.error ≤ tau ∧ r.terms ≤ arctanFuel tau := by
  have hg := sampled_phase_increment (rationalCircleCast previous) (rationalCircleCast current)
    theta0 theta1 e he he64 hstep hp hc
  have hre : 0<phaseRatioRe previous current := by
    apply (Rat.cast_pos (K := ℝ)).mp
    rw [rationalCircleCast_ratio_re]
    exact hg.1
  have hratio : |phaseRatioIm previous current/phaseRatioRe previous current| ≤ (1/2 : ℚ) := by
    apply (Rat.cast_le (K := ℝ)).mp
    push_cast
    rw [rationalCircleCast_ratio_im,rationalCircleCast_ratio_re]
    exact hg.2.1
  let r := rationalArctan (phaseRatioIm previous current/phaseRatioRe previous current) tau
  have hr := rationalArctan_error _ tau hratio htau
  have hs := rationalArctan_spec _ tau hratio htau
  have hang : Real.arctan ((phaseRatioIm previous current/phaseRatioRe previous current : ℚ) : ℝ)=
      (theta1-theta0)+sampleAngleError (rationalCircleCast current) theta1-
        sampleAngleError (rationalCircleCast previous) theta0 := by
    push_cast
    rw [rationalCircleCast_ratio_im,rationalCircleCast_ratio_re]
    exact hg.2.2
  rw [hang] at hr
  exact ⟨r,by simp only [rationalPhaseStep,if_pos (And.intro hre hratio),r],hr,hs.2.2.2.1,hs.2.2.1⟩

/-- The sample error angle telescopes in the *real* accumulated value. The
semantic phase sequence is not queried by the program and can make any
number of complete turns. -/
theorem rationalPhasePrefix_spec (samples : ℕ → RationalCircleSample) (theta : ℕ → ℝ)
    (N : ℕ) (e : ℝ) (tau : ℚ) (htau : 0<tau) (he : 0 ≤ e) (he64 : e ≤ 1/64)
    (hs0 : samples 0=(1,0)) (ht0 : theta 0=0)
    (hstep : ∀ j<N, |theta (j+1)-theta j| ≤ 1/8)
    (hsamples : ∀ j ≤ N, ‖rationalCircleCast (samples j)-complexPhase (theta j)‖ ≤ e) :
    ∀ n ≤ N, ∃ r, rationalPhasePrefix tau samples n=some r ∧ r.previous=samples n ∧
      |(r.value : ℝ)-(theta n+sampleAngleError (rationalCircleCast (samples n)) (theta n))| ≤ (r.arithmeticError : ℝ) ∧
      r.arithmeticError ≤ (n : ℚ)*tau ∧ r.terms ≤ n*arctanFuel tau := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨⟨(1,0),0,0,0⟩,rfl,hs0.symm,?_,by simp,by simp⟩
    simp only [ht0,hs0,rationalCircleCast_one,sampleAngleError_one,Rat.cast_zero,add_zero,sub_zero,abs_zero,le_refl]
  | succ n ih =>
    intro hn
    obtain ⟨r,hrun,hprevious,hvalue,herror,hterms⟩ := ih (Nat.le_of_succ_le hn)
    obtain ⟨inc,hinc,hincValue,hincError,hincTerms⟩ := rationalPhaseStep_spec (samples n) (samples (n+1))
      (theta n) (theta (n+1)) e tau htau he he64 (hstep n (by omega))
      (hsamples n (by omega)) (hsamples (n+1) hn)
    refine ⟨⟨samples (n+1),r.value+inc.value,r.arithmeticError+inc.error,r.terms+inc.terms⟩,?_,rfl,?_,?_,?_⟩
    · simp only [rationalPhasePrefix,hrun,hprevious,hinc]
    · change |((r.value+inc.value : ℚ) : ℝ)-
        (theta (n+1)+sampleAngleError (rationalCircleCast (samples (n+1))) (theta (n+1)))| ≤
          ((r.arithmeticError+inc.error : ℚ) : ℝ)
      have hid : ((r.value+inc.value : ℚ) : ℝ)-
          (theta (n+1)+sampleAngleError (rationalCircleCast (samples (n+1))) (theta (n+1)))=
          ((r.value : ℝ)-(theta n+sampleAngleError (rationalCircleCast (samples n)) (theta n)))+
          ((inc.value : ℝ)-((theta (n+1)-theta n)+sampleAngleError (rationalCircleCast (samples (n+1))) (theta (n+1))-
            sampleAngleError (rationalCircleCast (samples n)) (theta n))) := by push_cast; ring
      rw [hid,Rat.cast_add]
      exact (abs_add_le _ _).trans (add_le_add hvalue hincValue)
    · change r.arithmeticError+inc.error ≤ ((n+1 : ℕ) : ℚ)*tau
      calc
        _ ≤ (n : ℚ)*tau+tau := add_le_add herror hincError
        _ = _ := by push_cast; ring
    · change r.terms+inc.terms ≤ (n+1)*arctanFuel tau
      calc
        _ ≤ n*arctanFuel tau+arctanFuel tau := Nat.add_le_add hterms hincTerms
        _ = _ := by ring

/-- This finite semantic contract does not provide phase values to the
execution. Its next consumer supplies them from the actual angular primitive
of the circle curve, rather than an external lift oracle. -/
theorem rationalPhaseLog_finite (oracle : ℚ × ℕ → RationalCircleSample) (endpoint bound tau : ℚ)
    (ht : 0<tau) (theta : ℕ → ℝ) (ht0 : theta 0=0)
    (hstep : ∀ j<phaseLogSteps endpoint bound, |theta (j+1)-theta j| ≤ 1/8)
    (hsamples : ∀ j ≤ phaseLogSteps endpoint bound,
      ‖rationalCircleCast (phaseLogSamples oracle endpoint (phaseLogSteps endpoint bound) (phaseLogPrecision tau) j)-
        complexPhase (theta j)‖ ≤ (2^phaseLogPrecision tau : ℝ)⁻¹) :
    ∃ r, rationalPhaseLog oracle endpoint bound tau=some r ∧
      |(r.value : ℝ)-theta (phaseLogSteps endpoint bound)| ≤ (r.errorBound : ℝ) ∧ r.errorBound ≤ tau ∧
      r.steps=phaseLogSteps endpoint bound ∧ r.precision=phaseLogPrecision tau ∧
      r.terms ≤ r.steps*arctanFuel (tau/(2*(r.steps : ℚ))) := by
  let D := phaseLogSteps endpoint bound
  let b := phaseLogPrecision tau
  let samples := phaseLogSamples oracle endpoint D b
  let e : ℝ := (2^b : ℝ)⁻¹
  have hD : (0 : ℚ)<D := by exact_mod_cast phaseLogSteps_pos endpoint bound
  have he64 : e ≤ 1/64 := by
    have h : ((((2^b : ℚ)⁻¹ : ℚ)) : ℝ) ≤ (((1/64 : ℚ) : ℝ)) :=
      Rat.cast_le.mpr (phaseLogPrecision_small tau)
    push_cast at h
    exact h
  obtain ⟨state,hrun,_,hvalue,herror,hterms⟩ := rationalPhasePrefix_spec samples theta D e
    (tau/(2*(D : ℚ))) (by positivity) (by positivity) he64
    (by simp [samples,phaseLogSamples]) ht0 hstep hsamples D (le_refl D)
  let result : RationalPhaseLogResult :=
    ⟨state.value,state.arithmeticError,2*(2^b : ℚ)⁻¹+state.arithmeticError,D,b,state.terms⟩
  have hend := (sampleAngleError_spec (rationalCircleCast (samples D)) (theta D) e (by positivity) he64 (hsamples D (le_refl D))).2.1
  have hv : |(state.value : ℝ)-theta D| ≤ 2*e+(state.arithmeticError : ℝ) := by
    calc
      _ = |((state.value : ℝ)-(theta D+sampleAngleError (rationalCircleCast (samples D)) (theta D)))+
          sampleAngleError (rationalCircleCast (samples D)) (theta D)| := by congr 1; ring
      _ ≤ |(state.value : ℝ)-(theta D+sampleAngleError (rationalCircleCast (samples D)) (theta D))|+
          |sampleAngleError (rationalCircleCast (samples D)) (theta D)| := abs_add_le _ _
      _ ≤ (state.arithmeticError : ℝ)+2*e := add_le_add hvalue hend
      _ = _ := by ring
  have harith : state.arithmeticError ≤ tau/2 := by
    have hi : (D : ℚ)*(tau/(2*(D : ℚ)))=tau/2 := by field_simp
    exact herror.trans_eq hi
  have hb := phaseLogPrecision_budget tau ht
  refine ⟨result,?_,?_,?_,rfl,rfl,hterms⟩
  · change (rationalPhasePrefix (tau/(2*(D : ℚ))) samples D).map
      (fun r => ⟨r.value,r.arithmeticError,2*(2^b : ℚ)⁻¹+r.arithmeticError,D,b,r.terms⟩)=some result
    rw [hrun]
    rfl
  · change |(state.value : ℝ)-theta D| ≤ ((2*(2^b : ℚ)⁻¹+state.arithmeticError : ℚ) : ℝ)
    push_cast
    exact hv
  · change 2*(2^b : ℚ)⁻¹+state.arithmeticError ≤ tau
    linarith

end
end Qatlib.Concepts.EffectiveGauge.HopfAtlas
