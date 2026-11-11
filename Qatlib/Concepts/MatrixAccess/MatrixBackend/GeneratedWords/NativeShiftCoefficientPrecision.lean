/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeShiftBornPrecision
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeNeumannConsumer
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-! Uniform four-coordinate residual of the actual shift generator.
The generated preparation, phase and exact slack flag are the same inputs
used by identityCoefficient/oracleCoefficient. The original rational domain
suffices; a successful scalar certificate or final error is not assumed.
This is an output-value model, not whole Python or primitive bit-cost semantics. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open Qatlib Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- Construction for coordinate Size in the native shift coefficient precision model. -/
private def coordinateSize (z : ℂ) : ℝ := |z.re|+|z.im|

/-- The finite construction in `NativeShiftCoefficientPrecision` satisfies `coordinateSize_add` under the displayed hypotheses. -/
private theorem coordinateSize_add (z w : ℂ) :
    coordinateSize (z+w) ≤ coordinateSize z+coordinateSize w := by
  simp only [coordinateSize,Complex.add_re,Complex.add_im]
  linarith [abs_add_le z.re w.re,abs_add_le z.im w.im]

/-- The finite construction in `NativeShiftCoefficientPrecision` satisfies `coordinateSize_sum` under the displayed hypotheses. -/
private theorem coordinateSize_sum (f : Fin 8 → ℂ) :
    coordinateSize (∑ i,f i) ≤ ∑ i,coordinateSize (f i) := by
  simp only [coordinateSize,Complex.re_sum,Complex.im_sum,Finset.sum_add_distrib]
  exact add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)

/-- The finite construction in `NativeShiftCoefficientPrecision` satisfies `coordinateSize_real_mul` under the displayed hypotheses. -/
private theorem coordinateSize_real_mul (r : ℝ) (z : ℂ) :
    coordinateSize ((r : ℂ)*z)=|r| *coordinateSize z := by
  simp [coordinateSize,Complex.mul_re,Complex.mul_im,abs_mul,mul_add]

/-- The finite construction in `NativeShiftCoefficientPrecision` satisfies `coordinateSize_unit` under the displayed hypotheses. -/
private theorem coordinateSize_unit (z : ℂ) (hz : ‖z‖=1) : coordinateSize z ≤ 3/2 := by
  have hs : |z.re|^2+|z.im|^2=1 := by
    rw [sq_abs,sq_abs]
    have hh : ‖z‖^2=z.re^2+z.im^2 := by rw [Complex.sq_norm,Complex.normSq_apply]; ring
    rw [hz] at hh
    nlinarith
  dsimp only [coordinateSize]
  nlinarith [sq_nonneg (|z.re|-|z.im|),abs_nonneg z.re,abs_nonneg z.im]

/-- The finite construction in `NativeShiftCoefficientPrecision` satisfies `phaseCoefficient_norm` under the displayed hypotheses. -/
private theorem phaseCoefficient_norm (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) (i : Fin 8) :
    ‖Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.phaseCoefficient p slack i‖=1 := by
  have hp : ‖Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.phaseScalar p‖=1 := by
    have h : ‖Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.phaseScalar p‖^2=1 := by
      rw [Complex.sq_norm,Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.phaseScalar_norm]
    nlinarith [norm_nonneg (Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.phaseScalar p)]
  fin_cases i <;> cases slack <;> simp [Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.phaseCoefficient,hp]

/-- Construction for weighted Identity in the native shift coefficient precision model. -/
private def weightedIdentity (w : Fin 8 → ℝ) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) : ℂ :=
  ∑ i : Fin 8,if i.val<4 then (w i : ℂ)*Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.phaseCoefficient p slack i else 0

/-- Construction for weighted Oracle in the native shift coefficient precision model. -/
private def weightedOracle (w : Fin 8 → ℝ) (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) : ℂ :=
  ∑ i : Fin 8,if i.val<4 then 0 else (w i : ℂ)*Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.phaseCoefficient p slack i

/-- The finite construction in `NativeShiftCoefficientPrecision` satisfies `effectiveCoefficient_born` under the displayed hypotheses. -/
private theorem effectiveCoefficient_born (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) (i : Fin 8) :
    Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.effectiveCoefficients ps p slack i=
      (‖Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.prepAxis ps i‖^2 : ℝ)*Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.phaseCoefficient p slack i := by
  rw [Complex.sq_norm,Complex.normSq_eq_conj_mul_self]
  change star (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.prepAxis ps i)*Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.phaseCoefficient p slack i*Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.prepAxis ps i=
    (star (Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.prepAxis ps i)*Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.prepAxis ps i)*Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.phaseCoefficient p slack i
  ring

/-- The estimate `coefficient_group_error` retains the actual parameter, input-error and normalization budgets. -/
private theorem coefficient_group_error (ps : Fin 7 → Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle)
    (p : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) (w : Fin 8 → ℝ) :
    coordinateSize (identityCoefficient ps p slack-weightedIdentity w p slack)+
      coordinateSize (oracleCoefficient ps p slack-weightedOracle w p slack) ≤
      (3/2 : ℝ)*(∑ i : Fin 8,|‖Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.prepAxis ps i‖^2-w i|) := by
  let d : Fin 8 → ℂ := fun i =>
    ((‖Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.prepAxis ps i‖^2-w i : ℝ) : ℂ)*Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.phaseCoefficient p slack i
  have hI : identityCoefficient ps p slack-weightedIdentity w p slack=
      ∑ i : Fin 8,if i.val<4 then d i else 0 := by
    rw [identityCoefficient,weightedIdentity,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [effectiveCoefficient_born]
    by_cases hi : i.val<4 <;> simp [hi,d,Complex.ofReal_sub,sub_mul]
  have hO : oracleCoefficient ps p slack-weightedOracle w p slack=
      ∑ i : Fin 8,if i.val<4 then 0 else d i := by
    rw [oracleCoefficient,weightedOracle,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [effectiveCoefficient_born]
    by_cases hi : i.val<4 <;> simp [hi,d,Complex.ofReal_sub,sub_mul]
  have hi (i : Fin 8) : coordinateSize (d i) ≤
      |‖Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.prepAxis ps i‖^2-w i| *(3/2) := by
    dsimp only [d]
    rw [coordinateSize_real_mul]
    exact mul_le_mul_of_nonneg_left
      (coordinateSize_unit _ (phaseCoefficient_norm p slack i)) (abs_nonneg _)
  rw [hI,hO]
  calc
    _ ≤ (∑ i : Fin 8,coordinateSize (if i.val<4 then d i else 0))+
        (∑ i : Fin 8,coordinateSize (if i.val<4 then 0 else d i)) :=
      add_le_add (coordinateSize_sum _) (coordinateSize_sum _)
    _ = ∑ i : Fin 8,coordinateSize (d i) := by
      rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : i.val<4 <;> simp [h,coordinateSize]
    _ ≤ ∑ i : Fin 8,|‖Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.prepAxis ps i‖^2-w i| *(3/2) :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by rw [←Finset.sum_mul]; ring

/-- The finite construction in `NativeShiftCoefficientPrecision` satisfies `shift_weightedIdentity` under the displayed hypotheses. -/
private theorem shift_weightedIdentity (α B x y : ℚ) (p : ℕ) (q : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) :
    weightedIdentity (fun i => (shiftWeights α B x y p i : ℝ)) q slack=
      (shiftMassLower B x y p : ℂ)*Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.phaseScalar q+
        if slack then 0 else ((1-α/B-shiftMassLower B x y p : ℚ) : ℂ) := by
  cases slack <;>
    simp [weightedIdentity,shiftWeights,Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.phaseCoefficient,Fin.sum_univ_succ]

/-- The finite construction in `NativeShiftCoefficientPrecision` satisfies `shift_weightedOracle` under the displayed hypotheses. -/
private theorem shift_weightedOracle (α B x y : ℚ) (p : ℕ) (q : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle) (slack : Bool) :
    weightedOracle (fun i => (shiftWeights α B x y p i : ℝ)) q slack=-(α/B : ℚ) := by
  simp [weightedOracle,shiftWeights,Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep.phaseCoefficient,Fin.sum_univ_succ]


/-- The finite construction in `NativeShiftCoefficientPrecision` satisfies `gaussian_norm_sq` under the displayed hypotheses. -/
private theorem gaussian_norm_sq (x y : ℚ) :
    ‖gaussianRatComplex (x,y)‖^2=((x*x+y*y : ℚ) : ℝ) := by
  simp only [Complex.sq_norm,Complex.normSq_apply,gaussianRatComplex]
  simp

/-- The finite construction in `NativeShiftCoefficientPrecision` satisfies `gaussian_zero_iff` under the displayed hypotheses. -/
private theorem gaussian_zero_iff (x y : ℚ) :
    gaussianRatComplex (x,y)=0 ↔ x=0 ∧ y=0 := by
  constructor
  · intro h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    simp [gaussianRatComplex] at hr hi
    exact ⟨by exact_mod_cast hr,by exact_mod_cast hi⟩
  · rintro ⟨rfl,rfl⟩
    simp [gaussianRatComplex]

/-- Construction for shift Target Radius in the native shift coefficient precision model. -/
private def shiftTargetRadius (B x y : ℚ) : ℝ := ‖gaussianRatComplex (x,y)‖/(B : ℝ)

/-- The finite construction in `NativeShiftCoefficientPrecision` satisfies `nativePhaseTarget_norm` under the displayed hypotheses. -/
private theorem nativePhaseTarget_norm (x y : ℚ) : ‖nativePhaseTarget x y‖=1 := by
  by_cases hz : x=0 ∧ y=0
  · simp [nativePhaseTarget,hz]
  · have hn : ‖gaussianRatComplex (x,y)‖≠0 := by
      apply norm_ne_zero_iff.mpr
      exact fun h => hz ((gaussian_zero_iff x y).mp h)
    simp [nativePhaseTarget,hz,hn]

/-- The finite construction in `NativeShiftCoefficientPrecision` satisfies `shiftTargetRadius_phase` under the displayed hypotheses. -/
private theorem shiftTargetRadius_phase (B x y : ℚ) (hB : 0<B) :
    (shiftTargetRadius B x y : ℂ)*nativePhaseTarget x y=
      gaussianRatComplex (x,y)/(B : ℂ) := by
  by_cases hz : x=0 ∧ y=0
  · rcases hz with ⟨rfl,rfl⟩
    simp [shiftTargetRadius,nativePhaseTarget,gaussianRatComplex]
  · have hn : (‖gaussianRatComplex (x,y)‖ : ℂ)≠0 := by
      have hh : ‖gaussianRatComplex (x,y)‖≠0 :=
        norm_ne_zero_iff.mpr (fun h => hz ((gaussian_zero_iff x y).mp h))
      exact_mod_cast hh
    have hBC : (B : ℂ)≠0 := by exact_mod_cast ne_of_gt hB
    simp only [shiftTargetRadius,nativePhaseTarget,ite_eq_right hz,Complex.ofReal_div,
      Complex.ofReal_ratCast]
    field_simp [hn,hBC]

/-- The estimate `shiftMassLower_error` retains the actual parameter, input-error and normalization budgets. -/
private theorem shiftMassLower_error (B x y : ℚ) (p : ℕ) (hB : 0<B) :
    0 ≤ shiftTargetRadius B x y-(shiftMassLower B x y p : ℝ) ∧
      shiftTargetRadius B x y-(shiftMassLower B x y p : ℝ) ≤ 1/(2 : ℝ)^(2*p+16) := by
  have hnum : (0 : ℚ) ≤ x*x+y*y := by nlinarith [sq_nonneg x,sq_nonneg y]
  have hq : (0 : ℚ) ≤ (x*x+y*y)/(B*B) := div_nonneg hnum (by positivity)
  have hnumR : (0 : ℝ) ≤ ((x*x+y*y : ℚ) : ℝ) := by exact_mod_cast hnum
  have hden : Real.sqrt ((B*B : ℚ) : ℝ)=(B : ℝ) := by
    push_cast
    rw [←pow_two,Real.sqrt_sq (show (0 : ℝ) ≤ B by exact_mod_cast hB.le)]
  have hroot : Real.sqrt (((x*x+y*y)/(B*B) : ℚ) : ℝ)=shiftTargetRadius B x y := by
    rw [Rat.cast_div,Real.sqrt_div hnumR,hden,←gaussian_norm_sq x y,
      Real.sqrt_sq (norm_nonneg _)]
    rfl
  have hi := nativeSqrtInterval_real ((x*x+y*y)/(B*B)) (2*p+16) hq
  rw [hroot] at hi
  exact ⟨sub_nonneg.mpr hi.1,(le_abs_self _).trans hi.2.2.1⟩

/-- The finite construction in `NativeShiftCoefficientPrecision` satisfies `shift_zeroSlack_radius` under the displayed hypotheses. -/
private theorem shift_zeroSlack_radius (α B x y : ℚ) (hα : 0<α) (hB : α ≤ B)
    (hflag : nativeShiftSlack α B x y=false) :
    shiftTargetRadius B x y=1-(α/B : ℚ) := by
  have h0 : (B-α)^2=x*x+y*y := not_ne_iff.mp (of_decide_eq_false hflag)
  have hs : ‖gaussianRatComplex (x,y)‖^2=(((B-α : ℚ) : ℝ))^2 := by
    rw [gaussian_norm_sq]
    exact_mod_cast h0.symm
  have hBA : (0 : ℝ) ≤ ((B-α : ℚ) : ℝ) := by exact_mod_cast sub_nonneg.mpr hB
  have hn : ‖gaussianRatComplex (x,y)‖=((B-α : ℚ) : ℝ) := by
    nlinarith [norm_nonneg (gaussianRatComplex (x,y))]
  have hB0 : (B : ℝ)≠0 := by exact_mod_cast ne_of_gt (hα.trans_le hB)
  dsimp only [shiftTargetRadius]
  rw [hn]
  push_cast
  field_simp


/-- The estimate `shift_weightedIdentity_error` retains the actual parameter, input-error and normalization budgets. -/
private theorem shift_weightedIdentity_error (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) :
    coordinateSize (weightedIdentity (fun i => (shiftWeights α B x y p i : ℝ))
      (nativePhaseCircle x y p) (nativeShiftSlack α B x y)-
        gaussianRatComplex (x,y)/(B : ℂ)) ≤
      1/(8*(2 : ℝ)^p)+3/(2 : ℝ)^(2*p+16) := by
  let r0 : ℝ := shiftMassLower B x y p
  let r := shiftTargetRadius B x y
  let θ := nativePhaseTarget x y
  let q := nativePhaseCircle x y p
  let s : ℂ := if nativeShiftSlack α B x y then 0 else
    ((1-α/B-shiftMassLower B x y p : ℚ) : ℂ)
  let m : ℂ := (r0 : ℂ)*θ+s
  have hB0 : 0<B := hα.trans_le hB
  have hr0 : 0 ≤ r0 ∧ r0 ≤ 1 := by
    have hl := shiftMassLower_bounds α B x y p hα hB hz
    have hαB : (0 : ℚ) ≤ α/B := div_nonneg hα.le hB0.le
    constructor
    · dsimp only [r0]
      exact_mod_cast hl.1
    · dsimp only [r0]
      exact_mod_cast (show shiftMassLower B x y p ≤ 1 by linarith)
  have hd := shiftMassLower_error B x y p hB0
  change 0 ≤ r-r0 ∧ r-r0 ≤ _ at hd
  have hs : coordinateSize s ≤ r-r0 := by
    cases hflag : nativeShiftSlack α B x y
    · have hzero := shift_zeroSlack_radius α B x y hα hB hflag
      have he : s=((r-r0 : ℝ) : ℂ) := by
        dsimp only [s]
        rw [hflag]
        simp only [Bool.false_eq_true,ite_false]
        dsimp only [r,r0]
        rw [hzero]
        push_cast
        ring
      rw [he]
      simpa only [coordinateSize,Complex.ofReal_re,Complex.ofReal_im,abs_zero,add_zero,
        abs_of_nonneg hd.1] using (le_refl (r-r0))
    · simp only [s,hflag,ite_true,coordinateSize,Complex.zero_re,Complex.zero_im,abs_zero,
        add_zero]
      exact hd.1
  have hphase : coordinateSize (Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.phaseScalar q-θ) ≤ 1/(8*(2 : ℝ)^p) := by
    have hp := nativePhaseCircle_coordinate_error x y p
    change coordinateSize (gaussianRatComplex ((nativePhaseCircle x y p).c,
      (nativePhaseCircle x y p).s)-θ) ≤ _ at hp
    rw [←Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.phaseScalar_as_gaussian] at hp
    exact hp
  have hfirst : coordinateSize (weightedIdentity (fun i => (shiftWeights α B x y p i : ℝ)) q
      (nativeShiftSlack α B x y)-m) ≤ 1/(8*(2 : ℝ)^p) := by
    have he : weightedIdentity (fun i => (shiftWeights α B x y p i : ℝ)) q
        (nativeShiftSlack α B x y)-m=(r0 : ℂ)*(Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.phaseScalar q-θ) := by
      rw [shift_weightedIdentity]
      change (r0 : ℂ)*Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.phaseScalar q+s-((r0 : ℂ)*θ+s)=_
      ring
    rw [he,coordinateSize_real_mul,abs_of_nonneg hr0.1]
    calc
      _ ≤ r0*(1/(8*(2 : ℝ)^p)) := mul_le_mul_of_nonneg_left hphase hr0.1
      _ ≤ 1*(1/(8*(2 : ℝ)^p)) := mul_le_mul_of_nonneg_right hr0.2 (by positivity)
      _ = _ := one_mul _
  have hsecond : coordinateSize (m-gaussianRatComplex (x,y)/(B : ℂ)) ≤
      3/(2 : ℝ)^(2*p+16) := by
    have he : m-gaussianRatComplex (x,y)/(B : ℂ)=((r0-r : ℝ) : ℂ)*θ+s := by
      rw [←shiftTargetRadius_phase B x y hB0]
      change (r0 : ℂ)*θ+s-(r : ℂ)*θ=_
      push_cast
      ring
    have hθ : coordinateSize θ ≤ 3/2 := coordinateSize_unit _ (nativePhaseTarget_norm x y)
    rw [he]
    calc
      _ ≤ coordinateSize (((r0-r : ℝ) : ℂ)*θ)+coordinateSize s := coordinateSize_add _ _
      _ = (r-r0)*coordinateSize θ+coordinateSize s := by
        rw [coordinateSize_real_mul,abs_sub_comm,abs_of_nonneg hd.1]
      _ ≤ (r-r0)*(3/2)+(r-r0) :=
        add_le_add (mul_le_mul_of_nonneg_left hθ hd.1) hs
      _ ≤ 3*(1/(2 : ℝ)^(2*p+16)) := by nlinarith [hd.1,hd.2]
      _ = _ := by ring
  have he : weightedIdentity (fun i => (shiftWeights α B x y p i : ℝ)) q
      (nativeShiftSlack α B x y)-gaussianRatComplex (x,y)/(B : ℂ)=
      (weightedIdentity (fun i => (shiftWeights α B x y p i : ℝ)) q
        (nativeShiftSlack α B x y)-m)+(m-gaussianRatComplex (x,y)/(B : ℂ)) := by ring
  rw [he]
  exact (coordinateSize_add _ _).trans (add_le_add hfirst hsecond)

/-- Four real-coordinate residuals of the actual generated coefficient pair.
The exact squared-equality slack flag is shared with the emitted phase word. -/
def nativeShiftCoordinateResidual (α B x y : ℚ) (p : ℕ) : ℝ :=
  let ps := nativeShiftCircles α B x y p
  let q := nativePhaseCircle x y p
  let slack := nativeShiftSlack α B x y
  let a := identityCoefficient ps q slack-gaussianRatComplex (x,y)/(B : ℂ)
  let c := oracleCoefficient ps q slack+(α/B : ℚ)
  (|a.re|+|a.im|)+(|c.re|+|c.im|)

/-- The estimate `nativeShiftCoordinateResidual_bound` retains the actual parameter, input-error and normalization budgets. -/
theorem nativeShiftCoordinateResidual_bound (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) :
    nativeShiftCoordinateResidual α B x y p ≤
      276/(2 : ℝ)^(p+12)+1/(8*(2 : ℝ)^p)+3/(2 : ℝ)^(2*p+16) := by
  let ps := nativeShiftCircles α B x y p
  let q := nativePhaseCircle x y p
  let slack := nativeShiftSlack α B x y
  let w : Fin 8 → ℝ := fun i => shiftWeights α B x y p i
  have hg := coefficient_group_error ps q slack w
  have hb := nativeShiftBorn_error α B x y p hα hB hz
  have hg' : coordinateSize (identityCoefficient ps q slack-weightedIdentity w q slack)+
      coordinateSize (oracleCoefficient ps q slack-weightedOracle w q slack) ≤
      276/(2 : ℝ)^(p+12) :=
    hg.trans ((mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 3/2)).trans_eq (by ring))
  have hi := shift_weightedIdentity_error α B x y p hα hB hz
  have hO : oracleCoefficient ps q slack+(α/B : ℚ)=
      oracleCoefficient ps q slack-weightedOracle w q slack := by
    rw [shift_weightedOracle]
    simp
  have hI : identityCoefficient ps q slack-gaussianRatComplex (x,y)/(B : ℂ)=
      (identityCoefficient ps q slack-weightedIdentity w q slack)+
      (weightedIdentity w q slack-gaussianRatComplex (x,y)/(B : ℂ)) := by ring
  change coordinateSize (identityCoefficient ps q slack-gaussianRatComplex (x,y)/(B : ℂ))+
    coordinateSize (oracleCoefficient ps q slack+(α/B : ℚ)) ≤ _
  rw [hO,hI]
  have ht := coordinateSize_add (identityCoefficient ps q slack-weightedIdentity w q slack)
    (weightedIdentity w q slack-gaussianRatComplex (x,y)/(B : ℂ))
  change coordinateSize (weightedIdentity w q slack-gaussianRatComplex (x,y)/(B : ℂ)) ≤ _ at hi
  linarith

/-- The estimate `precision_scalar_bound` retains the actual parameter, input-error and normalization budgets. -/
private theorem precision_scalar_bound (p : ℕ) :
    276/(2 : ℝ)^(p+12)+1/(8*(2 : ℝ)^p)+3/(2 : ℝ)^(2*p+16) ≤
      12611/(65536*(2 : ℝ)^p) := by
  have hp : (0 : ℝ)<(2 : ℝ)^(p+16) := by positivity
  have he : (2 : ℝ)^(p+16) ≤ (2 : ℝ)^(2*p+16) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    _ ≤ 276/(2 : ℝ)^(p+12)+1/(8*(2 : ℝ)^p)+3/(2 : ℝ)^(p+16) :=
      add_le_add le_rfl (div_le_div_of_nonneg_left (by norm_num) hp he)
    _ = _ := by rw [pow_add,pow_add]; norm_num; ring

/-- The complete coordinate rate is uniform over the original rational
input domain, including p=0 and every exact-slack/zero-node branch. -/
theorem nativeShiftCoordinateResidual_error (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) :
    nativeShiftCoordinateResidual α B x y p ≤ 12611/(65536*(2 : ℝ)^p) :=
  (nativeShiftCoordinateResidual_bound α B x y p hα hB hz).trans (precision_scalar_bound p)

/-- The finite construction in `NativeShiftCoefficientPrecision` satisfies `nativeShiftCoordinateResidual_le` under the displayed hypotheses. -/
theorem nativeShiftCoordinateResidual_le (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) :
    nativeShiftCoordinateResidual α B x y p ≤ 1/(2 : ℝ)^p := by
  have he := nativeShiftCoordinateResidual_error α B x y p hα hB hz
  apply he.trans
  have hp : (0 : ℝ)<(2 : ℝ)^p := by positivity
  apply (div_le_div_iff₀ (by positivity) hp).mpr
  nlinarith


/-- The original input-domain check supplies the scale bound used by the
same-query resolvent consumer, without a separate contractivity premise. -/
theorem nativeShift_input_bound (α B x y : ℚ) (hB : α ≤ B)
    (hz : x*x+y*y ≤ (B-α)^2) :
    (α : ℝ)+‖gaussianRatComplex (x,y)‖ ≤ (B : ℝ) := by
  have hs := gaussian_norm_sq x y
  have hzR : ((x*x+y*y : ℚ) : ℝ) ≤ (((B-α : ℚ) : ℝ))^2 := by exact_mod_cast hz
  have hBA : (0 : ℝ) ≤ ((B-α : ℚ) : ℝ) := by exact_mod_cast sub_nonneg.mpr hB
  have hn : ‖gaussianRatComplex (x,y)‖ ≤ ((B-α : ℚ) : ℝ) := by
    nlinarith [norm_nonneg (gaussianRatComplex (x,y))]
  push_cast at hn
  linarith

/-- The same actual coefficients supply the existing original-oracle
consumer's complex-norm error; the four-coordinate rate is stronger. -/
theorem nativeShiftCoefficient_error (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) :
    nativeCoefficientError (nativeShiftCircles α B x y p) (nativePhaseCircle x y p)
      (nativeShiftSlack α B x y) (α : ℝ) (B : ℝ) (gaussianRatComplex (x,y)) ≤
      1/(2 : ℝ)^p := by
  have he := nativeShiftCoordinateResidual_le α B x y p hα hB hz
  dsimp only [nativeCoefficientError]
  apply (add_le_add (Complex.norm_le_abs_re_add_abs_im _)
    (Complex.norm_le_abs_re_add_abs_im _)).trans
  simpa only [nativeShiftCoordinateResidual,Complex.ofReal_ratCast,Rat.cast_div] using he

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
