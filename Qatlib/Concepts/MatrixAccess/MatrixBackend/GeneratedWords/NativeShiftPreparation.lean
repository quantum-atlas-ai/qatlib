/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixContour.ContourCalc.ContourModel

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

/-! Exact output-value model of the existing shift_parameters preparation.
The radial lower root, eight weight roots, eight actual prefix boxes and
seven midpoint-Cayley rotations are retained. The half-angle error is uniform
on the original rational input domain, including all zero branches.
This module does not assume a successful generated certificate or a final
coefficient error; the remaining column/coefficient connection is separate. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords Qatlib.Foundations.OpCalculus.ContourCalc Qatlib.Concepts.MatrixContour.ContourCalc Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords

open scoped BigOperators

/-- Construction for shift Mass Lower in the native shift preparation model. -/
def shiftMassLower (B x y : ℚ) (p : ℕ) : ℚ :=
  (nativeSqrtInterval ((x*x+y*y)/(B*B)) (2*p+16)).1

/-- Construction for shift Weights in the native shift preparation model. -/
def shiftWeights (α B x y : ℚ) (p : ℕ) : Fin 8 → ℚ :=
  ![shiftMassLower B x y p,(1-α/B-shiftMassLower B x y p)/2,
    (1-α/B-shiftMassLower B x y p)/2,0,α/B,0,0,0]

/-- Construction for shift Roots in the native shift preparation model. -/
def shiftRoots (α B x y : ℚ) (p : ℕ) (i : Fin 8) : ℚ :=
  (nativeSqrtInterval (shiftWeights α B x y p i) (p+12)).1

/-- Construction for shift Axis in the native shift preparation model. -/
def shiftAxis (α B x y : ℚ) (p : ℕ) (i : Fin 8) : ℚ :=
  shiftRoots α B x y p i+if i=0 then 1 else 0

/-- Construction for shift Prefix in the native shift preparation model. -/
def shiftPrefix (α B x y : ℚ) (p : ℕ) (i : Fin 8) : ℚ :=
  ∑ j : Fin 8, if j.val ≤ i.val then (shiftAxis α B x y p j)^2 else 0

/-- Construction for shift Prefix Box in the native shift preparation model. -/
def shiftPrefixBox (α B x y : ℚ) (p : ℕ) (i : Fin 8) : ℚ × ℚ × ℕ :=
  nativeSqrtInterval (shiftPrefix α B x y p i) (p+12)

/-- Construction for shift Half Lower in the native shift preparation model. -/
def shiftHalfLower (α B x y : ℚ) (p : ℕ) (i : Fin 7) : ℚ :=
  shiftAxis α B x y p i.succ/((shiftPrefixBox α B x y p i.succ).2.1+
    (shiftPrefixBox α B x y p i.castSucc).2.1)

/-- Construction for shift Half Upper in the native shift preparation model. -/
def shiftHalfUpper (α B x y : ℚ) (p : ℕ) (i : Fin 7) : ℚ :=
  shiftAxis α B x y p i.succ/((shiftPrefixBox α B x y p i.succ).1+
    (shiftPrefixBox α B x y p i.castSucc).1)

/-- Construction for shift Half in the native shift preparation model. -/
def shiftHalf (α B x y : ℚ) (p : ℕ) (i : Fin 7) : ℚ :=
  (shiftHalfLower α B x y p i+shiftHalfUpper α B x y p i)/2

/-- The estimate `shiftMassLower_bounds` retains the actual parameter, input-error and normalization budgets. -/
theorem shiftMassLower_bounds (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) :
    0 ≤ shiftMassLower B x y p ∧ shiftMassLower B x y p ≤ 1-α/B := by
  have hB0 : 0<B := hα.trans_le hB
  have hq : 0 ≤ (x*x+y*y)/(B*B) := div_nonneg (by nlinarith [sq_nonneg x,sq_nonneg y]) (by positivity)
  have hlo := nativeSqrtInterval_rational ((x*x+y*y)/(B*B)) (2*p+16) hq
  have hsq : (shiftMassLower B x y p)^2 ≤ (x*x+y*y)/(B*B) := hlo.2.2.1
  have hL : 0 ≤ shiftMassLower B x y p := hlo.1
  have hb : 0 ≤ 1-α/B := by have hh := (div_le_one hB0).mpr hB; linarith
  have hrat : (x*x+y*y)/(B*B) ≤ (1-α/B)^2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℚ)<B*B)).mpr
    have he : (1-α/B)^2*(B*B)=(B-α)^2 := by field_simp
    rw [he]
    exact hz
  exact ⟨hL,by nlinarith [hsq.trans hrat]⟩

/-- The finite construction in `NativeShiftPreparation` satisfies `shiftWeights_simplex` under the displayed hypotheses. -/
theorem shiftWeights_simplex (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) :
    (∀ i,0 ≤ shiftWeights α B x y p i) ∧ (∑ i,shiftWeights α B x y p i)=1 := by
  have hB0 : 0<B := hα.trans_le hB
  obtain ⟨hl,hu⟩ := shiftMassLower_bounds α B x y p hα hB hz
  constructor
  · intro i
    fin_cases i
    · exact hl
    · change 0 ≤ (1-α/B-shiftMassLower B x y p)/2
      linarith
    · change 0 ≤ (1-α/B-shiftMassLower B x y p)/2
      linarith
    · exact le_rfl
    · exact div_nonneg hα.le hB0.le
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl
  · simp only [shiftWeights,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ]
    ring

/-- The estimate `shiftRoots_bounds` retains the actual parameter, input-error and normalization budgets. -/
theorem shiftRoots_bounds (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) (i : Fin 8) :
    0 ≤ shiftRoots α B x y p i ∧ shiftRoots α B x y p i ≤ 1 := by
  obtain ⟨hw,hsum⟩ := shiftWeights_simplex α B x y p hα hB hz
  have hi : shiftWeights α B x y p i ≤ 1 := by
    rw [←hsum]
    exact Finset.single_le_sum (fun j _ => hw j) (Finset.mem_univ i)
  obtain ⟨hl,_,hlq,_,_,_⟩ := nativeSqrtInterval_rational (shiftWeights α B x y p i) (p+12) (hw i)
  exact ⟨hl,by change shiftRoots α B x y p i^2 ≤ _ at hlq; nlinarith⟩

/-- The estimate `shiftAxis_bounds` retains the actual parameter, input-error and normalization budgets. -/
theorem shiftAxis_bounds (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) :
    1 ≤ shiftAxis α B x y p 0 ∧ (∀ i,0 ≤ shiftAxis α B x y p i) ∧
      ∀ i, i≠0 → shiftAxis α B x y p i ≤ 1 := by
  have hh := shiftRoots_bounds α B x y p hα hB hz
  refine ⟨?_,?_,?_⟩
  · change 1 ≤ shiftRoots α B x y p 0+1
    linarith [(hh 0).1]
  · intro i
    unfold shiftAxis
    split_ifs <;> linarith [(hh i).1]
  · intro i hi
    simpa only [shiftAxis,ite_eq_right hi,add_zero] using (hh i).2

/-- The finite construction in `NativeShiftPreparation` satisfies `shiftPrefix_ge_one` under the displayed hypotheses. -/
theorem shiftPrefix_ge_one (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) (i : Fin 8) :
    1 ≤ shiftPrefix α B x y p i := by
  have haxis := (shiftAxis_bounds α B x y p hα hB hz).1
  have hs : (shiftAxis α B x y p 0)^2 ≤ shiftPrefix α B x y p i := by
    have hnonneg (j : Fin 8) :
        (0 : ℚ) ≤ if j.val ≤ i.val then (shiftAxis α B x y p j)^2 else 0 :=
      ite_nonneg (sq_nonneg _) le_rfl
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin 8 => if j.val ≤ i.val then (shiftAxis α B x y p j)^2 else 0)
      (a := (0 : Fin 8)) (fun j _ => hnonneg j) (Finset.mem_univ _)
    simpa only [shiftPrefix,Fin.val_zero,Nat.zero_le,ite_true] using hh
  nlinarith

/-- The estimate `half_bracket_bounds` retains the actual parameter, input-error and normalization budgets. -/
theorem half_bracket_bounds (a l l' u u' h : ℚ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hl : 1 ≤ l) (hl' : 1 ≤ l') (hlu : l ≤ u) (hlu' : l' ≤ u')
    (hw : u-l ≤ h) (hw' : u'-l' ≤ h) :
    0 ≤ a/(u+u') ∧ a/(u+u') ≤ a/(l+l') ∧ a/(l+l') ≤ 1/2 ∧
      a/(l+l')-a/(u+u') ≤ h/2 := by
  have hL : (0 : ℚ)<l+l' := by linarith
  have hU : (0 : ℚ)<u+u' := by linarith
  have hLU : l+l' ≤ u+u' := by linarith
  have hh : 0 ≤ h := by linarith
  refine ⟨by positivity,div_le_div_of_nonneg_left ha hL hLU,?_,?_⟩
  · apply (div_le_iff₀ hL).mpr
    linarith
  · have hid : a/(l+l')-a/(u+u')=a*((u-l)+(u'-l'))/((l+l')*(u+u')) := by
      field_simp
      ring
    rw [hid]
    apply (div_le_iff₀ (mul_pos hL hU)).mpr
    have hprod : 4 ≤ (l+l')*(u+u') := by nlinarith
    have hab : a*((u-l)+(u'-l')) ≤ 2*h := by nlinarith
    nlinarith [mul_nonneg hh (sub_nonneg.mpr hprod)]

/-- The finite construction in `NativeShiftPreparation` satisfies `shiftHalf_bracket` under the displayed hypotheses. -/
theorem shiftHalf_bracket (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) (i : Fin 7) :
    0 ≤ shiftHalfLower α B x y p i ∧ shiftHalfLower α B x y p i ≤ shiftHalfUpper α B x y p i ∧
      shiftHalfUpper α B x y p i ≤ 1/2 ∧
      shiftHalfUpper α B x y p i-shiftHalfLower α B x y p i ≤ 1/(2 : ℚ)^(p+13) := by
  have haxis := shiftAxis_bounds α B x y p hα hB hz
  have hne : i.succ≠0 := by intro h; have hh := congrArg Fin.val h; simp at hh
  have hcur := nativeSqrtInterval_rational (shiftPrefix α B x y p i.succ) (p+12)
    (by have h := shiftPrefix_ge_one α B x y p hα hB hz i.succ; linarith)
  have hprev := nativeSqrtInterval_rational (shiftPrefix α B x y p i.castSucc) (p+12)
    (by have h := shiftPrefix_ge_one α B x y p hα hB hz i.castSucc; linarith)
  have hc := nativeSqrtInterval_lower_one (shiftPrefix α B x y p i.succ) (p+12)
    (shiftPrefix_ge_one α B x y p hα hB hz i.succ)
  have hp := nativeSqrtInterval_lower_one (shiftPrefix α B x y p i.castSucc) (p+12)
    (shiftPrefix_ge_one α B x y p hα hB hz i.castSucc)
  have ht := half_bracket_bounds (shiftAxis α B x y p i.succ) _ _ _ _ (1/(2 : ℚ)^(p+12))
    (haxis.2.1 _) (haxis.2.2 _ hne) hc hp hcur.2.1 hprev.2.1 hcur.2.2.2.2.1 hprev.2.2.2.2.1
  change 0 ≤ shiftHalfLower α B x y p i ∧ shiftHalfLower α B x y p i ≤ shiftHalfUpper α B x y p i ∧
    shiftHalfUpper α B x y p i ≤ 1/2 ∧ _ at ht
  refine ⟨ht.1,ht.2.1,ht.2.2.1,?_⟩
  have he : (1/(2 : ℚ)^(p+12))/2=1/(2 : ℚ)^(p+13) := by rw [show p+13=(p+12)+1 by omega,pow_succ]; ring
  exact ht.2.2.2.trans_eq he


/-- Construction for shift Ideal Half in the native shift preparation model. -/
noncomputable def shiftIdealHalf (α B x y : ℚ) (p : ℕ) (i : Fin 7) : ℝ :=
  (shiftAxis α B x y p i.succ : ℝ)/
    (Real.sqrt (shiftPrefix α B x y p i.succ : ℝ)+Real.sqrt (shiftPrefix α B x y p i.castSucc : ℝ))

/-- The estimate `shiftHalf_error` retains the actual parameter, input-error and normalization budgets. -/
theorem shiftHalf_error (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) (i : Fin 7) :
    |(shiftHalf α B x y p i : ℝ)-shiftIdealHalf α B x y p i| ≤ 1/(2 : ℝ)^(p+14) := by
  have hq := shiftPrefix_ge_one α B x y p hα hB hz i.succ
  have hq' := shiftPrefix_ge_one α B x y p hα hB hz i.castSucc
  have hcur := nativeSqrtInterval_real (shiftPrefix α B x y p i.succ) (p+12) (by linarith)
  have hprev := nativeSqrtInterval_real (shiftPrefix α B x y p i.castSucc) (p+12) (by linarith)
  have hl := nativeSqrtInterval_lower_one (shiftPrefix α B x y p i.succ) (p+12) hq
  have hl' := nativeSqrtInterval_lower_one (shiftPrefix α B x y p i.castSucc) (p+12) hq'
  have ha : (0 : ℝ) ≤ shiftAxis α B x y p i.succ := by
    exact_mod_cast (shiftAxis_bounds α B x y p hα hB hz).2.1 i.succ
  have hlowpos : (0 : ℝ)<((shiftPrefixBox α B x y p i.succ).1 : ℝ)+
      ((shiftPrefixBox α B x y p i.castSucc).1 : ℝ) := by
    have hlR : (1 : ℝ) ≤ (shiftPrefixBox α B x y p i.succ).1 := by exact_mod_cast hl
    have hlR' : (1 : ℝ) ≤ (shiftPrefixBox α B x y p i.castSucc).1 := by exact_mod_cast hl'
    linarith
  have hRpos : (0 : ℝ)<Real.sqrt (shiftPrefix α B x y p i.succ : ℝ)+
      Real.sqrt (shiftPrefix α B x y p i.castSucc : ℝ) := by
    exact lt_of_lt_of_le hlowpos (add_le_add hcur.1 hprev.1)
  have hLower : (shiftHalfLower α B x y p i : ℝ) ≤ shiftIdealHalf α B x y p i := by
    simp only [shiftHalfLower,Rat.cast_div,Rat.cast_add,shiftIdealHalf]
    exact div_le_div_of_nonneg_left ha hRpos (add_le_add hcur.2.1 hprev.2.1)
  have hUpper : shiftIdealHalf α B x y p i ≤ (shiftHalfUpper α B x y p i : ℝ) := by
    simp only [shiftHalfUpper,Rat.cast_div,Rat.cast_add,shiftIdealHalf]
    exact div_le_div_of_nonneg_left ha hlowpos (add_le_add hcur.1 hprev.1)
  have hw : (shiftHalfUpper α B x y p i : ℝ)-(shiftHalfLower α B x y p i : ℝ) ≤
      1/(2 : ℝ)^(p+13) := by
    have hh : ((shiftHalfUpper α B x y p i-shiftHalfLower α B x y p i : ℚ) : ℝ) ≤
        ((1/(2 : ℚ)^(p+13) : ℚ) : ℝ) :=
      Rat.cast_le.mpr (shiftHalf_bracket α B x y p hα hB hz i).2.2.2
    push_cast at hh
    exact hh
  have he : (1/(2 : ℝ)^(p+13))/2=1/(2 : ℝ)^(p+14) := by
    rw [show p+14=(p+13)+1 by omega,pow_succ]
    ring
  rw [←he,abs_le]
  simp only [shiftHalf,Rat.cast_div,Rat.cast_add,Rat.cast_ofNat]
  constructor <;> linarith


/-- These are precisely the seven rational midpoint-Cayley output fields. -/
def nativeShiftCircles (α B x y : ℚ) (p : ℕ) (i : Fin 7) : Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle :=
  Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.Circle.half (shiftHalf α B x y p i)

/-- Preserve the source flag's exact squared equality, not rounded slack. -/
def nativeShiftSlack (α B x y : ℚ) : Bool := decide ((B-α)^2 ≠ x*x+y*y)

/-- Construction for shift Ideal Circle Value in the native shift preparation model. -/
noncomputable def shiftIdealCircleValue (α B x y : ℚ) (p : ℕ) (i : Fin 7) : ℂ :=
  let t := shiftIdealHalf α B x y p i
  Complex.mk ((1-t^2)/(1+t^2)) (2*t/(1+t^2))

/-- The estimate `nativeShiftCircles_error` retains the actual parameter, input-error and normalization budgets. -/
theorem nativeShiftCircles_error (α B x y : ℚ) (p : ℕ)
    (hα : 0<α) (hB : α ≤ B) (hz : x*x+y*y ≤ (B-α)^2) (i : Fin 7) :
    ‖Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase.gaussianRatComplex
      ((nativeShiftCircles α B x y p i).c,(nativeShiftCircles α B x y p i).s)-
      shiftIdealCircleValue α B x y p i‖ ≤ 1/(2 : ℝ)^(p+13) := by
  change ‖Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase.gaussianRatComplex (Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase.cayleyRat (shiftHalf α B x y p i))-
    Complex.mk ((1-(shiftIdealHalf α B x y p i)^2)/(1+(shiftIdealHalf α B x y p i)^2))
      (2*(shiftIdealHalf α B x y p i)/(1+(shiftIdealHalf α B x y p i)^2))‖ ≤ _
  have hc := nativeHalfCircle_error (shiftHalf α B x y p i) (shiftIdealHalf α B x y p i)
  have ht := shiftHalf_error α B x y p hα hB hz i
  have he : 2*(1/(2 : ℝ)^(p+14))=1/(2 : ℝ)^(p+13) := by
    rw [show p+14=(p+13)+1 by omega,pow_succ]
    ring
  exact hc.trans ((mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 2)).trans_eq he)

end Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data
