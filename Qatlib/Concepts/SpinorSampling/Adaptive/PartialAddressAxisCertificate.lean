/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddressFiniteAxisWord
import Mathlib.Algebra.QuadraticAlgebra.Basic

set_option backward.isDefEq.respectTransparency false

/-!
Executable rational/sqrt(2) axis and acceptance checks for actual finite words.
Mathlib QuadraticAlgebra supplies exact arithmetic. The nonnegative predicate
is proved equivalent to the real interpretation, including mixed coefficient
signs and zero. A true literal check yields the real overlap certificate;
actual pilot counter means feed the existing average-risk/minority analysis.
This verifies accepted words, not a search termination or efficient synthesis
claim. Random-training conditional main execution remains a separate bridge.
-/

open Qatlib.Concepts.SpinorSampling.Matching Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords Qatlib.Concepts.SpinorSampling.Retained
set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.AxisCertificate
open FiniteAxisWord AxisRisk
/-- Abbreviation for Quad in the partial address axis certificate model. -/
abbrev Quad := QuadraticAlgebra ℚ 2 0
/-- Construction for evaluate in the partial address axis certificate model. -/
noncomputable def evaluate : Quad →ₐ[ℚ] ℝ :=
  QuadraticAlgebra.lift ⟨Real.sqrt 2,by
    norm_num⟩

/-- Complete original `evaluate_formula` guarantee for `PartialAddressAxisCertificate`; all source hypotheses and output obligations are retained. -/
theorem evaluate_formula (q : Quad) : evaluate q=(q.re : ℝ)+(q.im : ℝ)*Real.sqrt 2 := by
  change q.re • (1 : ℝ)+q.im • Real.sqrt 2=_
  simp only [Algebra.smul_def,mul_one]
  rfl

/-- Complete original `evaluate_C` guarantee for `PartialAddressAxisCertificate`; all source hypotheses and output obligations are retained. -/
@[simp] theorem evaluate_C (r : ℚ) : evaluate (QuadraticAlgebra.C r : Quad)=(r : ℝ) := by
  simp

/-- Construction for q Half in the partial address axis certificate model. -/
def qHalf : Quad := ⟨0,1/2⟩

/-- Complete original `evaluate_half` guarantee for `PartialAddressAxisCertificate`; all source hypotheses and output obligations are retained. -/
theorem evaluate_half : evaluate qHalf=halfRoot := by
  simp [evaluate_formula,qHalf,halfRoot]
  ring

/-- Construction for q Rotate in the partial address axis certificate model. -/
def qRotate (g : Gate) (a : Fin 3 → Quad) : Fin 3 → Quad :=
  match g with
  | .h => ![a 2,-a 1,a 0]
  | .t => ![qHalf*(a 0+a 1),qHalf*(a 1-a 0),a 2]
  | .tdg => ![qHalf*(a 0-a 1),qHalf*(a 0+a 1),a 2]

/-- Construction for q Axis in the partial address axis certificate model. -/
def qAxis : List Gate → Fin 3 → Quad
  | [] => ![0,0,1]
  | g::gs => qRotate g (qAxis gs)

/-- Complete original `evaluate_axis` guarantee for `PartialAddressAxisCertificate`; all source hypotheses and output obligations are retained. -/
theorem evaluate_axis (gs : List Gate) (i : Fin 3) : evaluate (qAxis gs i)=wordAxis gs i := by
  induction gs generalizing i with
  | nil => fin_cases i <;> simp [qAxis,wordAxis]
  | cons g gs ih =>
    cases g <;> fin_cases i <;> simp [qAxis,qRotate,wordAxis,rotate,evaluate_half,ih]

/-- Construction for nonneg in the partial address axis certificate model. -/
def nonneg (q : Quad) : Bool :=
  if 0≤q.re then
    if 0≤q.im then true else decide (2*q.im^2≤q.re^2)
  else if 0≤q.im then decide (q.re^2≤2*q.im^2) else false

/-- Complete original `nonneg_correct` guarantee for `PartialAddressAxisCertificate`; all source hypotheses and output obligations are retained. -/
theorem nonneg_correct (q : Quad) : nonneg q=true ↔ 0≤evaluate q := by
  rw [evaluate_formula]
  have hs : ((q.im : ℝ)*Real.sqrt 2)^2=2*(q.im : ℝ)^2 := by
    rw [mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hs0 : 0≤Real.sqrt 2 := Real.sqrt_nonneg _
  by_cases ha : 0≤q.re <;> by_cases hb : 0≤q.im
  · simp only [nonneg,ite_eq_left ha,ite_eq_left hb,true_iff]
    have ha' : (0 : ℝ)≤q.re := by exact_mod_cast ha
    have hb' : (0 : ℝ)≤q.im := by exact_mod_cast hb
    positivity
  · simp only [nonneg,ite_eq_left ha,ite_eq_right hb,decide_eq_true_eq]
    have ha' : (0 : ℝ)≤q.re := by exact_mod_cast ha
    have hb' : (q.im : ℝ)<0 := by exact_mod_cast lt_of_not_ge hb
    constructor
    · intro h
      have hh : 2*(q.im : ℝ)^2≤(q.re : ℝ)^2 := by exact_mod_cast h
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hb'.le hs0]
    · intro h
      have hh : 2*(q.im : ℝ)^2≤(q.re : ℝ)^2 := by
        nlinarith [mul_nonpos_of_nonpos_of_nonneg hb'.le hs0]
      exact_mod_cast hh
  · simp only [nonneg,ite_eq_right ha,ite_eq_left hb,decide_eq_true_eq]
    have ha' : (q.re : ℝ)<0 := by exact_mod_cast lt_of_not_ge ha
    have hb' : (0 : ℝ)≤q.im := by exact_mod_cast hb
    constructor
    · intro h
      have hh : (q.re : ℝ)^2≤2*(q.im : ℝ)^2 := by exact_mod_cast h
      nlinarith [mul_nonneg hb' hs0]
    · intro h
      have hh : (q.re : ℝ)^2≤2*(q.im : ℝ)^2 := by nlinarith [mul_nonneg hb' hs0]
      exact_mod_cast hh
  · simp only [nonneg,ite_eq_right ha,ite_eq_right hb,Bool.false_eq_true,false_iff,not_le]
    have ha' : (q.re : ℝ)<0 := by exact_mod_cast lt_of_not_ge ha
    have hb' : (q.im : ℝ)<0 := by exact_mod_cast lt_of_not_ge hb
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hb'.le hs0]

/-- Construction for norm Q in the partial address axis certificate model. -/
def normQ (s : Fin 3 → ℚ) : ℚ := ∑ i,s i*s i

/-- Construction for numerator in the partial address axis certificate model. -/
def numerator (s : Fin 3 → ℚ) (gs : List Gate) : Quad :=
  ∑ i,QuadraticAlgebra.C (s i)*qAxis gs i

/-- Construction for check in the partial address axis certificate model. -/
def check (s : Fin 3 → ℚ) (τ : ℚ) (gs : List Gate) : Bool :=
  if normQ s=0 then decide (qAxis gs=qAxis []) else
    nonneg (numerator s gs) &&
      nonneg ((numerator s gs)^2-QuadraticAlgebra.C ((1-τ/64)^2*normQ s))

/-- Complete original `norm_cast` guarantee for `PartialAddressAxisCertificate`; all source hypotheses and output obligations are retained. -/
theorem norm_cast (s : Fin 3 → ℚ) : (normQ s : ℝ)=dot (fun i => (s i : ℝ)) (fun i => (s i : ℝ)) := by
  simp [normQ,dot]

/-- Complete original `numerator_evaluate` guarantee for `PartialAddressAxisCertificate`; all source hypotheses and output obligations are retained. -/
theorem numerator_evaluate (s : Fin 3 → ℚ) (gs : List Gate) :
    evaluate (numerator s gs)=dot (fun i => (s i : ℝ)) (wordAxis gs) := by
  simp [numerator,dot,evaluate_axis]

/-- Complete original `check_sound` guarantee for `PartialAddressAxisCertificate`; all source hypotheses and output obligations are retained. -/
theorem check_sound (s : Fin 3 → ℚ) (τ : ℚ) (gs : List Gate) (hc : check s τ gs=true) :
    accepted (fun i => (s i : ℝ)) (τ : ℝ) gs := by
  have hL : length (fun i => (s i : ℝ))=0 ↔ normQ s=0 := by
    constructor
    · intro h
      have hh := length_sq (fun i => (s i : ℝ))
      rw [h,← norm_cast] at hh
      have hz : (normQ s : ℝ)=0 := by linarith
      exact_mod_cast hz
    · intro h
      unfold length
      rw [← norm_cast,h]
      norm_num
  by_cases hn : normQ s=0
  · have hword : qAxis gs=qAxis [] := by simpa only [check,ite_eq_left hn,decide_eq_true_eq] using hc
    rw [accepted,ite_eq_left (hL.mpr hn)]
    funext i
    rw [← evaluate_axis,← evaluate_axis,hword]
  · have hh : nonneg (numerator s gs)=true ∧
        nonneg ((numerator s gs)^2-QuadraticAlgebra.C ((1-τ/64)^2*normQ s))=true := by
      simpa only [check,ite_eq_right hn,Bool.and_eq_true] using hc
    rw [accepted,ite_eq_right (by exact fun h => hn (hL.mp h))]
    constructor
    · simpa only [numerator_evaluate] using (nonneg_correct (numerator s gs)).mp hh.1
    · have h := (nonneg_correct ((numerator s gs)^2-QuadraticAlgebra.C ((1-τ/64)^2*normQ s))).mp hh.2
      simp only [map_sub,map_pow,evaluate_C,numerator_evaluate,Rat.cast_mul,Rat.cast_pow,
        Rat.cast_sub,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,norm_cast] at h
      linarith

/-- Complete original `checked_overlap` guarantee for `PartialAddressAxisCertificate`; all source hypotheses and output obligations are retained. -/
theorem checked_overlap (s : Fin 3 → ℚ) (τ : ℚ) (gs : List Gate)
    (hτ0 : 0<τ) (hτ1 : τ ≤ 1/2) (hc : check s τ gs=true) :
    1-dot (axis (fun i => (s i : ℝ))) (wordAxis gs) ≤ (τ : ℝ)/64 := by
  have ht : (τ : ℝ)*2≤1 := by exact_mod_cast (show τ*2≤1 by linarith)
  apply accepted_overlap _ _ _ (by exact_mod_cast hτ0) (by linarith)
  exact check_sound s τ gs hc

/-- Complete original `checked_axis_risk` guarantee for `PartialAddressAxisCertificate`; all source hypotheses and output obligations are retained. -/
theorem checked_axis_risk (r : Fin 3 → ℝ) (s : Fin 3 → ℚ) (τ : ℚ) (gs : List Gate)
    (hr : length r ≤ 1) (hτ0 : 0<τ) (hτ1 : τ ≤ 1/2) (hc : check s τ gs=true) :
    (1-dot r (wordAxis gs))/2 ≤ 8*((1-length r)/2)+
      4*distSq (fun i => (s i : ℝ)) r+(τ : ℝ)/32 := by
  apply compiled_axis_risk _ _ _ _ hr (word_axis_unit gs)
  have h := checked_overlap s τ gs hτ0 hτ1 hc
  have ht : (0 : ℝ)<τ := by exact_mod_cast hτ0
  linarith

variable {B A : Type} [Fintype B] [Fintype A] [Nonempty B] [Nonempty A]
  [DecidableEq B] [DecidableEq A]

omit [Nonempty A] [DecidableEq A] in
/-- Complete original `checked_average_risk` guarantee for `PartialAddressAxisCertificate`; all source hypotheses and output obligations are retained. -/
theorem checked_average_risk {n : ℕ} (m : Fin 3 → B × A → ℝ)
    (Ω : Fin 3 → Fin n → (B × A) × Bool) (words : B → List Gate) (τ : ℚ)
    (hr : ∀ b,length (PilotVector.boxVector m b) ≤ 1)
    (hτ0 : 0<τ) (hτ1 : τ ≤ 1/2)
    (hc : ∀ b,check (fun h => PilotProjection.counterMeanQ b (Ω h)) τ (words b)=true) :
    PilotVector.averageMinority m (fun b => wordAxis (words b)) ≤
      8*PilotVector.averageDefect m+4*PilotVector.averageError m Ω+(τ : ℝ)/32 := by
  apply PilotVector.average_compiled_risk m Ω _ (τ : ℝ) hr (fun b => word_axis_unit (words b))
  intro b
  have h := checked_overlap (fun h => PilotProjection.counterMeanQ b (Ω h)) τ (words b) hτ0 hτ1 (hc b)
  have ht : (0 : ℝ)<τ := by exact_mod_cast hτ0
  change 1-dot (axis (fun h => (PilotProjection.counterMeanQ b (Ω h) : ℝ))) (wordAxis (words b)) ≤ _
  linarith

omit [Nonempty A] [DecidableEq A] in
/-- Complete original `checked_good_minority` guarantee for `PartialAddressAxisCertificate`; all source hypotheses and output obligations are retained. -/
theorem checked_good_minority {n : ℕ} (m : Fin 3 → B × A → ℝ)
    (Ω : Fin 3 → Fin n → (B × A) × Bool) (words : B → List Gate) (τ : ℚ)
    (hr : ∀ b,length (PilotVector.boxVector m b) ≤ 1)
    (hτ0 : 0<τ) (hτ1 : τ ≤ 1/2)
    (hc : ∀ b,check (fun h => PilotProjection.counterMeanQ b (Ω h)) τ (words b)=true)
    (hq : PilotVector.averageDefect m ≤ (τ : ℝ)/32)
    (he : PilotVector.averageError m Ω ≤ (τ : ℝ)/16) :
    PilotVector.averageMinority m (fun b => wordAxis (words b)) ≤ 17*(τ : ℝ)/32 := by
  have h := checked_average_risk m Ω words τ hr hτ0 hτ1 hc
  linarith

#print axioms evaluate_formula
#print axioms evaluate_C
#print axioms evaluate_half
#print axioms evaluate_axis
#print axioms nonneg_correct
#print axioms norm_cast
#print axioms numerator_evaluate
#print axioms check_sound
#print axioms checked_overlap
#print axioms checked_axis_risk
#print axioms checked_average_risk
#print axioms checked_good_minority
end Qatlib.Concepts.SpinorSampling.Adaptive.PartialAddress.AxisCertificate
