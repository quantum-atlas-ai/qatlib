/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.BoolHidShift11.ShiftSample.SampleMath

@[expose] public section


/-! # Actual periods and Fourier annihilators

A period is characterized by vanishing influence and by absence of Fourier
mass crossing its orthogonal hyperplane. No aperiodicity conclusion is stored
as an input field of these equivalences.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.BoolHidShift11.InputModel.SupportMath
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.BoolHidShift11.InputModel.BHSPModel
open Qatlib.Papers.BoolHidShift11.ShiftSample.InfluenceFourier
open Qatlib.Papers.BoolHidShift11.ShiftSample.SampleMath
open scoped BigOperators

/-- An actual XOR period of a Boolean truth table. -/
def IsPeriod {n : ℕ} (f : Reg n → Bool) (v : Reg n) : Prop :=
  ∀ x : Reg n, f x=f (regXor x v)

/-- The two signs encode their Boolean values injectively. -/
theorem signInjective (a b : Bool) :
    (if a then (-1:ℝ) else 1)=(if b then (-1:ℝ) else 1) ↔ a=b := by
  cases a <;> cases b <;> norm_num

/-- Vanishing actual influence is equivalent to a genuine period. -/
theorem influenceZero {n : ℕ} (f : Reg n → Bool) (v : Reg n) :
    influence (signedFun f) v=0 ↔ IsPeriod f v := by
  have hw : uniformWeight n≠0 := by unfold uniformWeight; positivity
  constructor
  · intro h
    unfold influence at h
    have hs := (mul_eq_zero.mp h).resolve_left hw
    intro x
    have hx := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => by
      split_ifs <;> norm_num)).mp hs x (Finset.mem_univ x)
    by_cases he : signedFun f x=signedFun f (regXor x v)
    · exact (signInjective _ _).mp he
    · simp [he] at hx
  · intro h
    unfold influence
    have hs : ∀ x, signedFun f x=signedFun f (regXor x v) := by
      intro x
      exact (signInjective _ _).mpr (h x)
    have hz : (∑ x : Reg n, if signedFun f x=signedFun f (regXor x v)
        then (0:ℝ) else 1)=0 := by
      apply Finset.sum_eq_zero
      intro x _
      rw [hs x]
      simp only [ite_true]
    rw [hz,mul_zero]

/-- A period annihilates every Fourier coefficient of nonzero weight, and conversely. -/
theorem periodSupport {n : ℕ} (f : Reg n → Bool) (v : Reg n) :
    IsPeriod f v ↔ ∀ u : Reg n,
      fourierCoef (signedFun f) u≠0 → parityDot v u=false := by
  have hf := signedSquare f
  constructor
  · intro hp u hu
    have hz := (influenceZero f v).mpr hp
    rw [source_lemma1_influence _ hf] at hz
    by_cases he : parityDot v u=false
    · exact he
    · have hv : parityDot v u=true := by cases h : parityDot v u <;> simp_all
      have heq := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => sq_nonneg
        (fourierCoef (signedFun f) w))).mp hz u (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩)
      exact False.elim (hu (sq_eq_zero_iff.mp heq))
  · intro ha
    apply (influenceZero f v).mp
    rw [source_lemma1_influence _ hf]
    apply Finset.sum_eq_zero
    intro u hu
    have hv := (Finset.mem_filter.mp hu).2
    have hz : fourierCoef (signedFun f) u=0 := by
      by_contra h
      have hh := ha u h
      rw [hv] at hh
      contradiction
    rw [hz]
    norm_num

/-- The Fourier support has trivial annihilator exactly when the function is aperiodic. -/
theorem trivialKernel {n : ℕ} (f : Reg n → Bool) :
    (∀ v : Reg n, IsPeriod f v → v=ZeroStr n) ↔
    ∀ v : Reg n, (∀ u : Reg n, fourierCoef (signedFun f) u≠0 →
      parityDot v u=false) → v=ZeroStr n := by
  constructor
  · intro ha v hv
    exact ha v ((periodSupport f v).mpr hv)
  · intro ha v hv
    exact ha v ((periodSupport f v).mp hv)

end Qatlib.Papers.BoolHidShift11.InputModel.SupportMath
