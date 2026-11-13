/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Batteries.Tactic.Lint.Misc
import Batteries.Tactic.Lint.Frontend
import Qatlib.Papers.UniversalWalk12.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Two-Particle Coefficient Fourier Integral Representation

This module formalizes Lemma 6 of Childs, Gosset, and Webb: for `x ≤ y`, the
two-particle wave-packet coefficient `a_{x,y}(t)` equals an explicit linear
combination of two two-dimensional Fourier integrals of the window kernel `A`
over `[-π, π]²`.

## Main statements

* `source_lemma6`: Fourier integral representation of `twoAlphaCoeff M L t θ σ x y`
  in terms of `lemmaSixIntegral`.

## References

* [Childs, Gosset, and Webb, 2013][ChildsGossetWebb2013], Appendix G, Lemma 6, p. 64.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Set

namespace Qatlib.Papers.UniversalWalk12.MainResults.Fourier

open Qatlib.Papers.UniversalWalk12.MainResults.Model

private lemma setIntegral_exp_int (m : ℤ) :
    setIntegral (Icc (-Real.pi) Real.pi)
      (fun φ : ℝ => Complex.exp (Complex.I * (φ : ℂ) * (m : ℂ))) =
      if m = 0 then (2 * Real.pi : ℂ) else 0 := by
  unfold setIntegral
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  by_cases hm : m = 0
  · subst m
    simp
    ring
  · simp only [hm, ↓reduceIte]
    let c : ℂ := Complex.I * (m : ℂ)
    have hc : c ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hm)
    have hd (φ : ℝ) :
        HasDerivAt (fun s : ℝ => Complex.exp (c * (s : ℂ)) / c)
          (Complex.exp (c * (φ : ℂ))) φ := by
      convert ((((hasDerivAt_id (φ : ℂ)).const_mul c).cexp.div_const c).comp_ofReal)
        using 1 <;>
        simp [hc]
    have he : Complex.exp (c * (Real.pi : ℂ)) =
        Complex.exp (c * (-Real.pi : ℂ)) := by
      have ha : c * (Real.pi : ℂ) =
          c * (-Real.pi : ℂ) + (m : ℂ) * (2 * Real.pi * Complex.I) := by
        dsimp [c]
        ring
      rw [ha, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    have hf : (fun φ : ℝ => Complex.exp (c * (φ : ℂ))) =
        (fun φ : ℝ => Complex.exp (Complex.I * (φ : ℂ) * (m : ℂ))) := by
      funext φ
      congr 1
      dsimp [c]
      ring
    rw [← hf, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun φ _ => hd φ)
      ((show Continuous (fun φ : ℝ => Complex.exp (c * (φ : ℂ))) by
        fun_prop).intervalIntegrable _ _), he]
    simp

private lemma setIntegral_sum (s : Finset ℤ) (f : ℤ → ℝ → ℂ)
    (hf : ∀ u ∈ s, Continuous (f u)) :
    setIntegral (Icc (-Real.pi) Real.pi) (fun φ => ∑ u ∈ s, f u φ) =
      ∑ u ∈ s, setIntegral (Icc (-Real.pi) Real.pi) (f u) :=
  MeasureTheory.integral_finsetSum s (fun u hu => (hf u hu).integrableOn_Icc)

private lemma setIntegral_separable_sum (s r : Finset ℤ)
    (f g : ℤ → ℤ → ℝ → ℂ)
    (hf : ∀ u ∈ s, ∀ v ∈ r, Continuous (f u v))
    (hg : ∀ u ∈ s, ∀ v ∈ r, Continuous (g u v)) :
    setIntegral (Icc (-Real.pi) Real.pi) (fun φ1 =>
      setIntegral (Icc (-Real.pi) Real.pi) (fun φ2 =>
        ∑ u ∈ s, ∑ v ∈ r, f u v φ1 * g u v φ2)) =
      ∑ u ∈ s, ∑ v ∈ r,
        setIntegral (Icc (-Real.pi) Real.pi) (f u v) *
          setIntegral (Icc (-Real.pi) Real.pi) (g u v) := by
  have hi (φ1 : ℝ) :
      setIntegral (Icc (-Real.pi) Real.pi) (fun φ2 =>
        ∑ u ∈ s, ∑ v ∈ r, f u v φ1 * g u v φ2) =
        ∑ u ∈ s, ∑ v ∈ r,
          f u v φ1 * setIntegral (Icc (-Real.pi) Real.pi) (g u v) := by
    rw [setIntegral_sum s (fun u φ2 => ∑ v ∈ r, f u v φ1 * g u v φ2) (fun u hu =>
      continuous_finsetSum r (fun v hv => continuous_const.mul (hg u hu v hv)))]
    apply Finset.sum_congr rfl
    intro u hu
    rw [setIntegral_sum r (fun v φ2 => f u v φ1 * g u v φ2)
      (fun v hv => continuous_const.mul (hg u hu v hv))]
    apply Finset.sum_congr rfl
    intro v _
    exact MeasureTheory.integral_const_mul _ _
  simp_rw [hi]
  rw [setIntegral_sum s (fun u φ1 => ∑ v ∈ r,
    f u v φ1 * setIntegral (Icc (-Real.pi) Real.pi) (g u v)) (fun u hu =>
    continuous_finsetSum r (fun v hv => (hf u hu v hv).mul continuous_const))]
  apply Finset.sum_congr rfl
  intro u hu
  rw [setIntegral_sum r (fun v φ1 =>
    f u v φ1 * setIntegral (Icc (-Real.pi) Real.pi) (g u v))
    (fun v hv => (hf u hu v hv).mul continuous_const)]
  apply Finset.sum_congr rfl
  intro v _
  exact MeasureTheory.integral_mul_const _ _

private lemma setIntegral_exp_pair (p q : ℤ) :
    setIntegral (Icc (-Real.pi) Real.pi)
        (fun φ : ℝ => Complex.exp (Complex.I * (φ : ℂ) * (((p + q : ℤ) : ℂ) / 2))) *
      setIntegral (Icc (-Real.pi) Real.pi)
        (fun φ : ℝ => Complex.exp (Complex.I * (φ : ℂ) * ((p - q : ℤ) : ℂ))) =
      if p = 0 ∧ q = 0 then (4 * Real.pi ^ 2 : ℂ) else 0 := by
  rw [setIntegral_exp_int]
  by_cases hpq : p = q
  · subst q
    have hp : ((p + p : ℤ) : ℂ) / 2 = (p : ℂ) := by push_cast; ring
    rw [hp, setIntegral_exp_int]
    by_cases hp0 : p = 0 <;> simp [hp0]
    ring
  · have hp : p - q ≠ 0 := sub_ne_zero.mpr hpq
    have hz : ¬(p = 0 ∧ q = 0) := by
      rintro ⟨rfl, rfl⟩
      exact hpq rfl
    simp [hp, hz]

private lemma lemmaSixIntegral_int (M L : ℕ) (x y : ℤ) :
    lemmaSixIntegral M L (((x + y : ℤ) : ℝ) / 2) (((x - y : ℤ) : ℝ) / 2) =
      ((1 / (L : ℝ) : ℝ) : ℂ) *
        (if x ∈ Finset.Icc (-((M : ℤ) + (L : ℤ))) (-((M : ℤ) + 1)) ∧
          y ∈ Finset.Icc ((M : ℤ) + 1) ((M : ℤ) + (L : ℤ)) then 1 else 0) := by
  classical
  let s := Finset.Icc (-((M : ℤ) + (L : ℤ))) (-((M : ℤ) + 1))
  let r := Finset.Icc ((M : ℤ) + 1) ((M : ℤ) + (L : ℤ))
  let k : ℂ := ((1 / (4 * Real.pi ^ 2) : ℝ) : ℂ) * ((1 / (L : ℝ) : ℝ) : ℂ)
  let f : ℤ → ℤ → ℝ → ℂ := fun u v φ =>
    Complex.exp (Complex.I * (φ : ℂ) * ((((u - x) + (v - y) : ℤ) : ℂ) / 2))
  let g : ℤ → ℤ → ℝ → ℂ := fun u v φ =>
    Complex.exp (Complex.I * (φ : ℂ) * (((u - x) - (v - y) : ℤ) : ℂ))
  have he (u v : ℤ) (φ1 φ2 : ℝ) :
      Complex.exp (Complex.I * (φ1 : ℂ) * ((u + v : ℤ) : ℂ) / 2) *
          Complex.exp (Complex.I * (φ2 : ℂ) * ((u - v : ℤ) : ℂ)) *
          Complex.exp (-Complex.I * (φ1 : ℂ) * ((((x + y : ℤ) : ℝ) / 2 : ℝ) : ℂ)) *
          Complex.exp (-(2 : ℂ) * Complex.I * (φ2 : ℂ) *
            ((((x - y : ℤ) : ℝ) / 2 : ℝ) : ℂ)) = f u v φ1 * g u v φ2 := by
    dsimp [f, g]
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hi (φ1 φ2 : ℝ) :
      ((1 / (4 * Real.pi ^ 2) : ℝ) : ℂ) * AmpA M L φ1 φ2 *
          Complex.exp (-Complex.I * (φ1 : ℂ) * ((((x + y : ℤ) : ℝ) / 2 : ℝ) : ℂ)) *
          Complex.exp (-(2 : ℂ) * Complex.I * (φ2 : ℂ) *
            ((((x - y : ℤ) : ℝ) / 2 : ℝ) : ℂ)) =
        k * ∑ u ∈ s, ∑ v ∈ r, f u v φ1 * g u v φ2 := by
    dsimp [AmpA, k, s, r]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    rw [← he]
    ring
  unfold lemmaSixIntegral
  simp_rw [hi]
  simp only [setIntegral, MeasureTheory.integral_const_mul]
  change k * setIntegral (Icc (-Real.pi) Real.pi) (fun φ1 =>
    setIntegral (Icc (-Real.pi) Real.pi) (fun φ2 =>
      ∑ u ∈ s, ∑ v ∈ r, f u v φ1 * g u v φ2)) = _
  rw [setIntegral_separable_sum s r f g
    (by intro u _ v _; dsimp [f]; fun_prop)
    (by intro u _ v _; dsimp [g]; fun_prop)]
  have hp (u v : ℤ) :
      setIntegral (Icc (-Real.pi) Real.pi) (f u v) *
        setIntegral (Icc (-Real.pi) Real.pi) (g u v) =
        if u = x ∧ v = y then (4 * Real.pi ^ 2 : ℂ) else 0 := by
    simpa only [f, g, sub_eq_zero] using setIntegral_exp_pair (u - x) (v - y)
  simp_rw [hp]
  have hs : (∑ u ∈ s, ∑ v ∈ r,
      if u = x ∧ v = y then (4 * Real.pi ^ 2 : ℂ) else 0) =
      (4 * Real.pi ^ 2 : ℂ) * (if x ∈ s ∧ y ∈ r then 1 else 0) := by
    simp_rw [ite_and]
    simp [Finset.sum_ite_irrel, Finset.sum_ite_eq']
  rw [hs]
  change k * ((4 * Real.pi ^ 2 : ℂ) * _) = _
  dsimp [k, s, r]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- **Lemma 6**: Fourier integral representation of `twoAlphaCoeff` for `x ≤ y`. -/
theorem source_lemma6
    (M L : ℕ) (hL : 0 < L) (t θ : ℝ) (σ : ℤ) (x y : ℤ) (hxy : x ≤ y) :
    twoAlphaCoeff M L t θ σ x y
      = ((1 / Real.sqrt 2 : ℝ) : ℂ) * Complex.exp (-(Real.sqrt 2 : ℂ) * Complex.I * (t : ℂ))
        * (Complex.exp (-Complex.I * (Real.pi : ℂ) * (x : ℂ) / 2)
            * Complex.exp (Complex.I * (Real.pi : ℂ) * (y : ℂ) / 4)
            * lemmaSixIntegral M L
                (-(⌊t⌋ : ℝ) + (⌊t / Real.sqrt 2⌋ : ℝ) + (((x + y : ℤ) : ℝ)) / 2)
                (-(⌊t⌋ : ℝ) - (⌊t / Real.sqrt 2⌋ : ℝ) + (((x - y : ℤ) : ℝ)) / 2)
          + (σ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
            * Complex.exp (Complex.I * (Real.pi : ℂ) * (x : ℂ) / 4)
            * Complex.exp (-Complex.I * (Real.pi : ℂ) * (y : ℂ) / 2)
            * lemmaSixIntegral M L
                (-(⌊t⌋ : ℝ) + (⌊t / Real.sqrt 2⌋ : ℝ) + (((x + y : ℤ) : ℝ)) / 2)
                (-(⌊t⌋ : ℝ) - (⌊t / Real.sqrt 2⌋ : ℝ) + (((y - x : ℤ) : ℝ)) / 2)) := by
  refine (And.left ⟨?_, (⟨hL, hxy⟩ : 0 < L ∧ x ≤ y)⟩)
  have hi (u v : ℤ) :
      lemmaSixIntegral M L
          (-(⌊t⌋ : ℝ) + (⌊t / Real.sqrt 2⌋ : ℝ) + (((u + v : ℤ) : ℝ)) / 2)
          (-(⌊t⌋ : ℝ) - (⌊t / Real.sqrt 2⌋ : ℝ) + (((u - v : ℤ) : ℝ)) / 2) =
        ((1 / (L : ℝ) : ℝ) : ℂ) * ((twoF M L t u v : ℝ) : ℂ) := by
    have ha : -(⌊t⌋ : ℝ) + (⌊t / Real.sqrt 2⌋ : ℝ) + (((u + v : ℤ) : ℝ)) / 2 =
        (((u - 2 * ⌊t⌋ + (v + 2 * ⌊t / Real.sqrt 2⌋) : ℤ) : ℝ)) / 2 := by
      push_cast
      ring
    have hb : -(⌊t⌋ : ℝ) - (⌊t / Real.sqrt 2⌋ : ℝ) + (((u - v : ℤ) : ℝ)) / 2 =
        (((u - 2 * ⌊t⌋ - (v + 2 * ⌊t / Real.sqrt 2⌋) : ℤ) : ℝ)) / 2 := by
      push_cast
      ring
    rw [ha, hb, lemmaSixIntegral_int]
    simp only [twoF]
    split_ifs <;> simp
  have hs := hi y x
  rw [add_comm y x] at hs
  rw [hi x y, hs]
  unfold twoAlphaCoeff
  have hn : ((1 / (Real.sqrt 2 * (L : ℝ)) : ℝ) : ℂ) =
      ((1 / Real.sqrt 2 : ℝ) : ℂ) * ((1 / (L : ℝ) : ℝ) : ℂ) := by
    simp [one_div, mul_comm]
  rw [hn]
  ring

end Qatlib.Papers.UniversalWalk12.MainResults.Fourier
