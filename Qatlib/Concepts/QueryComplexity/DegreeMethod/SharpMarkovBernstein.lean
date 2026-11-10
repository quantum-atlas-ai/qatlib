/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.ByCases
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Qatlib.Concepts.QueryComplexity.DegreeMethod.SharpMarkovHelpers
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Topology.Algebra.Polynomial
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Polynomial
open scoped Real BigOperators

section Bernstein

def sharpBernsteinTrig (p : ℝ[X]) (θ : ℝ) : ℝ := p.eval (Real.cos θ)

theorem sharpBernsteinTrig_hasDerivAt (p : ℝ[X]) (θ : ℝ) :
    HasDerivAt (sharpBernsteinTrig p)
      (p.derivative.eval (Real.cos θ) * (-(Real.sin θ))) θ :=
  (p.hasDerivAt (Real.cos θ)).comp θ (Real.hasDerivAt_cos θ)

theorem sharpBernsteinTrig_continuous (p : ℝ[X]) : Continuous (sharpBernsteinTrig p) :=
  p.continuous.comp Real.continuous_cos

theorem exists_zero_of_mul_lt {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Set.Icc a b)) (hf : f a * f b < 0) :
    ∃ ζ, a < ζ ∧ ζ < b ∧ f ζ = 0 := by
  by_cases h1 : f a < 0
  · have hfb : 0 < f b := by
      by_contra hcon
      have hcon' : f b ≤ 0 := not_lt.mp hcon
      have h1' : (0 : ℝ) ≤ -(f a) := neg_nonneg.mpr (le_of_lt h1)
      have h2' : (0 : ℝ) ≤ -(f b) := neg_nonneg.mpr hcon'
      have hnn0 := mul_nonneg h1' h2'
      rw [neg_mul_neg] at hnn0
      linarith [hf]
    have hmem : (0 : ℝ) ∈ Set.Icc (f a) (f b) :=
      ⟨by linarith, by linarith⟩
    obtain ⟨c, hcmem, hcf⟩ := intermediate_value_Icc hab.le hc hmem
    obtain ⟨hc1, hc2⟩ := hcmem
    refine ⟨c, ?_, ?_, hcf⟩
    · exact lt_of_le_of_ne hc1 (by
        intro hcon
        rw [← hcon] at hcf
        linarith [h1])
    · exact lt_of_le_of_ne hc2 (by
        intro hcon
        rw [hcon] at hcf
        linarith [hfb])
  · have hfa : 0 < f a := by
      by_contra hcon
      have hcon' : f a ≤ 0 := not_lt.mp hcon
      have hzero : f a = 0 := le_antisymm hcon' (not_lt.mp h1)
      rw [hzero] at hf
      simp at hf
    have hfb : f b < 0 := by
      by_contra hcon
      have hcon' : 0 ≤ f b := not_lt.mp hcon
      have hnn : 0 ≤ f a * f b := mul_nonneg (le_of_lt hfa) hcon'
      linarith [hf]
    have hmem : (0 : ℝ) ∈ Set.Icc (f b) (f a) :=
      ⟨by linarith, by linarith⟩
    obtain ⟨c, hcmem, hcf⟩ := intermediate_value_Icc' hab.le hc hmem
    obtain ⟨hc1, hc2⟩ := hcmem
    refine ⟨c, ?_, ?_, hcf⟩
    · exact lt_of_le_of_ne hc1 (by
        intro hcon
        rw [← hcon] at hcf
        linarith [hfa])
    · exact lt_of_le_of_ne hc2 (by
        intro hcon
        rw [hcon] at hcf
        linarith [hfb])

private theorem tone_aux {czr szr Ãr Btr : ℝ} (h : czr * czr + szr * szr = 1) :
    ((((Ãr : ℝ) : ℂ) - ((Btr : ℝ) : ℂ) * Complex.I) / 2) *
        ((((czr : ℝ) : ℂ) + ((szr : ℝ) : ℂ) * Complex.I) *
          (((czr : ℝ) : ℂ) + ((szr : ℝ) : ℂ) * Complex.I)) +
      (((Ãr : ℝ) : ℂ) + ((Btr : ℝ) : ℂ) * Complex.I) / 2 =
    (((czr : ℝ) : ℂ) + ((szr : ℝ) : ℂ) * Complex.I) *
      (((Ãr : ℝ) : ℂ) * ((czr : ℝ) : ℂ) + ((Btr : ℝ) : ℂ) * ((szr : ℝ) : ℂ)) := by
  have hÃterm : Ãr * (czr * czr + szr * szr) = Ãr * 1 := by rw [h]
  have hBterm : Btr * (czr * czr + szr * szr) = Btr * 1 := by rw [h]
  field_simp
  rw [Complex.ext_iff]
  constructor <;>
    simp only [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] <;>
    norm_num <;>
    nlinarith [hÃterm, hBterm]

theorem sharpBernstein_lift_poly (d : ℕ) (p : ℝ[X]) (hdeg : p.natDegree ≤ d) (θ : ℝ) :
    (∑ j ∈ Finset.range (d + 1),
      Polynomial.C (((p.coeff j : ℝ) : ℂ) * ((2 : ℝ)⁻¹ ^ j : ℝ)) *
        (Polynomial.X ^ (d - j) * (Polynomial.X ^ 2 + 1) ^ j)).eval
      (Complex.exp (θ * Complex.I)) =
    (Complex.exp (θ * Complex.I)) ^ d * ((p.eval (Real.cos θ) : ℝ) : ℂ) := by
  set z := Complex.exp (θ * Complex.I) with hz
  set c := ((Real.cos θ : ℝ) : ℂ) with hc
  have hcs : (Real.cos θ) * (Real.cos θ) + (Real.sin θ) * (Real.sin θ) = 1 := by
    have h0 := Real.sin_sq_add_cos_sq θ
    rw [sq, sq] at h0
    linarith [h0]
  have hz2 : z ^ 2 + 1 = 2 * z * c := by
    have hexp : Complex.exp ((θ : ℝ) * Complex.I) =
        ((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * Complex.I := by
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [hz, hexp, Complex.ext_iff]
    constructor <;>
      simp only [pow_two, hc, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.one_re, Complex.one_im] <;>
      norm_num <;>
      nlinarith [hcs]
  have hterm : ∀ j ∈ Finset.range (d + 1),
      (Polynomial.C (((p.coeff j : ℝ) : ℂ) * ((2 : ℝ)⁻¹ ^ j : ℝ)) *
        (Polynomial.X ^ (d - j) * (Polynomial.X ^ 2 + 1) ^ j)).eval z =
      ((p.coeff j : ℝ) : ℂ) * (z ^ d * c ^ j) := by
    intro j hj
    have hjd : j ≤ d := Finset.mem_range_succ_iff.mp hj
    simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
    rw [hz2]
    have hp3 : (2 * z * c) ^ j = ((2 : ℝ) ^ j : ℝ) * (z ^ j * c ^ j) := by
      rw [mul_pow, mul_pow]
      push_cast
      ring
    rw [hp3]
    have hu2 : (((2 : ℝ)⁻¹ ^ j : ℝ) : ℂ) * (((2 : ℝ) ^ j : ℝ) : ℂ) = 1 := by
      have hreal : ((2 : ℝ)⁻¹ ^ j : ℝ) * ((2 : ℝ) ^ j : ℝ) = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ (by norm_num), one_pow]
      exact_mod_cast hreal
    have hzp : z ^ (d - j) * z ^ j = z ^ d := by
      rw [← pow_add, Nat.sub_add_cancel hjd]
    linear_combination ((p.coeff j : ℝ) : ℂ) * (z ^ (d - j) * (z ^ j * c ^ j)) * hu2
      + ((p.coeff j : ℝ) : ℂ) * c ^ j * hzp
  have hterm2 : ∀ j ∈ Finset.range (d + 1),
      (Polynomial.C (((p.coeff j : ℝ) : ℂ) * ((2 : ℝ)⁻¹ ^ j : ℝ)) *
        (Polynomial.X ^ (d - j) * (Polynomial.X ^ 2 + 1) ^ j)).eval z =
      z ^ d * (((p.coeff j : ℝ) : ℂ) * c ^ j) := by
    intro j hj
    rw [hterm j hj]
    ring
  rw [Polynomial.eval_finsetSum, Finset.sum_congr rfl (fun j hj => hterm2 j hj),
    ← Finset.mul_sum]
  have hpsum : ∑ j ∈ Finset.range (d + 1),
      ((p.coeff j : ℝ) : ℂ) * c ^ j = ((p.eval (Real.cos θ) : ℝ) : ℂ) := by
    have hrange : Finset.range (p.natDegree + 1) ⊆ Finset.range (d + 1) := by
      intro j hj
      rw [Finset.mem_range] at hj ⊢
      omega
    rw [Polynomial.eval_eq_sum_range]
    rw [Finset.sum_subset hrange ?_]
    · rw [hc]
      push_cast
      rfl
    · intro j _ hj'
      rw [Finset.mem_range] at hj'
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp
  rw [hpsum]

theorem sharpBernstein_lift_tone (Ã Bt : ℝ) (d : ℕ) (θ : ℝ) :
    (Polynomial.C ((((Ã : ℝ) : ℂ) - ((Bt : ℝ) : ℂ) * Complex.I) / 2) * Polynomial.X ^ (2 * d)
      + Polynomial.C ((((Ã : ℝ) : ℂ) + ((Bt : ℝ) : ℂ) * Complex.I) / 2)).eval
      (Complex.exp (θ * Complex.I)) =
    (Complex.exp (θ * Complex.I)) ^ d *
      (((Ã : ℝ) : ℂ) * ((Real.cos ((d : ℝ) * θ) : ℝ) : ℂ) +
        ((Bt : ℝ) : ℂ) * ((Real.sin ((d : ℝ) * θ) : ℝ) : ℂ)) := by
  set z := Complex.exp (θ * Complex.I) with hz
  have hcs : (Real.cos ((d : ℝ) * θ)) * (Real.cos ((d : ℝ) * θ)) +
      (Real.sin ((d : ℝ) * θ)) * (Real.sin ((d : ℝ) * θ)) = 1 := by
    have h0 := Real.sin_sq_add_cos_sq ((d : ℝ) * θ)
    rw [sq, sq] at h0
    linarith [h0]
  have hzd : z ^ d =
      (((Real.cos ((d : ℝ) * θ) : ℝ) : ℂ) + ((Real.sin ((d : ℝ) * θ) : ℝ) : ℂ) * Complex.I) := by
    have h1 : z ^ d = Complex.exp ((((d : ℝ) * θ : ℝ) : ℂ) * Complex.I) := by
      rw [hz, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [h1, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [eval_mul, eval_add, eval_C, eval_pow, eval_X]
  rw [show z ^ (2 * d) =
      ((((Real.cos ((d : ℝ) * θ) : ℝ) : ℂ) + ((Real.sin ((d : ℝ) * θ) : ℝ) : ℂ) * Complex.I) *
        (((Real.cos ((d : ℝ) * θ) : ℝ) : ℂ) + ((Real.sin ((d : ℝ) * θ) : ℝ) : ℂ) * Complex.I)) from by
      rw [show 2 * d = d + d from by omega, pow_add, hzd], hzd]
  exact tone_aux hcs

theorem sharpBernstein_violation (d : ℕ) (hd1 : 1 ≤ d) (p : ℝ[X]) (hdeg : p.natDegree ≤ d)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ θ : ℝ, |p.eval (Real.cos θ)| ≤ C) (η : ℝ)
    (hw : d * C < p.derivative.eval (Real.cos η) * (-(Real.sin η))) : False := by
  have hdR : (d : ℝ) ≠ 0 := by positivity
  have hdR' : 0 < (d : ℝ) := by positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  obtain ⟨Ã, hÃdef⟩ : ∃ Ã : ℝ, Ã = p.eval (Real.cos η) * Real.cos ((d : ℝ) * η) -
      (p.derivative.eval (Real.cos η) * (-(Real.sin η)) / (d : ℝ)) * Real.sin ((d : ℝ) * η) :=
    ⟨_, rfl⟩
  obtain ⟨Bt, hBtdef⟩ : ∃ Bt : ℝ, Bt = p.eval (Real.cos η) * Real.sin ((d : ℝ) * η) +
      (p.derivative.eval (Real.cos η) * (-(Real.sin η)) / (d : ℝ)) * Real.cos ((d : ℝ) * η) :=
    ⟨_, rfl⟩
  have hw'η : HasDerivAt (sharpBernsteinTrig p)
      (p.derivative.eval (Real.cos η) * (-(Real.sin η))) η := sharpBernsteinTrig_hasDerivAt p η
  have hwpos : 0 < p.derivative.eval (Real.cos η) * (-(Real.sin η)) := by
    nlinarith [hw, hC, hdR']
  have hCB : C < |p.derivative.eval (Real.cos η) * (-(Real.sin η)) / (d : ℝ)| := by
    rw [abs_div, abs_of_pos hdR', abs_of_pos hwpos]
    exact (lt_div_iff₀ hdR').mpr (by rwa [mul_comm])
  have hRdef : Real.sqrt ((p.eval (Real.cos η)) ^ 2 +
      (p.derivative.eval (Real.cos η) * (-(Real.sin η)) / (d : ℝ)) ^ 2) =
      Real.sqrt (Ã ^ 2 + Bt ^ 2) := by
    rw [hÃdef, hBtdef]
    congr 1
    have hcs : (Real.cos ((d : ℝ) * η)) ^ 2 + (Real.sin ((d : ℝ) * η)) ^ 2 = 1 := by
      have := Real.sin_sq_add_cos_sq ((d : ℝ) * η)
      linarith [this]
    nlinarith [hcs]
  set R := Real.sqrt (Ã ^ 2 + Bt ^ 2) with hR
  have hR2 : R * R = Ã ^ 2 + Bt ^ 2 := by
    have := Real.sq_sqrt (by positivity : 0 ≤ Ã ^ 2 + Bt ^ 2)
    rw [sq] at this
    exact this
  have hsum : Ã ^ 2 + Bt ^ 2 = (p.eval (Real.cos η)) ^ 2 +
      (p.derivative.eval (Real.cos η) * (-(Real.sin η)) / (d : ℝ)) ^ 2 := by
    have h1 := Real.sqrt_inj (by positivity) (by positivity) |>.mp hRdef
    exact h1.symm
  have hRpos : 0 < R := by
    have hne : p.derivative.eval (Real.cos η) * (-(Real.sin η)) / (d : ℝ) ≠ 0 :=
      abs_pos.mp (lt_of_le_of_lt hC hCB)
    have h1 : 0 < (p.derivative.eval (Real.cos η) * (-(Real.sin η)) / (d : ℝ)) ^ 2 :=
      sq_pos_of_ne_zero hne
    apply Real.sqrt_pos.mpr
    rw [hsum]
    nlinarith [h1, sq_nonneg (p.eval (Real.cos η))]
  have hCR : C < R := by
    have habsle : |p.derivative.eval (Real.cos η) * (-(Real.sin η)) / (d : ℝ)| ≤ R := by
      refine le_of_sq_le_sq ?_ (le_of_lt hRpos)
      rw [sq_abs, show R ^ 2 = R * R from sq R, hR2, hsum]
      nlinarith [sq_nonneg (p.eval (Real.cos η))]
    exact lt_of_lt_of_le hCB habsle

  obtain ⟨q, hq⟩ : ∃ q : ℝ → ℝ, ∀ θ, q θ =
      Ã * Real.cos ((d : ℝ) * θ) + Bt * Real.sin ((d : ℝ) * θ) := ⟨_, fun _ => rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, ∀ θ, g θ = sharpBernsteinTrig p θ - q θ := ⟨_, fun _ => rfl⟩
  have hgc : Continuous g := by
    have hfun : ∀ t, g t = sharpBernsteinTrig p t -
        (Ã * Real.cos ((d : ℝ) * t) + Bt * Real.sin ((d : ℝ) * t)) := by
      intro t
      rw [hg t, hq t]
    have hfeq : g = fun t => sharpBernsteinTrig p t -
        (Ã * Real.cos ((d : ℝ) * t) + Bt * Real.sin ((d : ℝ) * t)) := funext hfun
    rw [hfeq]
    exact (sharpBernsteinTrig_continuous p).sub
      (Continuous.add (continuous_const.mul (by fun_prop))
        (continuous_const.mul (by fun_prop)))
  have hqη : q η = p.eval (Real.cos η) := by
    have hcs : (Real.cos ((d : ℝ) * η)) ^ 2 + (Real.sin ((d : ℝ) * η)) ^ 2 = 1 := by
      have := Real.sin_sq_add_cos_sq ((d : ℝ) * η)
      linarith [this]
    rw [hq η, hÃdef, hBtdef]
    have hAc : (p.eval (Real.cos η)) *
        ((Real.cos ((d : ℝ) * η)) ^ 2 + (Real.sin ((d : ℝ) * η)) ^ 2) =
        p.eval (Real.cos η) := by rw [hcs, mul_one]
    nlinarith [hAc]
  have hgη : g η = 0 := by
    rw [hg η, hqη]
    simp [sharpBernsteinTrig]
  have hqderiv : ∀ θ : ℝ,
      HasDerivAt q (Ã * (-(Real.sin ((d : ℝ) * θ)) * (d : ℝ)) +
        Bt * (Real.cos ((d : ℝ) * θ) * (d : ℝ))) θ := by
    intro θ
    have hmul : HasDerivAt (fun θ => (d : ℝ) * θ) (d : ℝ) θ := by
      simpa using (hasDerivAt_id θ).const_mul (d : ℝ)
    have hc := (Real.hasDerivAt_cos ((d : ℝ) * θ)).comp θ hmul
    have hs := (Real.hasDerivAt_sin ((d : ℝ) * θ)).comp θ hmul
    have h1 : HasDerivAt (fun s => Ã * Real.cos ((d : ℝ) * s))
        (Ã * (-(Real.sin ((d : ℝ) * θ)) * (d : ℝ))) θ := hc.const_mul Ã
    have h2 : HasDerivAt (fun s => Bt * Real.sin ((d : ℝ) * s))
        (Bt * (Real.cos ((d : ℝ) * θ) * (d : ℝ))) θ := hs.const_mul Bt
    exact (h1.add h2).congr_of_eventuallyEq
      (Filter.Eventually.of_forall hq)
  have hq'η : HasDerivAt q (p.derivative.eval (Real.cos η) * (-(Real.sin η))) η := by
    have hval := hqderiv η
    have hcs : (Real.cos ((d : ℝ) * η)) ^ 2 + (Real.sin ((d : ℝ) * η)) ^ 2 = 1 := by
      have := Real.sin_sq_add_cos_sq ((d : ℝ) * η)
      linarith [this]
    have hnum : Ã * (-(Real.sin ((d : ℝ) * η)) * (d : ℝ)) +
        Bt * (Real.cos ((d : ℝ) * η) * (d : ℝ)) =
        p.derivative.eval (Real.cos η) * (-(Real.sin η)) := by
      rw [hÃdef, hBtdef]
      have hBw : (d : ℝ) * (p.derivative.eval (Real.cos η) * (-(Real.sin η)) / (d : ℝ)) =
          p.derivative.eval (Real.cos η) * (-(Real.sin η)) := by
        field_simp
      nlinarith [hcs, hBw, mul_pos hdR' (by positivity : (0 : ℝ) < 1)]
    rwa [hnum] at hval
  have hg'η : HasDerivAt g 0 η := by
    have hfun : g = fun θ => sharpBernsteinTrig p θ - q θ := funext hg
    rw [hfun]
    have h := hw'η.sub hq'η
    simpa using! h

  obtain ⟨ψ, hψc, hψs⟩ : ∃ ψ : ℝ, Real.cos ψ = Ã / R ∧ Real.sin ψ = Bt / R := by
    have hnsq : Complex.normSq (((Ã : ℝ) : ℂ) + ((Bt : ℝ) : ℂ) * Complex.I) =
        Ã ^ 2 + Bt ^ 2 := Complex.normSq_add_mul_I Ã Bt
    have hzne : (((Ã : ℝ) : ℂ) + ((Bt : ℝ) : ℂ) * Complex.I) ≠ 0 := by
      intro h0
      rw [h0, Complex.normSq_zero] at hnsq
      rw [← hR2] at hnsq
      exact hRpos.ne (by nlinarith [hnsq])
    have hnorm : ‖(((Ã : ℝ) : ℂ) + ((Bt : ℝ) : ℂ) * Complex.I)‖ = R := by
      have h1 : ‖(((Ã : ℝ) : ℂ) + ((Bt : ℝ) : ℂ) * Complex.I)‖ *
          ‖(((Ã : ℝ) : ℂ) + ((Bt : ℝ) : ℂ) * Complex.I)‖ = R * R := by
        rw [← sq, ← Complex.normSq_eq_norm_sq, hnsq, hR2]
      have h2 : 0 ≤ ‖(((Ã : ℝ) : ℂ) + ((Bt : ℝ) : ℂ) * Complex.I)‖ := norm_nonneg _
      nlinarith [h1, h2, hRpos]
    have hre : (((Ã : ℝ) : ℂ) + ((Bt : ℝ) : ℂ) * Complex.I).re = Ã := by
      simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
    have him : (((Ã : ℝ) : ℂ) + ((Bt : ℝ) : ℂ) * Complex.I).im = Bt := by
      simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
    refine ⟨Complex.arg (((Ã : ℝ) : ℂ) + ((Bt : ℝ) : ℂ) * Complex.I), ?_, ?_⟩
    · rw [Complex.cos_arg hzne, hre, hnorm]
    · rw [Complex.sin_arg, him, hnorm]

  obtain ⟨θ, hθdef⟩ : ∃ θ : ℕ → ℝ, ∀ k, θ k = ψ / (d : ℝ) + (k : ℝ) * (Real.pi / (d : ℝ)) :=
    ⟨_, fun _ => rfl⟩
  have hdθk : ∀ k : ℕ, (d : ℝ) * θ k = ψ + (k : ℝ) * Real.pi := by
    intro k
    rw [hθdef k]
    field_simp
  have hθlt : ∀ k : ℕ, θ k < θ (k + 1) := by
    intro k
    rw [hθdef k, hθdef (k + 1)]
    have hpos : 0 < Real.pi / (d : ℝ) := by positivity
    push_cast
    nlinarith [hpos]
  have hθmono : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → θ k₁ ≤ θ k₂ := by
    intro k₁ k₂ hle
    have hpos : 0 < Real.pi / (d : ℝ) := by positivity
    rw [hθdef k₁, hθdef k₂]
    have hcast : (k₁ : ℝ) ≤ (k₂ : ℝ) := by exact_mod_cast hle
    nlinarith [hpos, hcast]
  have hθ2d : θ (2 * d) = θ 0 + 2 * Real.pi := by
    rw [hθdef (2 * d), hθdef 0]
    push_cast
    field_simp
    ring

  have hqθk : ∀ k : ℕ, q (θ k) = (-1 : ℝ) ^ k * R := by
    intro k
    have hcos : Real.cos ((d : ℝ) * θ k) = (-1 : ℝ) ^ k * (Ã / R) := by
      rw [hdθk k, Real.cos_add, hψc, hψs, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi,
        mul_zero, sub_zero]
      ring
    have hsin : Real.sin ((d : ℝ) * θ k) = (-1 : ℝ) ^ k * (Bt / R) := by
      rw [hdθk k, Real.sin_add, hψc, hψs, Real.cos_nat_mul_pi, Real.sin_nat_mul_pi,
        mul_zero, add_zero]
      ring
    have hneR : R ≠ 0 := ne_of_gt hRpos
    have hsplit : Ã * ((-1 : ℝ) ^ k * (Ã / R)) + Bt * ((-1 : ℝ) ^ k * (Bt / R))
        = (-1 : ℝ) ^ k * ((Ã ^ 2 + Bt ^ 2) / R) := by
      field_simp
    rw [hq (θ k), hcos, hsin, hsplit, ← hR2]
    field_simp

  have hsign : ∀ k : ℕ, (-1 : ℝ) ^ k * g (θ k) < 0 := by
    intro k
    have hbθ := hb (θ k)
    have hs2 : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow (⟨k, by omega⟩ : Even (k + k))
    have hle : (-1 : ℝ) ^ k * sharpBernsteinTrig p (θ k) ≤ C := by
      calc (-1 : ℝ) ^ k * sharpBernsteinTrig p (θ k)
          ≤ |(-1 : ℝ) ^ k * sharpBernsteinTrig p (θ k)| := le_abs_self _
      _ = |sharpBernsteinTrig p (θ k)| := by
          rw [abs_mul, abs_neg_one_pow, one_mul]
      _ ≤ C := hbθ
    rw [hg (θ k), hqθk k, mul_sub, ← mul_assoc, hs2, one_mul]
    nlinarith [hle, hCR]

  have hivt : ∀ k : ℕ, ∃ ζ, θ k < ζ ∧ ζ < θ (k + 1) ∧ g ζ = 0 := by
    intro k
    have hs2 : (-1 : ℝ) ^ k * (-1 : ℝ) ^ k = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow (⟨k, by omega⟩ : Even (k + k))
    have e1 : (-1 : ℝ) ^ k * g (θ k) < 0 := hsign k
    have e2 : (-1 : ℝ) ^ k * g (θ (k + 1)) > 0 := by
      have e2' := hsign (k + 1)
      have hkey : ((-1 : ℝ) ^ (k + 1)) * g (θ (k + 1)) =
          -(((-1 : ℝ) ^ k) * g (θ (k + 1))) := by
        rw [pow_add, pow_one]
        ring
      rw [hkey] at e2'
      linarith
    have hprod : g (θ k) * g (θ (k + 1)) < 0 :=
      calc g (θ k) * g (θ (k + 1))
          = ((-1 : ℝ) ^ k * g (θ k)) * ((-1 : ℝ) ^ k * g (θ (k + 1))) := by
            linear_combination (-(g (θ k)) * g (θ (k + 1))) * hs2
      _ < 0 := mul_neg_of_neg_of_pos e1 e2
    exact exists_zero_of_mul_lt (hθlt k) hgc.continuousOn hprod
  choose ζ hζ using hivt

  have hX21 : (Polynomial.X ^ 2 + 1 : ℂ[X]).natDegree = 2 :=
    Polynomial.natDegree_X_pow_add_C
  have hmon : (Polynomial.X ^ 2 + 1 : ℂ[X]).Monic :=
    Polynomial.monic_X_pow_add_C (1 : ℂ) two_ne_zero
  have hsumdeg : (∑ j ∈ Finset.range (d + 1),
      Polynomial.C (((p.coeff j : ℝ) : ℂ) * ((2 : ℝ)⁻¹ ^ j : ℝ)) *
        (Polynomial.X ^ (d - j) * (Polynomial.X ^ 2 + 1) ^ j)).natDegree ≤ 2 * d := by
    refine Polynomial.natDegree_sum_le_of_forall_le (Finset.range (d + 1)) _ ?_
    intro j hj
    have hjd : j ≤ d := Finset.mem_range_succ_iff.mp hj
    have hC0 : (Polynomial.C (((p.coeff j : ℝ) : ℂ) * ((2 : ℝ)⁻¹ ^ j : ℝ))).natDegree = 0 :=
      Polynomial.natDegree_C _
    have hX2 : ((Polynomial.X ^ 2 + 1 : ℂ[X]) ^ j).natDegree = j * 2 := by
      rw [hmon.natDegree_pow, hX21]
    have hmul : (Polynomial.X ^ (d - j) * (Polynomial.X ^ 2 + 1 : ℂ[X]) ^ j).natDegree
        ≤ (d - j) + 2 * j := by
      calc (Polynomial.X ^ (d - j) * (Polynomial.X ^ 2 + 1 : ℂ[X]) ^ j).natDegree
          ≤ (Polynomial.X ^ (d - j)).natDegree + ((Polynomial.X ^ 2 + 1 : ℂ[X]) ^ j).natDegree :=
            Polynomial.natDegree_mul_le
        _ = (d - j) + j * 2 := by rw [Polynomial.natDegree_X_pow, hX2]
        _ ≤ (d - j) + 2 * j := by omega
    have hterm : (Polynomial.C (((p.coeff j : ℝ) : ℂ) * ((2 : ℝ)⁻¹ ^ j : ℝ)) *
        (Polynomial.X ^ (d - j) * (Polynomial.X ^ 2 + 1) ^ j)).natDegree ≤ 2 * d := by
      refine le_trans Polynomial.natDegree_mul_le ?_
      have h1 : (Polynomial.C (((p.coeff j : ℝ) : ℂ) * ((2 : ℝ)⁻¹ ^ j : ℝ))).natDegree +
          (Polynomial.X ^ (d - j) * (Polynomial.X ^ 2 + 1) ^ j).natDegree ≤
          0 + ((d - j) + 2 * j) := Nat.add_le_add hC0.le hmul
      omega
    exact hterm
  obtain ⟨P, hPdef, hPdeg⟩ : ∃ P : ℂ[X],
      (∀ θ : ℝ, P.eval (Complex.exp (θ * Complex.I)) =
        (Complex.exp (θ * Complex.I)) ^ d * ((p.eval (Real.cos θ) : ℝ) : ℂ)) ∧
      P.natDegree ≤ 2 * d :=
    ⟨_, fun θ => sharpBernstein_lift_poly d p hdeg θ, hsumdeg⟩
  have hQdegexp : (Polynomial.C ((((Ã : ℝ) : ℂ) - ((Bt : ℝ) : ℂ) * Complex.I) / 2) *
        Polynomial.X ^ (2 * d) +
      Polynomial.C ((((Ã : ℝ) : ℂ) + ((Bt : ℝ) : ℂ) * Complex.I) / 2)).natDegree ≤ 2 * d := by
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · calc (Polynomial.C ((((Ã : ℝ) : ℂ) - ((Bt : ℝ) : ℂ) * Complex.I) / 2) *
            Polynomial.X ^ (2 * d)).natDegree
          ≤ (Polynomial.C ((((Ã : ℝ) : ℂ) - ((Bt : ℝ) : ℂ) * Complex.I) / 2)).natDegree +
              (Polynomial.X ^ (2 * d)).natDegree := Polynomial.natDegree_mul_le
        _ = 2 * d := by rw [Polynomial.natDegree_C, zero_add, Polynomial.natDegree_X_pow]
    · rw [Polynomial.natDegree_C]
      omega
  obtain ⟨Q, hQdef, hQdeg⟩ : ∃ Q : ℂ[X],
      (∀ θ : ℝ, Q.eval (Complex.exp (θ * Complex.I)) =
        (Complex.exp (θ * Complex.I)) ^ d *
          (((Ã : ℝ) : ℂ) * ((Real.cos ((d : ℝ) * θ) : ℝ) : ℂ) +
            ((Bt : ℝ) : ℂ) * ((Real.sin ((d : ℝ) * θ) : ℝ) : ℂ))) ∧
      Q.natDegree ≤ 2 * d :=
    ⟨_, fun θ => sharpBernstein_lift_tone Ã Bt d θ, hQdegexp⟩
  obtain ⟨G, hGdef⟩ : ∃ G : ℂ[X], G = P - Q := ⟨_, rfl⟩
  have hGdeg : G.natDegree ≤ 2 * d := by
    rw [hGdef]
    exact le_trans (Polynomial.natDegree_sub_le _ _) (max_le hPdeg hQdeg)
  have hGid : ∀ θ : ℝ, G.eval (Complex.exp (θ * Complex.I)) =
      (Complex.exp (θ * Complex.I)) ^ d * ((g θ : ℝ) : ℂ) := by
    intro θ
    rw [hGdef, eval_sub, hPdef θ, hQdef θ, hg θ, hq θ]
    unfold sharpBernsteinTrig
    push_cast
    ring

  have hzne : Complex.exp (η * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hGz0 : G.eval (Complex.exp (η * Complex.I)) = 0 := by
    have h := hGid η
    rw [hgη] at h
    simpa using h
  have hcexp : HasDerivAt (fun θ : ℝ => Complex.exp (θ * Complex.I))
      (Complex.exp (η * Complex.I) * Complex.I) η := by
    simpa only [mul_assoc, one_mul, Complex.ofRealCLM_apply, Complex.ofReal_one] using
      ((Complex.ofRealCLM.hasDerivAt (x := η)).mul_const Complex.I).cexp
  have hFchain : HasDerivAt (fun θ : ℝ => G.eval (Complex.exp (θ * Complex.I)))
      (G.derivative.eval (Complex.exp (η * Complex.I)) *
        (Complex.exp (η * Complex.I) * Complex.I)) η := by
    have h := (Polynomial.hasDerivAt G (Complex.exp (η * Complex.I))).comp η hcexp
    simpa only [Function.comp_def] using h
  have hF1zero : HasDerivAt (fun θ : ℝ => G.eval (Complex.exp (θ * Complex.I))) 0 η := by
    have hB : HasDerivAt (fun θ : ℝ => ((g θ : ℝ) : ℂ)) 0 η := by
      simpa using hg'η.ofReal_comp
    have hcomb := (hcexp.pow' d).mul hB
    have hcomb' : HasDerivAt
        (fun θ : ℝ => (Complex.exp (θ * Complex.I)) ^ d * ((g θ : ℝ) : ℂ)) 0 η := by
      simpa [hgη] using! hcomb.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun _ => rfl))
    rw [funext hGid]
    exact hcomb'
  have hdeq := hFchain.unique hF1zero
  have hGz0' : G.derivative.eval (Complex.exp (η * Complex.I)) = 0 := by
    rcases mul_eq_zero.mp hdeq with h | h
    · exact h
    · exact absurd h (mul_ne_zero hzne Complex.I_ne_zero)

  have hfactor : ∃ H : ℂ[X], G =
      (Polynomial.X - Polynomial.C (Complex.exp (η * Complex.I))) ^ 2 * H := by
    have hdvd1 : (Polynomial.X - Polynomial.C (Complex.exp (η * Complex.I))) ∣
        (G - Polynomial.C (G.eval (Complex.exp (η * Complex.I)))) :=
      Polynomial.X_sub_C_dvd_sub_C_eval
    rw [hGz0, Polynomial.C_0, sub_zero] at hdvd1
    obtain ⟨G₁, hG₁⟩ := hdvd1
    have hG₁z : G₁.eval (Complex.exp (η * Complex.I)) = 0 := by
      have hderiv : G.derivative =
          (Polynomial.X - Polynomial.C (Complex.exp (η * Complex.I))).derivative * G₁ +
            (Polynomial.X - Polynomial.C (Complex.exp (η * Complex.I))) * G₁.derivative := by
        rw [hG₁]
        exact Polynomial.derivative_mul
      have h1 := congrArg (fun q : ℂ[X] => q.eval (Complex.exp (η * Complex.I))) hderiv
      simp only [eval_add, eval_mul] at h1
      rw [hGz0'] at h1
      have hdx : (Polynomial.X - Polynomial.C (Complex.exp (η * Complex.I))).derivative = 1 := by
        simp
      rw [hdx] at h1
      simp only [eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero, eval_one, one_mul] at h1
      exact h1.symm
    have hdvd2 : (Polynomial.X - Polynomial.C (Complex.exp (η * Complex.I))) ∣
        (G₁ - Polynomial.C (G₁.eval (Complex.exp (η * Complex.I)))) :=
      Polynomial.X_sub_C_dvd_sub_C_eval
    rw [hG₁z, Polynomial.C_0, sub_zero] at hdvd2
    obtain ⟨H, hH⟩ := hdvd2
    refine ⟨H, ?_⟩
    rw [hG₁, hH, ← mul_assoc, ← pow_two]

  have harc : ∀ k ∈ Finset.range (2 * d), θ 0 < ζ k ∧ ζ k < θ 0 + 2 * Real.pi := by
    intro k hk
    rw [Finset.mem_range] at hk
    obtain ⟨h1, h2', _⟩ := hζ k
    have hle1 : θ 0 ≤ θ k := hθmono 0 k (Nat.zero_le k)
    have hle2 : θ (k + 1) ≤ θ (2 * d) := hθmono (k + 1) (2 * d) (by omega)
    rw [hθ2d] at hle2
    exact ⟨lt_of_le_of_lt hle1 h1, lt_of_lt_of_le h2' hle2⟩
  have hexpinj : ∀ k₁ ∈ Finset.range (2 * d), ∀ k₂ ∈ Finset.range (2 * d),
      Complex.exp (ζ k₁ * Complex.I) = Complex.exp (ζ k₂ * Complex.I) → k₁ = k₂ := by
    intro k₁ h₁mem k₂ h₂mem heq
    rw [Finset.mem_range] at h₁mem h₂mem
    obtain ⟨ha1, ha2⟩ := harc k₁ (Finset.mem_range.mpr h₁mem)
    obtain ⟨hb1, hb2⟩ := harc k₂ (Finset.mem_range.mpr h₂mem)
    rw [Complex.exp_eq_exp_iff_exists_int] at heq
    obtain ⟨n, hn⟩ := heq
    have him := congrArg Complex.im hn
    have h2 : (ζ k₁ * Complex.I).im = ζ k₁ := by simp
    have h3 : (ζ k₂ * Complex.I + n * (2 * Real.pi * Complex.I)).im
        = ζ k₂ + (n : ℝ) * (2 * Real.pi) := by
      simp [Complex.add_im, Complex.mul_im]
    rw [h2, h3] at him
    have hpi2 : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
    have hlt : (n : ℝ) * (2 * Real.pi) < 2 * Real.pi := by linarith [him]
    have hgt : -(2 * Real.pi) < (n : ℝ) * (2 * Real.pi) := by linarith [him]
    have hnn : (n : ℝ) = 0 := by
      rcases lt_trichotomy (n : ℤ) 0 with hneg | hzero | hpos
      · exfalso
        have hc : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega)
        have hle : (n : ℝ) * (2 * Real.pi) ≤ -1 * (2 * Real.pi) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
        linarith
      · exact_mod_cast hzero
      · exfalso
        have hc : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega)
        have hge : 2 * Real.pi ≤ (n : ℝ) * (2 * Real.pi) := by
          nlinarith [hc, hpi2]
        linarith
    have hzz : ζ k₁ = ζ k₂ := by
      rw [hnn] at him
      linarith
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨_, hζa, _⟩ := hζ k₁
      obtain ⟨hζb, _, _⟩ := hζ k₂
      have hmono : θ (k₁ + 1) ≤ θ k₂ := hθmono (k₁ + 1) k₂ (by omega)
      linarith
    · obtain ⟨hζa, _, _⟩ := hζ k₁
      obtain ⟨_, hζb, _⟩ := hζ k₂
      have hmono : θ (k₂ + 1) ≤ θ k₁ := hθmono (k₂ + 1) k₁ (by omega)
      linarith
  obtain ⟨S, hS⟩ : ∃ S : Finset ℂ,
      S = (Finset.range (2 * d)).image (fun k => Complex.exp (ζ k * Complex.I)) := ⟨_, rfl⟩
  have hScard : S.card = 2 * d := by
    rw [hS, Finset.card_image_of_injOn]
    · simp
    · intro a ha b hb hab
      have ha' : a ∈ Finset.range (2 * d) := Finset.mem_coe.mp ha
      have hb' : b ∈ Finset.range (2 * d) := Finset.mem_coe.mp hb
      exact hexpinj a ha' b hb' hab
  have hGS : ∀ s ∈ S, G.eval s = 0 := by
    intro s hs
    rw [hS, Finset.mem_image] at hs
    obtain ⟨k, _, hkeq⟩ := hs
    rw [← hkeq]
    have h := hGid (ζ k)
    rw [(hζ k).2.2] at h
    simpa using h

  rcases eq_or_ne G 0 with hG0 | hG0
  · have h0 := hGid (θ 0)
    rw [hG0, Polynomial.eval_zero] at h0
    have hnz : (Complex.exp (θ 0 * Complex.I)) ^ d ≠ 0 :=
      pow_ne_zero d (Complex.exp_ne_zero _)
    have hgz : ((g (θ 0) : ℝ) : ℂ) = 0 := by
      rcases mul_eq_zero.mp h0.symm with h | h
      · exact absurd h hnz
      · exact h
    have hgθ0 : g (θ 0) = 0 := by exact_mod_cast hgz
    have hsign0 := hsign 0
    rw [pow_zero, one_mul] at hsign0
    linarith
  · obtain ⟨H, hH⟩ := hfactor
    have hHne : H ≠ 0 := by
      intro hcon
      exact hG0 (by rw [hH, hcon, mul_zero])
    have hm1 : (Polynomial.X - Polynomial.C (Complex.exp (η * Complex.I))).Monic :=
      Polynomial.monic_X_sub_C _
    have hm2 := hm1.pow 2
    have hHdeg : H.natDegree ≤ 2 * d - 2 := by
      have hlead : ((Polynomial.X - Polynomial.C (Complex.exp (η * Complex.I))) ^ 2).leadingCoeff *
          H.leadingCoeff ≠ 0 := by
        rw [hm2.leadingCoeff, one_mul]
        exact Polynomial.leadingCoeff_ne_zero.mpr hHne
      have h1 : G.natDegree =
          ((Polynomial.X - Polynomial.C (Complex.exp (η * Complex.I))) ^ 2).natDegree +
            H.natDegree := by
        rw [hH, Polynomial.natDegree_mul' hlead]
      rw [hm1.natDegree_pow, Polynomial.natDegree_X_sub_C] at h1
      omega
    obtain ⟨T, hT⟩ : ∃ T : Finset ℂ,
        T = S.filter (fun s => s ≠ Complex.exp (η * Complex.I)) := ⟨_, rfl⟩
    have hHT : ∀ t ∈ T, H.eval t = 0 := by
      intro t ht
      rw [hT, Finset.mem_filter] at ht
      obtain ⟨htS, htne⟩ := ht
      have hGt : G.eval t = 0 := hGS t htS
      rw [hH, eval_mul, eval_pow, eval_sub, eval_X, eval_C] at hGt
      rcases mul_eq_zero.mp hGt with h | h
      · exact False.elim (htne (sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h)))
      · exact h
    have hTcard : 2 * d - 1 ≤ T.card := by
      have hsub : S ⊆ insert (Complex.exp (η * Complex.I)) T := by
        intro s hs
        by_cases hsz : s = Complex.exp (η * Complex.I)
        · exact Finset.mem_insert.mpr (Or.inl hsz)
        · exact Finset.mem_insert_of_mem (by
            rw [hT]
            exact Finset.mem_filter.mpr ⟨hs, hsz⟩)
      have h1 : S.card ≤ (insert (Complex.exp (η * Complex.I)) T).card :=
        Finset.card_le_card hsub
      have h2 := Finset.card_insert_le (Complex.exp (η * Complex.I)) T
      rw [hScard] at h1
      omega
    exact hHne
      (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' H T hHT (by omega))

theorem sharpBernstein_trig_bound (d : ℕ) (p : ℝ[X]) (C : ℝ)
    (hd : 1 ≤ d) (hdeg : p.natDegree ≤ d) (hC : 0 ≤ C)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ C) (θ : ℝ) :
    |p.derivative.eval (Real.cos θ) * (-(Real.sin θ))| ≤ (d : ℝ) * C := by
  have hbtrig : ∀ θ : ℝ, |p.eval (Real.cos θ)| ≤ C :=
    fun θ => hb _ ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  apply abs_le.mpr
  constructor
  · by_contra h
    have hneg : (d : ℝ) * C <
        (-p).derivative.eval (Real.cos θ) * (-(Real.sin θ)) := by
      simp only [Polynomial.derivative_neg, Polynomial.eval_neg]
      linarith [not_le.mp h]
    exact sharpBernstein_violation d hd (-p)
      (by simpa using hdeg) hC (by simpa using hbtrig) θ hneg
  · by_contra h
    exact sharpBernstein_violation d hd p hdeg hC hbtrig θ (not_le.mp h)

theorem sharpBernstein_interior (d : ℕ) (p : ℝ[X]) (C : ℝ)
    (hd : 1 ≤ d) (hdeg : p.natDegree ≤ d) (hC : 0 ≤ C)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ C)
    (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Real.sqrt (1 - x ^ 2) * |p.derivative.eval x| ≤ (d : ℝ) * C := by
  have h := sharpBernstein_trig_bound d p C hd hdeg hC hb (Real.arccos x)
  rw [Real.cos_arccos hx.1 hx.2, abs_mul, abs_neg, Real.sin_arccos,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_comm] at h
  exact h

end Bernstein

end Qatlib.Concepts.QueryComplexity.DegreeMethod
