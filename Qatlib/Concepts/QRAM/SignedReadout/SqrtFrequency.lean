/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QRAM.SignedReadout.Sampling

@[expose] public section

/-!
# Concentration of an estimated amplitude magnitude

[KerenidisLandmanPrakash2020], Appendix G, estimates coordinate magnitudes
by taking square roots of observed frequencies. An optimized exponential
moment bound controls the resulting error on the amplitude scale. The
lower endpoint at zero is treated with a finite Chernoff parameter and
costs a factor of two in the uniform exponent.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.QRAM.SignedReadout

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.ProbabilityCore.Concentration (eventMass)
open Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
open scoped Classical

/-- The Poisson Chernoff rate dominates the square of the square-root difference. -/
private theorem sqrt_sub_sq_le_poisson_rate (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (Real.sqrt x - Real.sqrt y) ^ 2 ≤ x * Real.log (x / y) - x + y := by
  let a := Real.sqrt x
  let b := Real.sqrt y
  have ha : 0 < a := Real.sqrt_pos.mpr hx
  have hb : 0 < b := Real.sqrt_pos.mpr hy
  have haSq : a ^ 2 = x := Real.sq_sqrt hx.le
  have hbSq : b ^ 2 = y := Real.sq_sqrt hy.le
  change (a - b) ^ 2 ≤ _
  rw [← haSq, ← hbSq]
  have hLog : Real.log (a ^ 2 / b ^ 2) = -2 * Real.log (b / a) := by
    rw [← div_pow, Real.log_pow, Real.log_div ha.ne' hb.ne', Real.log_div hb.ne' ha.ne']
    push_cast
    ring
  rw [hLog]
  have hBound := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hb ha))
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg a))
  calc
    _ = -(2 * a ^ 2 * (b / a - 1)) - a ^ 2 + b ^ 2 := by
      field_simp [ha.ne']
      ring
    _ ≤ _ := by nlinarith only [hBound]

/-- Upper frequency tails decay exponentially in squared amplitude distance, including when
the true probability is zero. -/
theorem count_upper_sqrt_exp {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X)
    (a : X) (n : ℕ) (q : ℝ) (hAbove : p.prob a ≤ q) :
    eventMass (independentSampleLaw fun _ : Fin n => p)
      (fun shots => n * q ≤ ((List.ofFn shots).count a : ℝ)) ≤
        Real.exp (-(n : ℝ) * (Real.sqrt q - Real.sqrt (p.prob a)) ^ 2) := by
  by_cases hp : 0 < p.prob a
  · have hq := hp.trans_le hAbove
    have hParam : 0 ≤ Real.log (q / p.prob a) :=
      Real.log_nonneg ((le_div_iff₀ hp).mpr (by simpa only [one_mul] using hAbove))
    refine (count_upper_exp p a n _ _ hParam).trans (Real.exp_le_exp.mpr ?_)
    rw [Real.exp_log (div_pos hq hp)]
    have hRate : p.prob a * (q / p.prob a - 1) = q - p.prob a := by
      rw [mul_sub, mul_one, mul_comm (p.prob a) (q / p.prob a), div_mul_cancel₀ _ hp.ne']
    rw [hRate]
    calc
      _ = -(n : ℝ) * (q * Real.log (q / p.prob a) - q + p.prob a) := by ring
      _ ≤ _ := mul_le_mul_of_nonpos_left (sqrt_sub_sq_le_poisson_rate q (p.prob a) hq hp)
        (neg_nonpos.mpr (Nat.cast_nonneg n))
  · have hp0 := le_antisymm (le_of_not_gt hp) (p.nonneg a)
    refine (count_upper_exp p a n _ 1 zero_le_one).trans (Real.exp_le_exp.mpr ?_)
    rw [hp0, Real.sqrt_zero, sub_zero, Real.sq_sqrt ((p.nonneg a).trans hAbove)]
    simp [neg_mul]

/-- Lower frequency tails decay exponentially in squared amplitude distance. The factor
one half allows the same bound when the threshold is zero. -/
theorem count_lower_sqrt_exp {X : Type} [Fintype X] [DecidableEq X] (p : FinDist X)
    (a : X) (n : ℕ) (q : ℝ) (hq : 0 ≤ q) (hBelow : q ≤ p.prob a) :
    eventMass (independentSampleLaw fun _ : Fin n => p)
      (fun shots => ((List.ofFn shots).count a : ℝ) ≤ n * q) ≤
        Real.exp (-(n : ℝ) * (Real.sqrt q - Real.sqrt (p.prob a)) ^ 2 / 2) := by
  rcases hq.eq_or_lt with hZero | hqPos
  · subst q
    refine (count_lower_exp p a n _ (Real.log 2) (Real.log_nonneg (by norm_num))).trans
      (Real.exp_le_exp.mpr ?_)
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2),
      Real.sqrt_zero, zero_sub, neg_sq, Real.sq_sqrt (p.nonneg a)]
    ring_nf
    exact le_rfl
  · have hp := hqPos.trans_le hBelow
    have hParam : 0 ≤ Real.log (p.prob a / q) :=
      Real.log_nonneg ((le_div_iff₀ hqPos).mpr (by simpa only [one_mul] using hBelow))
    refine (count_lower_exp p a n _ _ hParam).trans (Real.exp_le_exp.mpr ?_)
    rw [Real.exp_neg, Real.exp_log (div_pos hp hqPos), inv_div]
    have hRate : p.prob a * (q / p.prob a - 1) = q - p.prob a := by
      rw [mul_sub, mul_one, mul_comm (p.prob a) (q / p.prob a), div_mul_cancel₀ _ hp.ne']
    have hLog : Real.log (p.prob a / q) = -Real.log (q / p.prob a) := by
      rw [Real.log_div hp.ne' hqPos.ne', Real.log_div hqPos.ne' hp.ne', neg_sub]
    rw [hRate, hLog]
    have hNonneg : 0 ≤ (n : ℝ) * (Real.sqrt q - Real.sqrt (p.prob a)) ^ 2 :=
      mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    calc
      _ = -(n : ℝ) * (q * Real.log (q / p.prob a) - q + p.prob a) := by ring
      _ ≤ -(n : ℝ) * (Real.sqrt q - Real.sqrt (p.prob a)) ^ 2 :=
        mul_le_mul_of_nonpos_left (sqrt_sub_sq_le_poisson_rate q (p.prob a) hqPos hp)
          (neg_nonpos.mpr (Nat.cast_nonneg n))
      _ ≤ _ := by nlinarith

/-- For a positive shot count, the observed square-root frequency has an error tail
of at most `2 * exp (-n * tolerance^2 / 2)`. This is the magnitude estimate used by
the signed QRAM readout. -/
theorem sqrt_frequency_error_probability {X : Type} [Fintype X] [DecidableEq X]
    (p : FinDist X) (a : X) (n : ℕ) (hn : 0 < n)
    (tolerance : ℝ) (hTolerance : 0 < tolerance) :
    eventMass (independentSampleLaw fun _ : Fin n => p)
      (fun shots => tolerance ≤
        |Real.sqrt (((List.ofFn shots).count a : ℝ) / n) - Real.sqrt (p.prob a)|) ≤
      2 * Real.exp (-(n : ℝ) * tolerance ^ 2 / 2) := by
  let law := independentSampleLaw (fun _ : Fin n => p)
  let root := Real.sqrt (p.prob a)
  let empirical := fun shots : Fin n → X => Real.sqrt (((List.ofFn shots).count a : ℝ) / n)
  let upper := fun shots => root + tolerance ≤ empirical shots
  let lower := fun shots => empirical shots ≤ root - tolerance
  let errorBound := Real.exp (-(n : ℝ) * tolerance ^ 2 / 2)
  have hRoot : 0 ≤ root := Real.sqrt_nonneg _
  have hRootSq : root ^ 2 = p.prob a := Real.sq_sqrt (p.nonneg a)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hEmpirical (shots : Fin n → X) : 0 ≤ empirical shots := Real.sqrt_nonneg _
  have hEmpiricalSq (shots : Fin n → X) :
      empirical shots ^ 2 = ((List.ofFn shots).count a : ℝ) / n :=
    Real.sq_sqrt (div_nonneg (Nat.cast_nonneg _) hn'.le)
  have hUpper : eventMass law upper ≤ errorBound := by
    let q := (root + tolerance) ^ 2
    have hAdd : 0 ≤ root + tolerance := add_nonneg hRoot hTolerance.le
    have hAbove : p.prob a ≤ q := by
      rw [← hRootSq]
      exact (sq_le_sq₀ hRoot hAdd).2 (le_add_of_nonneg_right hTolerance.le)
    have hCount := count_upper_sqrt_exp p a n q hAbove
    have hEq : Real.sqrt q - root = tolerance := by
      rw [show q = (root + tolerance) ^ 2 from rfl, Real.sqrt_sq hAdd]
      ring
    change _ ≤ Real.exp (-(n : ℝ) * (Real.sqrt q - root) ^ 2) at hCount
    rw [hEq] at hCount
    refine (eventMass_mono law upper (fun shots => n * q ≤ ((List.ofFn shots).count a : ℝ))
      ?_).trans (hCount.trans (Real.exp_le_exp.mpr ?_))
    · intro shots h
      have hs := (sq_le_sq₀ hAdd (hEmpirical shots)).2 h
      rw [hEmpiricalSq] at hs
      simpa only [mul_comm] using (le_div_iff₀ hn').mp hs
    · have hNonneg := mul_nonneg hn'.le (sq_nonneg tolerance)
      change -(n : ℝ) * tolerance ^ 2 ≤ -(n : ℝ) * tolerance ^ 2 / 2
      nlinarith
  have hLower : eventMass law lower ≤ errorBound := by
    by_cases hSub : 0 ≤ root - tolerance
    · let q := (root - tolerance) ^ 2
      have hBelow : q ≤ p.prob a := by
        rw [← hRootSq]
        exact (sq_le_sq₀ hSub hRoot).2 (sub_le_self _ hTolerance.le)
      have hCount := count_lower_sqrt_exp p a n q (sq_nonneg _) hBelow
      have hEq : Real.sqrt q - root = -tolerance := by
        rw [show q = (root - tolerance) ^ 2 from rfl, Real.sqrt_sq hSub]
        ring
      change _ ≤ Real.exp (-(n : ℝ) * (Real.sqrt q - root) ^ 2 / 2) at hCount
      rw [hEq, neg_sq] at hCount
      refine (eventMass_mono law lower (fun shots => ((List.ofFn shots).count a : ℝ) ≤ n * q)
        ?_).trans hCount
      intro shots h
      have hs := (sq_le_sq₀ (hEmpirical shots) hSub).2 h
      rw [hEmpiricalSq] at hs
      exact ((div_le_iff₀ hn').mp hs).trans_eq (mul_comm _ _)
    · have hEmpty (shots : Fin n → X) : ¬ lower shots :=
        fun h => hSub ((hEmpirical shots).trans h)
      simp [eventMass, hEmpty, errorBound, Real.exp_nonneg]
  change eventMass law (fun shots => tolerance ≤ |empirical shots - root|) ≤ 2 * errorBound
  have hSubset (shots : Fin n → X) (h : tolerance ≤ |empirical shots - root|) :
      upper shots ∨ lower shots := by
    by_cases hSign : 0 ≤ empirical shots - root
    · rw [abs_of_nonneg hSign] at h
      left
      change root + tolerance ≤ empirical shots
      linarith
    · rw [abs_of_nonpos (le_of_not_ge hSign)] at h
      right
      change empirical shots ≤ root - tolerance
      linarith
  calc
    _ ≤ eventMass law (fun shots => upper shots ∨ lower shots) := eventMass_mono law _ _ hSubset
    _ ≤ eventMass law upper + eventMass law lower := eventMass_or_le law upper lower
    _ ≤ errorBound + errorBound := add_le_add hUpper hLower
    _ = _ := by ring

end Qatlib.Concepts.QRAM.SignedReadout
