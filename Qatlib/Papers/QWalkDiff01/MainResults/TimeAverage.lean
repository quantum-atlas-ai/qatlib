/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic
import Qatlib.Papers.QWalkDiff01.MainResults.LimitingDistribution

/-!
# Continuous time averages of spectral probabilities

The finite spectral amplitude `spectralAmplitude` and its real probability expansion
`eigenTransitionProb` model continuous time evolution. Oscillatory cross terms vanish under time
averaging when the energies are distinct, identifying the limit with `limitingDistribution` as
used in [ChildsFarhiGutmann2002].

## Main statements

* `normSq_spectralAmplitude`: identifies the probability expansion with the squared amplitude
  norm.
* `timeAverage_limitingDistribution`: proves convergence to the spectral limiting distribution.
* `timeAverage_rightRoot_lower_bound`: combines convergence with the endpoint-overlap lower
  bound.

## References

* [Childs et al., 2002][ChildsFarhiGutmann2002]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators InnerProductSpace
open Filter Topology
open ComplexConjugate

namespace Qatlib.Papers.QWalkDiff01.MainResults

variable {ι : Type*} [Fintype ι]

/-- The finite spectral amplitude `∑ r, A r * exp(-i * E r * t)` for real coefficients and
energies. -/
def spectralAmplitude (A E : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ r, (A r : ℂ) * Complex.exp (-(((E r * t : ℝ)) : ℂ) * Complex.I)

/-- The real double-sum probability expansion with coefficients `A r * A s` and phases `cos ((E
r - E s) * t)`. -/
def eigenTransitionProb (A E : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ r, ∑ s, A r * A s * Real.cos ((E r - E s) * t)

/-- The product of one spectral phase and the conjugate of another is the exponential of their
energy difference. -/
theorem exp_mul_conj_exp (a b t : ℝ) :
    Complex.exp (-(((a * t : ℝ)) : ℂ) * Complex.I) *
        conj (Complex.exp (-(((b * t : ℝ)) : ℂ) * Complex.I)) =
      Complex.exp (((((b - a) * t : ℝ)) : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj]
  have hconj : conj (-(((b * t : ℝ)) : ℂ) * Complex.I) =
      (((b * t : ℝ)) : ℂ) * Complex.I := by
    rw [map_mul, Complex.conj_I, map_neg, Complex.conj_ofReal]
    ring
  rw [hconj, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The real part of a spectral phase times a conjugate spectral phase is the cosine of the
energy difference times time. -/
theorem exp_mul_conj_exp_re (a b t : ℝ) :
    (Complex.exp (-(((a * t : ℝ)) : ℂ) * Complex.I) *
        conj (Complex.exp (-(((b * t : ℝ)) : ℂ) * Complex.I))).re =
      Real.cos ((a - b) * t) := by
  rw [exp_mul_conj_exp]
  have harg : ((b - a) * t : ℝ) = -((a - b) * t) := by ring
  rw [harg, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- The squared norm of `spectralAmplitude` equals `eigenTransitionProb`. -/
theorem normSq_spectralAmplitude (A E : ι → ℝ) (t : ℝ) :
    ‖spectralAmplitude A E t‖ ^ 2 = eigenTransitionProb A E t := by
  have hre : (spectralAmplitude A E t * conj (spectralAmplitude A E t)).re =
      ‖spectralAmplitude A E t‖ ^ 2 := by
    rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [← hre]
  unfold spectralAmplitude eigenTransitionProb
  rw [map_sum, Finset.sum_mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [map_mul, Complex.conj_ofReal]
  rw [show (A r : ℂ) * Complex.exp (-(((E r * t : ℝ)) : ℂ) * Complex.I) *
      ((A s : ℂ) * conj (Complex.exp (-(((E s * t : ℝ)) : ℂ) * Complex.I))) =
      ((A r * A s : ℝ) : ℂ) *
        (Complex.exp (-(((E r * t : ℝ)) : ℂ) * Complex.I) *
          conj (Complex.exp (-(((E s * t : ℝ)) : ℂ) * Complex.I))) by
    push_cast
    ring]
  rw [Complex.re_ofReal_mul, exp_mul_conj_exp_re]

/-- For nonzero frequency `ω`, the integral of `cos (ω * t)` from zero to `T` is `sin (ω * T) /
ω`. -/
theorem intervalIntegral_cos_mul (ω T : ℝ) (hω : ω ≠ 0) :
    ∫ t in (0 : ℝ)..T, Real.cos (ω * t) = Real.sin (ω * T) / ω := by
  rw [intervalIntegral.integral_comp_mul_left (f := Real.cos) (a := 0) (b := T) (c := ω) hω,
    integral_cos]
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- The time average of `cos (ω * t)` tends to one for zero frequency and zero otherwise. -/
theorem tendsto_avg_cos (ω : ℝ) :
    Tendsto (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T, Real.cos (ω * t)) atTop
      (𝓝 (if ω = 0 then 1 else 0)) := by
  by_cases hω : ω = 0
  · subst hω
    rw [if_pos rfl]
    have heq : (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T, Real.cos ((0 : ℝ) * t))
        =ᶠ[atTop] fun _ => (1 : ℝ) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      simp only [zero_mul, Real.cos_zero]
      rw [intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul, mul_one]
      field_simp
    exact tendsto_const_nhds.congr' heq.symm
  · rw [if_neg hω]
    have heq : (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T, Real.cos (ω * t))
        =ᶠ[atTop] fun T : ℝ => (Real.sin (ω * T) / ω) * (1 / T) := by
      filter_upwards with T
      rw [intervalIntegral_cos_mul ω T hω]
      ring
    rw [tendsto_congr' heq]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbound : ∀ T : ℝ,
        ‖Real.sin (ω * T) / ω * (1 / T)‖ ≤ (1 / |ω|) * ‖(T : ℝ)⁻¹‖ := by
      intro T
      have hωpos : 0 < |ω| := abs_pos.mpr hω
      have h1 : |Real.sin (ω * T)| ≤ 1 := Real.abs_sin_le_one _
      rw [norm_mul, norm_div, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        show (1 : ℝ) / T = (T : ℝ)⁻¹ from one_div T, abs_inv]
      have h2 : |Real.sin (ω * T)| / |ω| ≤ 1 / |ω| := by
        rw [div_le_div_iff_of_pos_right hωpos]
        exact h1
      calc |Real.sin (ω * T)| / |ω| * |T|⁻¹ ≤ (1 / |ω|) * |T|⁻¹ := by
            exact mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = (1 / |ω|) * ‖(T : ℝ)⁻¹‖ := by rw [Real.norm_eq_abs, abs_inv]
    refine squeeze_zero (fun T => norm_nonneg _) hbound ?_
    have hinv : Tendsto (fun T : ℝ => ‖(T : ℝ)⁻¹‖) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero (𝕜 := ℝ)).norm
    simpa using (tendsto_const_nhds (x := (1 : ℝ) / |ω|)).mul hinv

/-- With pairwise distinct energies, the time average of the spectral transition probability
tends to the sum of squared coefficients. -/
theorem tendsto_timeAverage_eigenTransitionProb (A E : ι → ℝ)
    (hE : ∀ r s : ι, E r = E s → r = s) :
    Tendsto (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T, eigenTransitionProb A E t) atTop
      (𝓝 (∑ r, A r ^ 2)) := by
  have heq : ∀ T : ℝ, (1 / T) * ∫ t in (0 : ℝ)..T, eigenTransitionProb A E t =
      ∑ r, ∑ s, A r * A s *
        ((1 / T) * ∫ t in (0 : ℝ)..T, Real.cos ((E r - E s) * t)) := by
    intro T
    unfold eigenTransitionProb
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro r _
      rw [intervalIntegral.integral_finsetSum]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro s _
        rw [intervalIntegral.integral_const_mul]
        ring
      · intro s _
        exact (by fun_prop : Continuous fun t : ℝ =>
          A r * A s * Real.cos ((E r - E s) * t)).intervalIntegrable _ _
    · intro r _
      exact (by fun_prop : Continuous fun t : ℝ =>
        ∑ s, A r * A s * Real.cos ((E r - E s) * t)).intervalIntegrable _ _
  rw [tendsto_congr' (Eventually.of_forall heq)]
  have hterm : ∀ r s : ι, Tendsto
      (fun T : ℝ => A r * A s *
        ((1 / T) * ∫ t in (0 : ℝ)..T, Real.cos ((E r - E s) * t)))
      atTop (𝓝 (A r * A s * (if E r - E s = 0 then 1 else 0))) := by
    intro r s
    exact tendsto_const_nhds.mul (tendsto_avg_cos (E r - E s))
  have hsum : Tendsto
      (fun T : ℝ => ∑ r, ∑ s, A r * A s *
        ((1 / T) * ∫ t in (0 : ℝ)..T, Real.cos ((E r - E s) * t)))
      atTop (𝓝 (∑ r, ∑ s, A r * A s * (if E r - E s = 0 then 1 else 0))) := by
    refine tendsto_finsetSum _ ?_
    intro r _
    refine tendsto_finsetSum _ ?_
    intro s _
    exact hterm r s
  have hval : (∑ r, ∑ s, A r * A s * (if E r - E s = 0 then 1 else 0)) =
      ∑ r, A r ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro r _
    rw [Finset.sum_eq_single r]
    · simp
      ring
    · intro s _ hsr
      have hne : E r - E s ≠ 0 := by
        intro h
        have hEq : E r = E s := by linarith
        exact hsr (hE r s hEq).symm
      simp [hne]
    · intro hr
      exact absurd (Finset.mem_univ r) hr
  rw [hval] at hsum
  exact hsum

/-- For pairwise distinct energies, the time-averaged transition probability between `a` and `c`
converges to their spectral limiting distribution, as in [ChildsFarhiGutmann2002]. -/
theorem timeAverage_limitingDistribution (n : ℕ) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (basis : OrthonormalBasis (Fin (2 * n + 1)) ℝ E) (a c : E)
    (energies : Fin (2 * n + 1) → ℝ)
    (henergy : ∀ r s : Fin (2 * n + 1), energies r = energies s → r = s) :
    Tendsto (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T,
        eigenTransitionProb (fun r => ⟪basis r, a⟫_ℝ * ⟪basis r, c⟫_ℝ) energies t)
      atTop (𝓝 (limitingDistribution basis a c)) := by
  have hmain := tendsto_timeAverage_eigenTransitionProb
    (A := fun r => ⟪basis r, a⟫_ℝ * ⟪basis r, c⟫_ℝ) (E := energies) henergy
  have hsum : (∑ r, (⟪basis r, a⟫_ℝ * ⟪basis r, c⟫_ℝ) ^ 2) =
      limitingDistribution basis a c := by
    unfold limitingDistribution
    exact Finset.sum_congr rfl (fun r _ => by ring)
  rw [hsum] at hmain
  exact hmain

/-- For distinct energies and a unit source with equal-magnitude endpoint overlaps, the time
average converges to `limitingDistribution`, which is at least `1 / (2 * n + 1)`. -/
theorem timeAverage_rightRoot_lower_bound (n : ℕ) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (basis : OrthonormalBasis (Fin (2 * n + 1)) ℝ E) (a c : E) (ha : ‖a‖ = 1)
    (hparity : ∀ r : Fin (2 * n + 1), |⟪basis r, a⟫_ℝ| = |⟪basis r, c⟫_ℝ|)
    (energies : Fin (2 * n + 1) → ℝ)
    (henergy : ∀ r s : Fin (2 * n + 1), energies r = energies s → r = s) :
    Tendsto (fun T : ℝ => (1 / T) * ∫ t in (0 : ℝ)..T,
        eigenTransitionProb (fun r => ⟪basis r, a⟫_ℝ * ⟪basis r, c⟫_ℝ) energies t)
      atTop (𝓝 (limitingDistribution basis a c)) ∧
      1 / ((2 * n + 1 : ℕ) : ℝ) ≤ limitingDistribution basis a c :=
  ⟨timeAverage_limitingDistribution n basis a c energies henergy,
    limitingDistribution_rightRoot_lower_bound n basis a c ha hparity⟩

end Qatlib.Papers.QWalkDiff01.MainResults
