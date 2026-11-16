/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Qatlib.Papers.AdiabGaps09.MainResults.GaussianBound

@[expose] public section



set_option backward.isDefEq.respectTransparency false

/-!
# Finite cube moments and a conditional Gaussian tail bound

The moment identities are exact, including the empty cube. The tail statement
assumes a nondegenerate shifted Gaussian limit for the gap divided by a positive
scale. This makes explicit the Gaussian approximation used in Section III of
arXiv:0909.4766v2; the approximation itself is not proved here.
-/

set_option autoImplicit false
noncomputable section

open Finset Filter
open scoped BigOperators

open Qatlib.Papers.AdiabGaps09.MainResults.GaussianBound
open Qatlib.Papers.AdiabGaps09.MainResults.GaussianBound.ThetaAtTop

namespace Qatlib.Papers.AdiabGaps09.MainResults.GaussianBound

/-- The squared random coefficient `c_i^2` (`1/4` or `9/4` with probability
`1/2`). -/
def cSq (b : Bool) : ℝ := if b then (9 / 4 : ℝ) else (1 / 4 : ℝ)

/-- The equally weighted squared coefficient has mean five quarters. `E[c_i^2] = 5/4`. -/
theorem cSq_mean : (1 / 2 : ℝ) * cSq false + (1 / 2 : ℝ) * cSq true = 5 / 4 := by
  norm_num [cSq]

/-- The second moment of the squared coefficient is forty-one sixteenths. `E[(c_i^2)^2] = 41/16`. -/
theorem cSq_second :
    (1 / 2 : ℝ) * (cSq false) ^ 2 + (1 / 2 : ℝ) * (cSq true) ^ 2 = 41 / 16 := by
  norm_num [cSq]

/-- `Var(c_i^2) = 1`. -/
theorem cSq_variance :
    (1 / 2 : ℝ) * (cSq false) ^ 2 + (1 / 2 : ℝ) * (cSq true) ^ 2
      - ((1 / 2 : ℝ) * cSq false + (1 / 2 : ℝ) * cSq true) ^ 2 = 1 := by
  norm_num [cSq]

/-- The randomized second-order difference `Σ_i c_i^2 d_i`. -/
def secondOrderGap {n : ℕ} (d : Fin n → ℝ) (z : Fin n → Bool) : ℝ :=
  ∑ i, cSq (z i) * d i

/-- Uniform expectation over the cube `Fin n → Bool` (the `2^n` coefficient draws
`c_i ∈ {1/2,3/2}` are equiprobable). -/
def cubeMean {n : ℕ} (f : (Fin n → Bool) → ℝ) : ℝ :=
  (∑ z, f z) / (2 : ℝ) ^ n

/-- Uniform variance over the cube. -/
def cubeVar {n : ℕ} (f : (Fin n → Bool) → ℝ) : ℝ :=
  cubeMean (fun z => (f z) ^ 2) - (cubeMean f) ^ 2

/-- **mean.**  `E[Σ_i c_i^2 d_i] = (5/4) Σ_i d_i` (paper p. 11).  Linearity
of the finite sum plus the single-site mean `cSq_mean`. -/
theorem cubeMean_second_order {n : ℕ} (d : Fin n → ℝ) :
    cubeMean (fun z => secondOrderGap d z) = (5 / 4) * ∑ i, d i := by
  exact Qatlib.Papers.AdiabGaps09.MainResults.cubeMean_second_order d

/-- **variance.**  `Var(Σ_i c_i^2 d_i) = Σ_i d_i^2` (paper p. 11), because
the `c_i` are independent and `Var(c_i^2) = 1`.  Needs the factorisation
`E[c_i^2 c_j^2] = E[c_i^2] E[c_j^2]` for `i ≠ j`. -/
theorem cubeVar_second_order {n : ℕ} (d : Fin n → ℝ) :
    cubeVar (fun z => secondOrderGap d z) = ∑ i, (d i) ^ 2 := by
  exact Qatlib.Papers.AdiabGaps09.MainResults.cubeVar_second_order d

open MeasureTheory Set

/-- The unnormalized Gaussian upper tail used to state the limiting law. -/
def gaussianTail (a : ℝ) : ℝ := ∫ x in Ioi a, Real.exp (-(x ^ 2))

/-- Every finite threshold has strictly positive Gaussian upper tail. -/
private theorem gaussianTail_pos (a : ℝ) : 0 < gaussianTail a := by
  have hi : Integrable (fun x : ℝ => Real.exp (-(x ^ 2))) := by
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) zero_lt_one
      (s := 0) (by norm_num)
    simpa using h
  unfold gaussianTail
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have hs : Function.support (fun x : ℝ => Real.exp (-(x ^ 2))) = univ := by
      ext x
      simp [Function.mem_support, Real.exp_ne_zero]
    rw [hs, univ_inter, Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  · exact Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)
  · exact hi.integrableOn

/-- Under a shifted Gaussian limit and an eventually positive scale, every fixed
real scaled threshold has an eventually positive fraction of cube draws.
The limit hypothesis is the explicit distributional premise from Section III. -/
theorem probability_exceeds_scale (d : (n : ℕ) → Fin n → ℝ) (sc : ℕ → ℝ) (a : ℝ)
    (hsc : ∀ᶠ n in Filter.atTop, 0 < sc n)
    (hgauss : ∃ (μ : ℝ) (σ : {s : ℝ // 0 < s}), ∀ x : ℝ,
      Tendsto (fun n =>
        ((Finset.univ.filter (fun z : Fin n → Bool =>
          x < secondOrderGap (d n) z / sc n)).card : ℝ) / (2 : ℝ) ^ n)
        Filter.atTop (nhds
          (gaussianTail ((x - μ) / σ.val)
            / Real.sqrt Real.pi))) :
    ∃ p : ℝ, 0 < p ∧ ∀ᶠ n in Filter.atTop,
      p * (2 : ℝ) ^ n
        ≤ ((Finset.univ.filter
              (fun z : Fin n → Bool => a * sc n < secondOrderGap (d n) z)).card : ℝ) := by
  classical
  obtain ⟨μ, σ, hμ⟩ := hgauss
  let q := gaussianTail ((a - μ) / σ.val)
    / Real.sqrt Real.pi
  have hq : 0 < q := div_pos
    (gaussianTail_pos ((a - μ) / σ.val))
    (Real.sqrt_pos.2 Real.pi_pos)
  refine ⟨q / 2, by positivity, ?_⟩
  have hev := (hμ a).eventually (eventually_gt_nhds (show q / 2 < q by linarith))
  filter_upwards [hsc, hev] with n hn htail
  have hfilter : (Finset.univ.filter (fun z : Fin n → Bool =>
      a < secondOrderGap (d n) z / sc n)) =
      Finset.univ.filter (fun z : Fin n → Bool =>
        a * sc n < secondOrderGap (d n) z) := by
    apply Finset.filter_congr
    intro z _
    exact lt_div_iff₀ hn
  rw [hfilter] at htail
  exact ((lt_div_iff₀ (show (0 : ℝ) < 2 ^ n by positivity)).mp htail).le

end Qatlib.Papers.AdiabGaps09.MainResults.GaussianBound
