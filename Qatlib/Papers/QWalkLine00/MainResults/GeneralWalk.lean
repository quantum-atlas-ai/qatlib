/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkLine00.MainResults.WalkModel.FamilyDerivatives
import Qatlib.Papers.QWalkLine00.MainResults.LinearMixing.MixingCore

/-!
# Density expressions and conditional mixing for a walk family

The parameterized stationary curvature defines `familyDensity` and the integral expression
`familyIntervalTV`. Positivity is established inside the interval determined by the coin angle,
and `general_walk_linear_mixing_of_good_sites` supplies a finite-set mixing bound under explicit
mass and cardinality hypotheses, in the setting of [NayakVishwanath2000].

## Main statements

* `familyDensity_pos`: proves positivity inside the parameterized interior regime.
* `general_walk_linear_mixing_of_good_sites`: bounds total variation from uniform using a set of
  sites with a mass lower bound.

## References

* [Nayak and Vishwanath, 2000][NayakVishwanath2000]
-/

set_option warningAsError false

namespace Qatlib.Papers.QWalkLine00.MainResults

set_option autoImplicit false

noncomputable section

open scoped Interval BigOperators

/-- For `0 < θ < π` and `α² < cos² (θ / 2)`, the parameterized stationary curvature factor is
positive. -/
theorem omegaSecondAtStationaryTheta_pos {θ α : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi)
    (hα : α ^ 2 < Real.cos (θ / 2) ^ 2) :
    0 < omegaSecondAtStationaryTheta θ α := by
  unfold omegaSecondAtStationaryTheta
  have h1α : 0 < 1 - α ^ 2 := by
    have hc_le : Real.cos (θ / 2) ^ 2 ≤ 1 := by
      have h := Real.abs_cos_le_one (θ / 2)
      have h2 := sq_abs (Real.cos (θ / 2))
      have h3 := abs_nonneg (Real.cos (θ / 2))
      nlinarith [h, h2, h3]
    nlinarith
  have hdiff : 0 < Real.cos (θ / 2) ^ 2 - α ^ 2 := by linarith
  have hsin : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  exact div_pos (mul_pos h1α (Real.sqrt_pos.2 hdiff)) hsin

/-- The reciprocal curvature expression `1 / (π * omegaSecondAtStationaryTheta θ α)`. -/
def familyDensity (θ α : ℝ) : ℝ := 1 / (Real.pi * omegaSecondAtStationaryTheta θ α)

/-- The family density expression is positive for `0 < θ < π` and `α² < cos² (θ / 2)`. -/
theorem familyDensity_pos {θ α : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi)
    (hα : α ^ 2 < Real.cos (θ / 2) ^ 2) :
    0 < familyDensity θ α := by
  unfold familyDensity
  exact div_pos one_pos (mul_pos Real.pi_pos (omegaSecondAtStationaryTheta_pos h0 hπ hα))

/-- Half the integral over `[-cos (θ / 2), cos (θ / 2)]` of the absolute difference between
`familyDensity` and the uniform density on that interval. -/
def familyIntervalTV (θ : ℝ) : ℝ :=
  (1 / 2) * ∫ α in (-(Real.cos (θ / 2)))..(Real.cos (θ / 2)),
    |familyDensity θ α - 1 / (2 * Real.cos (θ / 2))|

/-- For a probability function on a nonempty finite site set, a subset occupying at least a
fraction `β` with masses at least `c / card s` gives total variation error at most `1 - β *
c`, under the stated parameter and window hypotheses. See [NayakVishwanath2000]. -/
theorem general_walk_linear_mixing_of_good_sites
    (θ : ℝ) (_h0 : 0 < θ) (_hπ : θ < Real.pi)
    (s : Finset ℤ) (p : ℤ → ℝ) (hcard : 0 < s.card)
    (hp_nonneg : ∀ i ∈ s, 0 ≤ p i) (hp_sum : ∑ i ∈ s, p i = 1)
    {β c : ℝ} (hβ : 0 ≤ β) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (G : Finset ℤ) (hGsub : ∀ i ∈ G, i ∈ s)
    (hGcard : β * (s.card : ℝ) ≤ (G.card : ℝ))
    (hmass : ∀ i ∈ G, c / (s.card : ℝ) ≤ p i)
    (_hwidth : ∀ i ∈ s, |(i : ℝ)| ≤ (s.card : ℝ) * Real.cos (θ / 2)) :
    (1 / 2) * ∑ i ∈ s, |p i - 1 / (s.card : ℝ)| ≤ 1 - β * c :=
  mixing_core s p hcard hp_nonneg hp_sum hβ hc hc1 G hGsub hGcard hmass

end

end Qatlib.Papers.QWalkLine00.MainResults
