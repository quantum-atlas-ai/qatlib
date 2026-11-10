/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QWalkLine00.MainResults.WalkModel.FamilyDerivatives
import Qatlib.Papers.QWalkLine00.MainResults.LinearMixing.MixingCore
set_option warningAsError false

namespace Qatlib.Papers.QWalkLine00.MainResults

set_option autoImplicit false

noncomputable section

open scoped Interval BigOperators

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

def familyDensity (θ α : ℝ) : ℝ := 1 / (Real.pi * omegaSecondAtStationaryTheta θ α)

theorem familyDensity_pos {θ α : ℝ} (h0 : 0 < θ) (hπ : θ < Real.pi)
    (hα : α ^ 2 < Real.cos (θ / 2) ^ 2) :
    0 < familyDensity θ α := by
  unfold familyDensity
  exact div_pos one_pos (mul_pos Real.pi_pos (omegaSecondAtStationaryTheta_pos h0 hπ hα))

def familyIntervalTV (θ : ℝ) : ℝ :=
  (1 / 2) * ∫ α in (-(Real.cos (θ / 2)))..(Real.cos (θ / 2)),
    |familyDensity θ α - 1 / (2 * Real.cos (θ / 2))|

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
