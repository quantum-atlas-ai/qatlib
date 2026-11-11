/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Conditional per-edge approximation ratios

`Fhat` is the odd hypergeometric factor in the rank-three rounding kernel. `perEdgeRatio`
combines the secondary-state and rounded-product bounds, and `conditionalRatio` takes the
supremum of uniform lower bounds obtainable by choosing a mixture weight in [0, 1]; the transfer
lemmas derive the 0.651 and 0.614 bounds from explicit numerator inequalities.

These results support the development of [CrostaSaubanereHuber2026].

## Main statements

* `conditionalRatio_bddAbove`: proves boundedness for positive resource quality.
* `ratio_651_of_bound` and `ratio_614_of_bound`: transfer scalar numerator certificates.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option autoImplicit false
noncomputable section

open Set

namespace Qatlib.Papers.RydbergMaxCut26.RatioBounds.Core

/-- The function `t * ₂F₁(1/2, 1/2; 5/2; t^2)` appearing in the rank-three rounding kernel. -/
def Fhat (t : ℝ) : ℝ := t * (₂F₁ (1 / 2 : ℝ) (1 / 2 : ℝ) (5 / 2 : ℝ) (t ^ 2))

/-- The mixture numerator `p*(-4*t) + (1-p)*(1-(8/(3*π))*Fhat t)` divided by `1-(3/η)*t`. -/
def perEdgeRatio (η p t : ℝ) : ℝ :=
  (p * (-4 * t) + (1 - p) * (1 - (8 / (3 * Real.pi)) * Fhat t)) / (1 - (3 / η) * t)

/-- The supremum of uniform lower bounds on `perEdgeRatio η p t` over `-1 ≤ t < η/3`, allowing a
mixture weight `p ∈ [0, 1]`. -/
def conditionalRatio (η : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ p : ℝ, p ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ t : ℝ, t ∈ Set.Ico (-1 : ℝ) (η / 3) → v ≤ perEdgeRatio η p t}

/-- The odd hypergeometric factor `Fhat` vanishes at zero. -/
lemma Fhat_zero : Fhat 0 = 0 := by
  simp [Fhat]

/-- The per-edge ratio at `t = 0` is `1 - p` for every resource parameter `η`. -/
lemma perEdgeRatio_at_zero (η p : ℝ) : perEdgeRatio η p 0 = 1 - p := by
  simp [perEdgeRatio, Fhat_zero]

/-- When the ratio denominator is positive, a lower bound on `perEdgeRatio` is equivalent to the
corresponding denominator-cleared numerator inequality. -/
lemma le_perEdgeRatio_iff {η p t c : ℝ} (h : 0 < 1 - (3 / η) * t) :
    c ≤ perEdgeRatio η p t ↔
      c * (1 - (3 / η) * t)
        ≤ p * (-4 * t) + (1 - p) * (1 - (8 / (3 * Real.pi)) * Fhat t) := by
  rw [perEdgeRatio, le_div_iff₀ h]

/-- For `-1 ≤ t < 1/3`, the ideal-resource denominator `1 - 3*t` is positive. -/
lemma denom_pos_one {t : ℝ} (ht : t ∈ Set.Ico (-1 : ℝ) (1 / 3)) : 0 < 1 - 3 * t := by
  have h := ht.2
  linarith

/-- For `-1 ≤ t < 0.89/3`, the resource-quality denominator `1 - (3/0.89)*t` is positive. -/
lemma denom_pos_089 {t : ℝ} (ht : t ∈ Set.Ico (-1 : ℝ) (0.89 / 3)) :
    0 < 1 - (3 / 0.89) * t := by
  have h89 : (0 : ℝ) < 0.89 := by norm_num
  have h3t : 3 * t < 0.89 := by
    have := ht.2
    linarith
  have heq : (3 / 0.89) * t = 3 * t / 0.89 := by ring
  rw [heq]
  have hlt : 3 * t / 0.89 < 1 := (div_lt_one h89).2 h3t
  linarith

/-- For positive `η`, the set of uniformly achievable lower bounds defining `conditionalRatio η`
is bounded above. -/
lemma conditionalRatio_bddAbove {η : ℝ} (hη : 0 < η) :
    BddAbove {v : ℝ | ∃ p : ℝ, p ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ t : ℝ, t ∈ Set.Ico (-1 : ℝ) (η / 3) → v ≤ perEdgeRatio η p t} := by
  refine ⟨1, ?_⟩
  rintro v ⟨p, hp, hv⟩
  have hmem : (0 : ℝ) ∈ Set.Ico (-1 : ℝ) (η / 3) := by
    refine ⟨by norm_num, ?_⟩
    have : (0 : ℝ) < η / 3 := by positivity
    exact this
  have h := hv 0 hmem
  rw [perEdgeRatio_at_zero] at h
  linarith [hp.1]

/-- The stated numerator certificate on `[-1, 1/3)` implies a 0.651 lower bound for
`perEdgeRatio 1 (345/1000)` throughout that interval. -/
lemma perEdgeRatio_651_of_bound (hnum : ∀ t ∈ Set.Ico (-1 : ℝ) (1 / 3),
    (0.651 : ℝ) * (1 - (3 / (1 : ℝ)) * t)
      ≤ (345 / 1000 : ℝ) * (-4 * t)
        + (1 - 345 / 1000 : ℝ) * (1 - (8 / (3 * Real.pi)) * Fhat t))
    (t : ℝ) (ht : t ∈ Set.Ico (-1 : ℝ) (1 / 3)) :
    (0.651 : ℝ) ≤ perEdgeRatio 1 (345 / 1000) t := by
  have hden : 0 < 1 - (3 / (1 : ℝ)) * t := by
    simpa using denom_pos_one ht
  exact (le_perEdgeRatio_iff (η := (1 : ℝ)) (p := (345 / 1000 : ℝ)) (t := t)
    (c := (0.651 : ℝ)) hden).2 (hnum t ht)

/-- The stated numerator certificate implies `0.651 ≤ conditionalRatio 1`, yielding the scalar
ideal-resource guarantee associated with [CrostaSaubanereHuber2026]. -/
theorem ratio_651_of_bound (hnum : ∀ t ∈ Set.Ico (-1 : ℝ) (1 / 3),
    (0.651 : ℝ) * (1 - (3 / (1 : ℝ)) * t)
      ≤ (345 / 1000 : ℝ) * (-4 * t)
        + (1 - 345 / 1000 : ℝ) * (1 - (8 / (3 * Real.pi)) * Fhat t)) :
    (0.651 : ℝ) ≤ conditionalRatio 1 := by
  unfold conditionalRatio
  refine le_csSup (conditionalRatio_bddAbove (by norm_num))
    ⟨(345 / 1000 : ℝ), ⟨by norm_num, by norm_num⟩, ?_⟩
  intro t ht
  exact perEdgeRatio_651_of_bound hnum t ht

/-- The stated numerator certificate on `[-1, 0.89/3)` implies a 0.614 lower bound for
`perEdgeRatio 0.89 (3825/10000)` throughout that interval. -/
lemma perEdgeRatio_614_of_bound (hnum : ∀ t ∈ Set.Ico (-1 : ℝ) (0.89 / 3),
    (0.614 : ℝ) * (1 - (3 / 0.89) * t)
      ≤ (3825 / 10000 : ℝ) * (-4 * t)
        + (1 - 3825 / 10000 : ℝ) * (1 - (8 / (3 * Real.pi)) * Fhat t))
    (t : ℝ) (ht : t ∈ Set.Ico (-1 : ℝ) (0.89 / 3)) :
    (0.614 : ℝ) ≤ perEdgeRatio 0.89 (3825 / 10000) t := by
  have hden : 0 < 1 - (3 / 0.89) * t := denom_pos_089 ht
  exact (le_perEdgeRatio_iff (η := (0.89 : ℝ)) (p := (3825 / 10000 : ℝ)) (t := t)
    (c := (0.614 : ℝ)) hden).2 (hnum t ht)

/-- The stated numerator certificate implies `0.614 ≤ conditionalRatio 0.89`, yielding the
scalar robust guarantee associated with [CrostaSaubanereHuber2026]. -/
theorem ratio_614_of_bound (hnum : ∀ t ∈ Set.Ico (-1 : ℝ) (0.89 / 3),
    (0.614 : ℝ) * (1 - (3 / 0.89) * t)
      ≤ (3825 / 10000 : ℝ) * (-4 * t)
        + (1 - 3825 / 10000 : ℝ) * (1 - (8 / (3 * Real.pi)) * Fhat t)) :
    (0.614 : ℝ) ≤ conditionalRatio 0.89 := by
  unfold conditionalRatio
  refine le_csSup (conditionalRatio_bddAbove (by norm_num))
    ⟨(3825 / 10000 : ℝ), ⟨by norm_num, by norm_num⟩, ?_⟩
  intro t ht
  exact perEdgeRatio_614_of_bound hnum t ht

end Qatlib.Papers.RydbergMaxCut26.RatioBounds.Core
