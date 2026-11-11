/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GrandUnif21.MainResults.PhaseEstimation.DeltaRegion

set_option backward.isDefEq.respectTransparency false

/-!
# GrandUnif21 Lemma 13 — `Δ`-region localization

Source: arXiv:2105.02859v3, Lemma 13 (Sec. V A 2, metadata lines 1818--1841),
Appendix B, Eqs. (B14)--(B16) and Fig. 18.

The QSVT sign-function approximation fails on the `Δ`-region
`[1/√2 − Δ/2, 1/√2 + Δ/2]`; the iteration is "in the region" when
`σ^j = |cos π(0.φ[j+1:] − θ)|` lies there.  Lemma 13 states that if `Δ`
satisfies condition (B16),

`1/4 − (1/π) arccos(1/√2 + Δ/2) < 1/16`

then the region can only be hit at the last iteration `j = n-1`.  The
equivant numerical statement, proved below, is that a region hit forces the
deviation `y = 0.φ[j+1:] − θ` to satisfy
`|y| ∈ (1/4 − 1/16, 1/4 + 1/16) ∪ (3/4 − 1/16, 3/4 + 1/16)`;
the region-avoidance at earlier iterations then follows from Lemma 12's
localization `|y| ≤ 1/8`, proved in `SourceTheorem08.lean`.

Reused machinery: `arccos_bounds_of_B16` and `region_bounds` from
`DeltaRegion.lean` (the `arccos` antitone argument of Fig. 18).

Boundary: the trigonometric localization of the deviation.  The identification
`σ^j = |cos π(0.φ[j+1:] − θ)|` (paper Eq. (65)) and the sign-function
approximation model itself are not formalized.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GrandUnif21.MainResults.PhaseEstimation

open scoped Real

/-- GrandUnif21 Lemma 13 (arXiv:2105.02859v3, metadata lines 1818--1841):
under condition (B16) on `Δ ≥ 0`, a `Δ`-region hit
`|cos(π y)| ∈ [1/√2 − Δ/2, 1/√2 + Δ/2]` with `|y| ≤ 1` forces
`|y| ∈ (3/16, 5/16) ∪ (11/16, 13/16)`. -/
theorem source_lemma13 {Δ : ℝ} (hΔ0 : 0 ≤ Δ)
    (hB16 : 1 / 4 - (1 / π) * Real.arccos (1 / Real.sqrt 2 + Δ / 2) < 1 / 16)
    {y : ℝ} (hy : |y| ≤ 1)
    (hreg : |Real.cos (π * y)| ∈
      Set.Icc (1 / Real.sqrt 2 - Δ / 2) (1 / Real.sqrt 2 + Δ / 2)) :
    (1 / 4 - 1 / 16 < |y| ∧ |y| < 1 / 4 + 1 / 16) ∨
      (3 / 4 - 1 / 16 < |y| ∧ |y| < 3 / 4 + 1 / 16) := by
  obtain ⟨hA1gt, hA2lt⟩ := arccos_bounds_of_B16 hΔ0 hB16
  have hcosu : |Real.cos (π * y)| = |Real.cos (π * |y|)| := by
    have h : Real.cos (π * y) = Real.cos (π * |y|) := by
      rw [← Real.cos_abs (π * y)]
      congr 1
      rw [abs_mul, abs_of_pos Real.pi_pos]
    rw [h]
  have hreg' : |Real.cos (π * |y|)| ∈
      Set.Icc (1 / Real.sqrt 2 - Δ / 2) (1 / Real.sqrt 2 + Δ / 2) := by
    rwa [← hcosu]
  have hy0 : 0 ≤ |y| := abs_nonneg y
  by_cases hhalf : |y| ≤ 1 / 2
  · have hb := region_bounds (c := 1 / Real.sqrt 2)
      (A₁ := Real.arccos (1 / Real.sqrt 2 + Δ / 2))
      (A₂ := Real.arccos (1 / Real.sqrt 2 - Δ / 2)) rfl rfl hA1gt hA2lt hy0 hhalf hreg'
    obtain ⟨hb1, hb2⟩ := hb
    exact Or.inl ⟨by linarith, by linarith⟩
  · push_neg at hhalf
    have hv0 : 0 ≤ 1 - |y| := by linarith
    have hvhalf : 1 - |y| ≤ 1 / 2 := by linarith
    have hcosv : |Real.cos (π * |y|)| = |Real.cos (π * (1 - |y|))| := by
      have h : Real.cos (π * |y|) = -Real.cos (π * (1 - |y|)) := by
        have harg : π * |y| = π - π * (1 - |y|) := by ring
        rw [harg, Real.cos_pi_sub]
      rw [h, abs_neg]
    have hreg'' : |Real.cos (π * (1 - |y|))| ∈
        Set.Icc (1 / Real.sqrt 2 - Δ / 2) (1 / Real.sqrt 2 + Δ / 2) := by
      simpa [hcosv] using hreg'
    have hb := region_bounds (c := 1 / Real.sqrt 2)
      (A₁ := Real.arccos (1 / Real.sqrt 2 + Δ / 2))
      (A₂ := Real.arccos (1 / Real.sqrt 2 - Δ / 2)) rfl rfl hA1gt hA2lt hv0 hvhalf hreg''
    obtain ⟨h1, h2⟩ := hb
    exact Or.inr ⟨by linarith, by linarith⟩

end Qatlib.Papers.GrandUnif21.MainResults.PhaseEstimation
