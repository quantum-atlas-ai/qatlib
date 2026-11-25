/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.NullLinking.MagneticCircles

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The oriented crossing of the disk spanning the magnetic pole

[IrvineBouwmeester2008KnottedLight], Eq. (2) and Fig. 1,
[DOI](https://doi.org/10.1038/nphys1056).
Each finite nonzero initial magnetic circle crosses the flat unit disk
spanning the projective pole at one interior point. The finite circle
crosses positively relative to the pole's oriented boundary.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.NullLinking

/-- The initial circle lies in the plane of the pole disk exactly
when the sine of its parameter vanishes. -/
private theorem initial_circle_first_eq_zero_iff (u v θ : ℝ) (hd : 0 < u ^ 2 + v ^ 2) :
    initialMagneticCircle u v θ 0 = 0 ↔ Real.sin θ = 0 := by
  change 0 + -(Real.sqrt (u ^ 2 + v ^ 2) * Real.sin θ) / (u ^ 2 + v ^ 2) = 0 ↔ _
  rw [zero_add, div_eq_zero_iff, or_iff_left hd.ne', neg_eq_zero, mul_eq_zero,
    or_iff_right (Real.sqrt_pos.2 hd).ne']

/-- The squared radius from the pole disk's center, at either plane
crossing of a finite magnetic circle. -/
private theorem initial_circle_radius_sq_on_pole_plane (u v θ : ℝ) (hd : 0 < u ^ 2 + v ^ 2)
    (hθ : Real.sin θ = 0) :
    initialMagneticCircle u v θ 1 ^ 2 + initialMagneticCircle u v θ 2 ^ 2 =
      (Real.sqrt (u ^ 2 + v ^ 2 + 1) * Real.cos θ - 1) ^ 2 / (u ^ 2 + v ^ 2) := by
  let d := u ^ 2 + v ^ 2
  let r := Real.sqrt (d + 1)
  let q := Real.sqrt d
  change (-u / d + (u * (r * Real.cos θ) + v * (q * Real.sin θ)) / d) ^ 2 +
    (-v / d + (v * (r * Real.cos θ) - u * (q * Real.sin θ)) / d) ^ 2 =
    (r * Real.cos θ - 1) ^ 2 / d
  simp only [hθ, mul_zero, add_zero, sub_zero]
  field_simp [show d ≠ 0 from hd.ne']
  dsimp only [d]
  ring

/-- A finite nonzero initial magnetic circle meets the pole's closed
disk only at the angle zero modulo its full period. -/
theorem initial_magnetic_circle_mem_pole_disk_iff (u v θ : ℝ) (hd : 0 < u ^ 2 + v ^ 2) :
    (initialMagneticCircle u v θ 0 = 0 ∧
      initialMagneticCircle u v θ 1 ^ 2 + initialMagneticCircle u v θ 2 ^ 2 ≤ 1) ↔
    Real.cos θ = 1 := by
  let r := Real.sqrt (u ^ 2 + v ^ 2 + 1)
  have hr : 1 < r := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hr2 : r ^ 2 = u ^ 2 + v ^ 2 + 1 := Real.sq_sqrt (by positivity)
  constructor
  · rintro ⟨hx, hrad⟩
    have hθ := (initial_circle_first_eq_zero_iff u v θ hd).1 hx
    rw [initial_circle_radius_sq_on_pole_plane u v θ hd hθ] at hrad
    rcases Real.sin_eq_zero_iff_cos_eq.mp hθ with h | h
    · exact h
    · rw [h] at hrad
      have hbound := (div_le_iff₀ hd).1 hrad
      change (r * (-1) - 1) ^ 2 ≤ 1 * (u ^ 2 + v ^ 2) at hbound
      nlinarith only [hr2, hr, hbound]
  · intro h
    have hθ := Real.sin_eq_zero_iff_cos_eq.mpr (Or.inl h)
    refine ⟨(initial_circle_first_eq_zero_iff u v θ hd).2 hθ, ?_⟩
    rw [initial_circle_radius_sq_on_pole_plane u v θ hd hθ, h]
    apply (div_le_iff₀ hd).2
    change (r * 1 - 1) ^ 2 ≤ 1 * (u ^ 2 + v ^ 2)
    nlinarith only [hr, hr2]

/-- The unique crossing in the interval [0,2π) is at zero, lies in
the open disk, and has positive normal speed relative to the orientation
of the pole boundary (0, cos θ, -sin θ). -/
theorem initial_magnetic_circle_pole_disk_positive_crossing (u v : ℝ)
    (hd : 0 < u ^ 2 + v ^ 2) :
    ∃! θ : ℝ, θ ∈ Set.Ico 0 (2 * Real.pi) ∧ initialMagneticCircle u v θ 0 = 0 ∧
      initialMagneticCircle u v θ 1 ^ 2 + initialMagneticCircle u v θ 2 ^ 2 < 1 ∧
      0 < -deriv (fun s => initialMagneticCircle u v s 0) θ := by
  refine ⟨0, ⟨⟨le_rfl, by positivity⟩, ?_, ?_, ?_⟩, ?_⟩
  · exact (initial_circle_first_eq_zero_iff u v 0 hd).mpr Real.sin_zero
  · rw [initial_circle_radius_sq_on_pole_plane u v 0 hd Real.sin_zero, Real.cos_zero]
    apply (div_lt_iff₀ hd).2
    let r := Real.sqrt (u ^ 2 + v ^ 2 + 1)
    have hr : 1 < r := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    have hr2 : r ^ 2 = u ^ 2 + v ^ 2 + 1 := Real.sq_sqrt (by positivity)
    change (r * 1 - 1) ^ 2 < 1 * (u ^ 2 + v ^ 2)
    nlinarith only [hr, hr2]
  · rw [(hasDerivAt_initial_magnetic_circle u v 0 0).deriv]
    change 0 < - (-(Real.sqrt (u ^ 2 + v ^ 2) * Real.cos 0) / (u ^ 2 + v ^ 2))
    rw [Real.cos_zero, mul_one, neg_div, neg_neg]
    exact div_pos (Real.sqrt_pos.2 hd) hd
  · rintro θ ⟨hθ, hx, hr, _⟩
    have hcos := (initial_magnetic_circle_mem_pole_disk_iff u v θ hd).1 ⟨hx, hr.le⟩
    exact (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos, hθ.1]) hθ.2).mp hcos

end Qatlib.Papers.KnottedLight08.NullLinking
