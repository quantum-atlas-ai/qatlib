/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HSPAffine13.MainResults.AffineModel.InjectiveOnC

set_option backward.isDefEq.respectTransparency false

/-!
# The aligned orbit of `C_b`

Theorem 4 distinguishes the aligned case `x = b / (1 - u)` from the generic
case.  In the aligned case every element of the orbit `C_b · g` has the same
translation coordinate, and if `u` generates `Fˣ` the orbit is exactly the
horizontal line through `g` in the coordinates `(a, b) = (Fˣ, F)`.

This file proves that orbit description; it is the set-theoretic input for
the Fourier computation in `Theorem4Aligned`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.HSPAffine13.MainResults

open AffineGroup

variable {F : Type*} [Field F]

/-- In the aligned case, multiplying by any element of `C_b` preserves the
translation coordinate. -/
theorem C_mul_second_eq (u : Fˣ) (b v : F) (hu : (u : F) ≠ 1)
    (hv : b + (u : F) * v = v) (a : Fˣ) (j : ℤ) :
    (((⟨u, b⟩ : AffineGroup F) ^ j) * (⟨a, v⟩ : AffineGroup F)).b = v := by
  rw [mul_b, zpow_a, zpow_b_eq u b hu j, Units.val_zpow_eq_zpow_val]
  have hden : (u : F) - 1 ≠ 0 := sub_ne_zero.mpr hu
  have hnum : b = v - (u : F) * v := by
    calc
      b = (b + (u : F) * v) - (u : F) * v := by ring
      _ = v - (u : F) * v := by rw [hv]
  rw [hnum]
  field_simp [hden]
  ring

/-- In the aligned case, the orbit `C_b · g` is exactly the horizontal line
through `g`, provided `u` generates `Fˣ`. -/
theorem mem_orbit_iff_second_eq (u : Fˣ) (b : F) (hu : (u : F) ≠ 1)
    (hgen : Subgroup.zpowers u = ⊤) (g h : AffineGroup F)
    (hg : g.b = b / (1 - (u : F))) :
    (∃ c ∈ C u b, c * g = h) ↔ h.b = g.b := by
  have hv : b + (u : F) * g.b = g.b := by
    rw [hg]
    have hden : 1 - (u : F) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
    field_simp [hden]
    ring
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨j, rfl⟩ := (mem_C_iff u b c).mp hc
    exact C_mul_second_eq u b g.b hu hv g.a j
  · intro hb
    have hgen_a : h.a * g.a⁻¹ ∈ Subgroup.zpowers u := by
      rw [hgen]
      exact Subgroup.mem_top _
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hgen_a
    refine ⟨(⟨u, b⟩ : AffineGroup F) ^ j, Subgroup.zpow_mem_zpowers _ _, ?_⟩
    ext
    · rw [mul_a, zpow_a, hj]
      simp
    · rw [hb]
      exact C_mul_second_eq u b g.b hu hv g.a j

end Qatlib.Papers.HSPAffine13.MainResults
