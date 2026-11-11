/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# qDRIFT exponential-count bound

Defines `qdriftExponentials` and proves the explicit fourth-power coefficient-mass and
inverse-precision bound associated with Appendix D of [LeeEtAl2021]. Bounding both shifted phase
magnitudes by `2π` yields the constant `8π²`.

## Main statements

* `max_pi_shift_le`: bounds the shifted phase magnitudes for `|phi| ≤ π`.
* `d14_scaling`: bounds the defined exponential-count expression for positive precision.

## References

* [Lee et al., 2021][LeeEtAl2021]
-/

set_option autoImplicit false

namespace Qatlib.Papers.TensorHyper20.MainResults.QdriftScaling

/-- The real-valued exponential-count expression `4 * phiMax^2 * lam^4 / (2 * eps^4)`. -/
noncomputable def qdriftExponentials (phiMax lam eps : ℝ) : ℝ :=
  4 * phiMax ^ 2 * lam ^ 4 / (2 * eps ^ 4)

/-- If `|phi| ≤ π`, then the maximum of `|π - phi|` and `|π + phi|` is at most `2π`. -/
theorem max_pi_shift_le (phi : ℝ) (hphi : |phi| ≤ Real.pi) :
    max |Real.pi - phi| |Real.pi + phi| ≤ 2 * Real.pi := by
  have h := abs_le.mp hphi
  apply max_le
  · exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2, Real.pi_pos]⟩
  · exact abs_le.mpr ⟨by linarith [h.1, Real.pi_pos], by linarith [h.2]⟩

/-- For `|phi| ≤ π` and positive `eps`, the specified qDRIFT expression is at most `8π² * lam^4
/ eps^4`. -/
theorem d14_exponentials_bound (phi lam eps : ℝ) (hphi : |phi| ≤ Real.pi)
    (heps : 0 < eps) :
    qdriftExponentials (max |Real.pi - phi| |Real.pi + phi|) lam eps
      ≤ 8 * Real.pi ^ 2 * lam ^ 4 / eps ^ 4 := by
  have hmax := max_pi_shift_le phi hphi
  have hmax0 : 0 ≤ max |Real.pi - phi| |Real.pi + phi| :=
    le_trans (abs_nonneg _) (le_max_left _ _)
  have h2 : max |Real.pi - phi| |Real.pi + phi| * max |Real.pi - phi| |Real.pi + phi|
      ≤ (2 * Real.pi) * (2 * Real.pi) :=
    mul_le_mul hmax hmax hmax0 (by positivity)
  unfold qdriftExponentials
  rw [pow_two]
  have hden : (0 : ℝ) < 2 * eps ^ 4 := by positivity
  have hnum :
      4 * (max |Real.pi - phi| |Real.pi + phi| * max |Real.pi - phi| |Real.pi + phi|)
          * lam ^ 4
        ≤ 4 * ((2 * Real.pi) * (2 * Real.pi)) * lam ^ 4 := by
    have := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ lam ^ 4)
    nlinarith
  calc
    4 * (max |Real.pi - phi| |Real.pi + phi| * max |Real.pi - phi| |Real.pi + phi|)
        * lam ^ 4 / (2 * eps ^ 4)
        ≤ 4 * ((2 * Real.pi) * (2 * Real.pi)) * lam ^ 4 / (2 * eps ^ 4) := by
          exact div_le_div_of_nonneg_right hnum (le_of_lt hden)
    _ = 8 * Real.pi ^ 2 * lam ^ 4 / eps ^ 4 := by
          field_simp
          ring

/-- For a phase in `[-π, π]` and positive precision, bounds the defined qDRIFT expression by
`8π²` times `lam^4 / eps^4`. See [LeeEtAl2021]. -/
theorem d14_scaling (phi lam eps : ℝ) (hphi : |phi| ≤ Real.pi)
    (heps : 0 < eps) :
    qdriftExponentials (max |Real.pi - phi| |Real.pi + phi|) lam eps
      ≤ 8 * Real.pi ^ 2 * (lam ^ 4 / eps ^ 4) := by
  have h := d14_exponentials_bound phi lam eps hphi heps
  calc
    qdriftExponentials (max |Real.pi - phi| |Real.pi + phi|) lam eps
        ≤ 8 * Real.pi ^ 2 * lam ^ 4 / eps ^ 4 := h
    _ = 8 * Real.pi ^ 2 * (lam ^ 4 / eps ^ 4) := by ring

end Qatlib.Papers.TensorHyper20.MainResults.QdriftScaling
