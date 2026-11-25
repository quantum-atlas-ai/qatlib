/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DysonSeries22.HistoryReadout
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

/-!
# A lower bound for the RHS preparation amplitude

A common positive lower bound on the segment norms can be substituted into the
sum of squares. The initial-state weight can only improve the resulting normalized
amplitude when the segment lower bound lies below the normalization scale.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.DysonSeries22.QuantumCompile

/-- The numerical preparation amplitude in Eq. (63) is bounded below by the ratio
of the common segment norm lower bound to the forcing normalization. -/
theorem dyson_success_lower_bound {r : ℕ} (hr : 0 < r)
    (lamX lamB dt vMin : ℝ) (hv : 0 < vMin)
    (hscale : vMin ≤ (Real.exp 1 - 1) * lamB * dt)
    (vNorm : Fin r → ℝ) (hNorm : ∀ j, vMin ≤ vNorm j) :
    vMin / ((Real.exp 1 - 1) * lamB * dt) ≤
      Real.sqrt ((lamX ^ 2 + ∑ j, vNorm j ^ 2) /
        (lamX ^ 2 + ((Real.exp 1 - 1) * lamB * dt) ^ 2 * (r : ℝ))) := by
  let q := (Real.exp 1 - 1) * lamB * dt
  have hq : 0 < q := hv.trans_le hscale
  have hq₂ : 0 < q ^ 2 := sq_pos_of_pos hq
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hden : 0 < lamX ^ 2 + q ^ 2 * (r : ℝ) :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hq₂ hr')
  have hsum : (r : ℝ) * vMin ^ 2 ≤ ∑ j, vNorm j ^ 2 := by
    simpa using (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin r)))
      (fun j _ => pow_le_pow_left₀ hv.le (hNorm j) 2))
  have hv₂ : vMin ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ hv.le hscale 2
  have hnum : 0 ≤ lamX ^ 2 + ∑ j, vNorm j ^ 2 :=
    add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  change vMin / q ≤ Real.sqrt ((lamX ^ 2 + ∑ j, vNorm j ^ 2) / (lamX ^ 2 + q ^ 2 * r))
  rw [Real.le_sqrt (div_nonneg hv.le hq.le) (div_nonneg hnum hden.le), div_pow,
    div_le_div_iff₀ hq₂ hden]
  have hA := mul_le_mul_of_nonneg_right hv₂ (sq_nonneg lamX)
  have hB' := mul_le_mul_of_nonneg_right hsum hq₂.le
  nlinarith

end Qatlib.Papers.DysonSeries22.QuantumCompile
