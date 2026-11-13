/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QChemistry14.ScalarModels.Definitions

/-!
# Scalar Trotter error and cost bounds

`trotterErrorBound` and `trotterStep` model a quadratic step error and its precision-dependent
step size. The module rewrites the resulting call count and proves an explicit bound
proportional to M⁵ log M for the scalar cost expression used in the chemistry analysis. See
[McCleanEtAl2014].

## Main statements

* `trotter_error_le_precision`: controls any error bounded by the scalar Trotter model.
* `trotter_Nc_rewrite`: evaluates the call count at the chosen step size.
* `trotter_bigO`: bounds the cost expression by an explicit multiple of M⁵ log M.

## References

* [McClean et al., 2014][McCleanEtAl2014]
-/

set_option autoImplicit false

namespace Qatlib.Papers.QChemistry14.ScalarModels.TrotterCost

noncomputable section

/-- The scalar Trotter error model `C ^ 3 * dt ^ 2`. -/
def trotterErrorBound (C dt : ℝ) : ℝ := C ^ 3 * dt ^ 2

/-- The step size `Real.sqrt (ε / C ^ 3)` selected for the scalar error budget. -/
def trotterStep (C ε : ℝ) : ℝ := Real.sqrt (ε / C ^ 3)

/-- The scalar call count `Ng * T / dt` for gate multiplicity `Ng`, duration `T`, and step size
`dt`. -/
def trotterCallCount (Ng T dt : ℝ) : ℝ := Ng * T / dt

/-- The scalar gate cost `C ^ (3 / 2 : ℝ) * Ng / ε ^ (3 / 2 : ℝ)`. -/
def trotterGateCount (C Ng ε : ℝ) : ℝ :=
  C ^ (3 / 2 : ℝ) * Ng / ε ^ (3 / 2 : ℝ)

/-- For positive `C` and `ε`, a nonnegative step at most `trotterStep C ε` has square at most `ε
/ C ^ 3`. -/
theorem step_sq_le (C ε dt : ℝ) (hC : 0 < C) (hε : 0 < ε) (hdt : 0 ≤ dt)
    (hstep : dt ≤ trotterStep C ε) :
    dt ^ 2 ≤ ε / C ^ 3 := by
  unfold trotterStep at hstep
  have hεC : 0 ≤ ε / C ^ 3 := by positivity
  have hsq : dt ^ 2 ≤ (Real.sqrt (ε / C ^ 3)) ^ 2 :=
    pow_le_pow_left₀ hdt hstep 2
  rwa [Real.sq_sqrt hεC] at hsq

/-- An error bounded by `trotterErrorBound C dt` is at most `ε` when `C` and `ε` are positive
and the nonnegative step is at most `trotterStep C ε`. -/
theorem trotter_error_le_precision (E1 C ε dt : ℝ) (hC : 0 < C) (hε : 0 < ε)
    (hdt : 0 ≤ dt) (hE1 : E1 ≤ trotterErrorBound C dt) (hstep : dt ≤ trotterStep C ε) :
    E1 ≤ ε := by
  have hsq : dt ^ 2 ≤ ε / C ^ 3 := step_sq_le C ε dt hC hε hdt hstep
  have hC3 : 0 < C ^ 3 := by positivity
  have hmul : C ^ 3 * dt ^ 2 ≤ C ^ 3 * (ε / C ^ 3) :=
    mul_le_mul_of_nonneg_left hsq (le_of_lt hC3)
  have heq : C ^ 3 * (ε / C ^ 3) = ε := by field_simp
  unfold trotterErrorBound at hE1
  linarith

/-- For positive `C` and `ε`, substituting `trotterStep C ε` into the call count gives `C ^ (3 /
2 : ℝ) * Ng * T / ε ^ (1 / 2 : ℝ)`. -/
theorem trotter_Nc_rewrite (C Ng ε T : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    trotterCallCount Ng T (trotterStep C ε)
      = C ^ (3 / 2 : ℝ) * Ng * T / ε ^ (1 / 2 : ℝ) := by
  unfold trotterCallCount trotterStep
  have hC3 : (0 : ℝ) < C ^ 3 := by positivity
  rw [Real.sqrt_div' ε (le_of_lt hC3)]
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [show (C ^ 3) ^ (1 / 2 : ℝ) = C ^ (3 / 2 : ℝ) by
    rw [← Real.rpow_natCast C 3]
    rw [← Real.rpow_mul (le_of_lt hC)]
    norm_num]
  field_simp

/-- For `M ≥ 1`, nonnegative coefficients, and positive precision, the displayed scalar cost is
at most `2 * (β + h) ^ (3 / 2 : ℝ) * M ^ 5 * Real.log M / ε ^ (3 / 2 : ℝ)`. This is the
scalar estimate associated with Eqs. (34)–(37) of [McCleanEtAl2014]. -/
theorem trotter_bigO (β h M ε : ℝ) (hM : 1 ≤ M) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hε : 0 < ε) :
    (β * M ^ (5 / 3 : ℝ) + h * M ^ 2) ^ (3 / 2 : ℝ) * ((M + M ^ 2) * Real.log M)
        / ε ^ (3 / 2 : ℝ)
      ≤ (2 * (β + h) ^ (3 / 2 : ℝ)) * M ^ 5 * Real.log M / ε ^ (3 / 2 : ℝ) := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hpow : M ^ (5 / 3 : ℝ) ≤ M ^ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := M) (y := 5 / 3) (z := ((2:ℕ):ℝ)) hM
      (by norm_num)
    rwa [Real.rpow_natCast] at h
  have hM5 : 0 ≤ M ^ (5 / 3 : ℝ) := Real.rpow_nonneg (le_of_lt hMpos) _
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  have hB0 : 0 ≤ β * M ^ (5 / 3 : ℝ) + h * M ^ 2 :=
    add_nonneg (mul_nonneg hβ hM5) (mul_nonneg hh hM2)
  have hB : β * M ^ (5 / 3 : ℝ) + h * M ^ 2 ≤ (β + h) * M ^ 2 := by
    have h1 : β * M ^ (5 / 3 : ℝ) ≤ β * M ^ 2 := mul_le_mul_of_nonneg_left hpow hβ
    have hexp : (β + h) * M ^ 2 = β * M ^ 2 + h * M ^ 2 := by ring
    rw [hexp]; linarith
  have hBh : 0 ≤ (β + h) * M ^ 2 := mul_nonneg (by linarith) hM2
  have hBpow : (β * M ^ (5 / 3 : ℝ) + h * M ^ 2) ^ (3 / 2 : ℝ)
      ≤ ((β + h) * M ^ 2) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hB0 hB (by norm_num)
  have hp : (M ^ 2) ^ (3 / 2 : ℝ) = M ^ 3 := by
    rw [← Real.rpow_natCast M 2]
    rw [← Real.rpow_mul (le_of_lt hMpos) ((2 : ℕ) : ℝ) (3 / 2 : ℝ)]
    rw [show ((2 : ℕ) : ℝ) * (3 / 2 : ℝ) = ((3 : ℕ) : ℝ) by norm_num]
    rw [Real.rpow_natCast]
  have hBhEq : ((β + h) * M ^ 2) ^ (3 / 2 : ℝ)
      = (β + h) ^ (3 / 2 : ℝ) * M ^ 3 := by
    rw [Real.mul_rpow (by linarith) hM2]
    rw [hp]
  have hsum : M + M ^ 2 ≤ 2 * M ^ 2 := by nlinarith
  have hlog0 : 0 ≤ Real.log M := Real.log_nonneg hM
  have hsum0 : 0 ≤ M + M ^ 2 := by positivity
  have hM2log : 0 ≤ (M + M ^ 2) * Real.log M := mul_nonneg hsum0 hlog0
  have hup : (β * M ^ (5 / 3 : ℝ) + h * M ^ 2) ^ (3 / 2 : ℝ) * ((M + M ^ 2) * Real.log M)
      ≤ ((β + h) ^ (3 / 2 : ℝ) * M ^ 3) * (2 * M ^ 2 * Real.log M) := by
    rw [← hBhEq]
    apply mul_le_mul hBpow _ hM2log _
    · exact mul_le_mul_of_nonneg_right hsum hlog0
    · positivity
  have heq : ((β + h) ^ (3 / 2 : ℝ) * M ^ 3) * (2 * M ^ 2 * Real.log M)
      = (2 * (β + h) ^ (3 / 2 : ℝ)) * M ^ 5 * Real.log M := by ring
  calc
    (β * M ^ (5 / 3 : ℝ) + h * M ^ 2) ^ (3 / 2 : ℝ) * ((M + M ^ 2) * Real.log M)
        / ε ^ (3 / 2 : ℝ)
        ≤ ((β + h) ^ (3 / 2 : ℝ) * M ^ 3) * (2 * M ^ 2 * Real.log M)
            / ε ^ (3 / 2 : ℝ) :=
          div_le_div_of_nonneg_right hup (Real.rpow_nonneg (le_of_lt hε) _)
    _ = (2 * (β + h) ^ (3 / 2 : ℝ)) * M ^ 5 * Real.log M / ε ^ (3 / 2 : ℝ) := by
          rw [heq]

end
end Qatlib.Papers.QChemistry14.ScalarModels.TrotterCost
