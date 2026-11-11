/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Split propagation phases and Fourier resolution

This module proves the scalar phase identities underlying the diagonal Fourier factorization of
the split propagation kernel in [LidarWang1999]. Under the resolution relation, the two
quadratic phases and the Fourier cross term combine into the displacement-squared phase.

It also identifies the Fourier matrix entries and derives the base-two logarithmic register size
from the resolution relation for a power-of-two dimension.

## Main statements

* `source_split_operator_phase_identity`: combines the quadratic and Fourier phases
  algebraically.
* `source_split_operator_kernel_factorization`: lifts the phase identity to complex
  exponentials.
* `source_qubit_count_log2`: recovers the register size from the resolution parameters.

## References

* [Lidar and Wang, 1999][LidarWang1999]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ThermalRate98.MainResults

open Qatlib.Concepts.SpectralFilter.PhaseReadout (QFTMatrix primRoot
  qftMatrix_apply primRoot_zpow_eq_exp)

/-- Each QFT matrix entry is the inverse square-root normalization times the positive Fourier
phase for its two indices. -/
theorem source_fourier_kernel_eq_qftMatrix (N : ℕ) (j j' : Fin N) :
    QFTMatrix N j j' =
      (Real.sqrt (N : ℝ) : ℂ)⁻¹ *
        Complex.exp (2 * Real.pi * Complex.I * ((j.val : ℝ) * (j'.val : ℝ) / (N : ℝ))) := by
  rw [qftMatrix_apply, primRoot_zpow_eq_exp]
  congr 1
  push_cast
  ring

/-- For nonzero dimension and time step satisfying the resolution relation, the two quadratic
phases and Fourier cross term sum to the displacement-squared phase plus the potential
phase. -/
theorem source_split_operator_phase_identity
    (m Δx Δt N : ℝ) (hN : N ≠ 0) (hΔt : Δt ≠ 0)
    (hres : m * Δx ^ 2 / Δt = 2 * Real.pi / N)
    (V : ℝ) (j j' : ℤ) :
    (-Real.pi * (j : ℝ) ^ 2 / N + V * Δt)
        + 2 * Real.pi * (j : ℝ) * (j' : ℝ) / N
        + (-Real.pi * (j' : ℝ) ^ 2 / N)
      = -m * ((j : ℝ) - (j' : ℝ)) ^ 2 * Δx ^ 2 / (2 * Δt) + V * Δt := by

  have hcross : m * Δx ^ 2 * N = 2 * Real.pi * Δt := by
    field_simp [hN, hΔt] at hres
    linarith [hres]

  have hmx : m * Δx ^ 2 = 2 * Real.pi * Δt / N := by
    rw [eq_div_iff hN]
    linarith [hcross]
  have hrearr : -m * ((j : ℝ) - (j' : ℝ)) ^ 2 * Δx ^ 2 / (2 * Δt)
      = -((j : ℝ) - (j' : ℝ)) ^ 2 * (m * Δx ^ 2) / (2 * Δt) := by
    ring
  rw [hrearr, hmx]
  field_simp [hN, hΔt]
  ring

/-- Under the nonzero dimension, nonzero time step, and resolution hypotheses, the product of
the two quadratic phase exponentials and the Fourier phase equals the displacement-kernel
phase exponential. -/
theorem source_split_operator_kernel_factorization
    (m Δx Δt N : ℝ) (hN : N ≠ 0) (hΔt : Δt ≠ 0)
    (hres : m * Δx ^ 2 / Δt = 2 * Real.pi / N)
    (V : ℝ) (j j' : ℤ) :
    Complex.exp (Complex.I * (-Real.pi * (j : ℝ) ^ 2 / N + V * Δt))
        * Complex.exp (Complex.I * (2 * Real.pi * (j : ℝ) * (j' : ℝ) / N))
        * Complex.exp (Complex.I * (-Real.pi * (j' : ℝ) ^ 2 / N))
      = Complex.exp
          (Complex.I * (-m * ((j : ℝ) - (j' : ℝ)) ^ 2 * Δx ^ 2 / (2 * Δt) + V * Δt)) := by
  have hsum :
      Complex.I * (-Real.pi * (j : ℝ) ^ 2 / N + V * Δt)
          + Complex.I * (2 * Real.pi * (j : ℝ) * (j' : ℝ) / N)
          + Complex.I * (-Real.pi * (j' : ℝ) ^ 2 / N)
        = Complex.I * (-m * ((j : ℝ) - (j' : ℝ)) ^ 2 * Δx ^ 2 / (2 * Δt) + V * Δt) := by
    have hreal := source_split_operator_phase_identity m Δx Δt N hN hΔt hres V j j'
    have hpull :
        Complex.I * (-Real.pi * (j : ℝ) ^ 2 / N + V * Δt)
            + Complex.I * (2 * Real.pi * (j : ℝ) * (j' : ℝ) / N)
            + Complex.I * (-Real.pi * (j' : ℝ) ^ 2 / N)
          = Complex.I * ((-Real.pi * (j : ℝ) ^ 2 / N + V * Δt)
            + (2 * Real.pi * (j : ℝ) * (j' : ℝ) / N)
            + (-Real.pi * (j' : ℝ) ^ 2 / N)) := by
      ring
    rw [hpull]

    have hcast := congrArg (fun r : ℝ => (r : ℂ)) hreal
    push_cast at hcast ⊢
    rw [hcast]
  calc
    Complex.exp (Complex.I * (-Real.pi * (j : ℝ) ^ 2 / N + V * Δt))
        * Complex.exp (Complex.I * (2 * Real.pi * (j : ℝ) * (j' : ℝ) / N))
        * Complex.exp (Complex.I * (-Real.pi * (j' : ℝ) ^ 2 / N))
        = Complex.exp
            (Complex.I * (-Real.pi * (j : ℝ) ^ 2 / N + V * Δt)
              + Complex.I * (2 * Real.pi * (j : ℝ) * (j' : ℝ) / N)
              + Complex.I * (-Real.pi * (j' : ℝ) ^ 2 / N)) := by
          rw [← Complex.exp_add, ← Complex.exp_add]
    _ = Complex.exp
          (Complex.I * (-m * ((j : ℝ) - (j' : ℝ)) ^ 2 * Δx ^ 2 / (2 * Δt) + V * Δt)) := by
          rw [hsum]

/-- For nonzero mass, grid spacing, and time step satisfying the power-of-two resolution
relation, the base-two logarithm of `2 * π * Δt / (m * Δx²)` equals `ν`. See
[LidarWang1999]. -/
theorem source_qubit_count_log2
    (m Δx Δt : ℝ) (ν : ℕ) (hm : m ≠ 0) (hΔx : Δx ≠ 0) (hΔt : Δt ≠ 0)
    (hres : m * Δx ^ 2 / Δt = 2 * Real.pi / (2 : ℝ) ^ ν) :
    Real.logb 2 (2 * Real.pi * Δt / (m * Δx ^ 2)) = ν := by
  have hmain : 2 * Real.pi * Δt / (m * Δx ^ 2) = (2 : ℝ) ^ ν := by
    have hNne : (2 : ℝ) ^ ν ≠ 0 := pow_ne_zero _ (by norm_num)
    have hmx : m * Δx ^ 2 ≠ 0 := mul_ne_zero hm (pow_ne_zero 2 hΔx)
    rw [div_eq_iff hmx]
    field_simp [hNne, hΔt] at hres
    linarith
  rw [hmain, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  ring

end Qatlib.Papers.ThermalRate98.MainResults
