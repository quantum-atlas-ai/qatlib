/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
import Mathlib.Analysis.SpecialFunctions.Log.Base
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ThermalRate98.MainResults

open Qatlib.Concepts.SpectralFilter.PhaseReadout (QFTMatrix primRoot
  qftMatrix_apply primRoot_zpow_eq_exp)

theorem source_fourier_kernel_eq_qftMatrix (N : ℕ) (j j' : Fin N) :
    QFTMatrix N j j' =
      (Real.sqrt (N : ℝ) : ℂ)⁻¹ *
        Complex.exp (2 * Real.pi * Complex.I * ((j.val : ℝ) * (j'.val : ℝ) / (N : ℝ))) := by
  rw [qftMatrix_apply, primRoot_zpow_eq_exp]
  congr 1
  push_cast
  ring

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
