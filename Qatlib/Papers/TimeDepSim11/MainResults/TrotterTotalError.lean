/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Time-dependent Trotter–Suzuki total error bound

Source: Poulin–Qarry–Somma–Verstraete, "Quantum simulation of time-dependent
Hamiltonians and the convenient illusion of Hilbert space", fixed arXiv:1102.1360v1
(7 Feb 2011). Displayed bound after Eq. (3) on p. 2–3, and the `Δt = ε/(T c_max² L²)`
choice on p. 3.

The paper iterates the first-order time-dependent Trotter–Suzuki splitting
`log₂ L` times. At the `n`-th level there are `2ⁿ` terms, each of operator norm at
most `c_max L / 2ⁿ`. The accumulated per-segment error is

`½ c_max² (Δt)² · Σ_{m=1}^{M} 2^m (L/2^m)²`,

and the paper bounds this by `½ c_max² L² (Δt)²` using `Σ_{m=1}^{M} 2^m (L/2^m)² = L² Σ 2^{-m} ≤ L²`.
Summing `T/Δt` segments gives the total error `½ T c_max² L² Δt`, which equals `ε/2`
when `Δt = ε/(T c_max² L²)`.

This module formalises exactly these finite-sum and arithmetic statements. The
operator-norm modelling of a single segment is not needed for the bound; only the
elementary inequality is.
-/

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Qatlib.Papers.TimeDepSim11.MainResults.TrotterTotalError

/-- Geometric tail bound: `Σ_{i=0}^{M-1} (1/2)^{i+1} ≤ 1`.
This is the paper's `Σ_{m=1}^{M} 2^m (L/2^m)² = L² Σ_{m=1}^{M} 2^{-m} ≤ L²`
after factoring out `L²`. -/
theorem sum_half_pow_succ_le_one (M : ℕ) :
    (∑ i ∈ Finset.range M, ((1 : ℝ) / 2) ^ (i + 1)) ≤ 1 := by
  have hr : ((1 : ℝ) / 2) ≠ 1 := by norm_num
  have hsum : (∑ i ∈ Finset.range M, ((1 : ℝ) / 2) ^ (i + 1))
      = ((1 : ℝ) / 2) * (∑ i ∈ Finset.range M, ((1 : ℝ) / 2) ^ i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [pow_succ]
    ring
  rw [hsum, geom_sum_eq hr M]
  have hkey : ((1 : ℝ) / 2) * ((((1 : ℝ) / 2) ^ M - 1) / (((1 : ℝ) / 2) - 1))
      = 1 - ((1 : ℝ) / 2) ^ M := by
    field_simp
    ring
  rw [hkey]
  have hp : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ M := by positivity
  linarith

/-- Faithful finite form of the paper's iterated Trotter–Suzuki error sum.
With the paper's index `m = i+1`, this is `Σ_{m=1}^{M} 2^m (L/2^m)² ≤ L²`.
The paper has `M = log₂ L`; no relation between `M` and `L` is required for the bound. -/
theorem trotter_iterated_sum_bound (L : ℝ) (M : ℕ) :
    (∑ i ∈ Finset.range M, (2 : ℝ) ^ (i + 1) * (L / (2 : ℝ) ^ (i + 1)) ^ 2) ≤ L ^ 2 := by
  have hterm : ∀ i : ℕ,
      (2 : ℝ) ^ (i + 1) * (L / (2 : ℝ) ^ (i + 1)) ^ 2
        = L ^ 2 * ((1 : ℝ) / 2) ^ (i + 1) := by
    intro i
    have h2 : (2 : ℝ) ^ (i + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hinv : ((1 : ℝ) / 2) ^ (i + 1) = ((2 : ℝ) ^ (i + 1))⁻¹ := by
      rw [one_div, inv_pow]
    rw [hinv, div_pow]
    field_simp
  calc
    (∑ i ∈ Finset.range M, (2 : ℝ) ^ (i + 1) * (L / (2 : ℝ) ^ (i + 1)) ^ 2)
        = ∑ i ∈ Finset.range M, L ^ 2 * ((1 : ℝ) / 2) ^ (i + 1) := by
          apply Finset.sum_congr rfl
          intro i _
          exact hterm i
    _ = L ^ 2 * (∑ i ∈ Finset.range M, ((1 : ℝ) / 2) ^ (i + 1)) := by
          rw [Finset.mul_sum]
    _ ≤ L ^ 2 * 1 := by
          exact mul_le_mul_of_nonneg_left (sum_half_pow_succ_le_one M) (sq_nonneg L)
    _ = L ^ 2 := by ring

/-- The per-segment error bound of the paper:
`½ c_max² (Δt)² · Σ_{m=1}^{M} 2^m (L/2^m)² ≤ ½ c_max² L² (Δt)²`.
No sign hypothesis on `L` or `Δt` is needed; only `c_max ≥ 0`. -/
theorem trotter_step_error_bound (cmax L dt : ℝ) (M : ℕ) (hcmax : 0 ≤ cmax) :
    (1 / 2) * cmax ^ 2 * dt ^ 2
        * (∑ i ∈ Finset.range M, (2 : ℝ) ^ (i + 1) * (L / (2 : ℝ) ^ (i + 1)) ^ 2)
      ≤ (1 / 2) * cmax ^ 2 * L ^ 2 * dt ^ 2 := by
  have hsum := trotter_iterated_sum_bound L M
  have hc : 0 ≤ (1 / 2 : ℝ) * cmax ^ 2 * dt ^ 2 := by positivity
  calc
    (1 / 2) * cmax ^ 2 * dt ^ 2
        * (∑ i ∈ Finset.range M, (2 : ℝ) ^ (i + 1) * (L / (2 : ℝ) ^ (i + 1)) ^ 2)
        ≤ (1 / 2) * cmax ^ 2 * dt ^ 2 * L ^ 2 :=
          mul_le_mul_of_nonneg_left hsum hc
    _ = (1 / 2) * cmax ^ 2 * L ^ 2 * dt ^ 2 := by ring

/-- Total error over `T`, from `T/Δt` segments each bounded by `½ c_max² L² (Δt)²`:
`(T/Δt) · ½ c_max² L² (Δt)² ≤ ½ T c_max² L² Δt`.
This is the paper's step from the per-segment bound to the total error. -/
theorem trotter_total_error_bound (T cmax L dt : ℝ) (M : ℕ)
    (hT : 0 ≤ T) (hdt : 0 < dt) (hcmax : 0 ≤ cmax) :
    (T / dt) * ((1 / 2) * cmax ^ 2 * L ^ 2 * dt ^ 2)
      ≤ (1 / 2) * T * cmax ^ 2 * L ^ 2 * dt := by
  have hratio : 0 ≤ T / dt := div_nonneg hT hdt.le
  calc
    (T / dt) * ((1 / 2) * cmax ^ 2 * L ^ 2 * dt ^ 2)
        = (1 / 2) * T * cmax ^ 2 * L ^ 2 * dt := by
          field_simp
    _ ≤ (1 / 2) * T * cmax ^ 2 * L ^ 2 * dt := le_refl _

/-- The paper's choice `Δt = ε/(T c_max² L²)` yields total error `ε/2`:
`(T/Δt) · ½ c_max² L² (Δt)² = ε/2`.
This is the final sentence of the p. 2–3 computation. -/
theorem trotter_dt_choice_half_epsilon (ε T cmax L : ℝ)
    (hε : 0 < ε) (hT : 0 < T) (hcmax : 0 < cmax) (hL : 0 < L) :
    (T / (ε / (T * cmax ^ 2 * L ^ 2)))
        * ((1 / 2) * cmax ^ 2 * L ^ 2 * (ε / (T * cmax ^ 2 * L ^ 2)) ^ 2)
      = ε / 2 := by
  have hc : cmax ^ 2 ≠ 0 := pow_ne_zero _ hcmax.ne'
  have hl : L ^ 2 ≠ 0 := pow_ne_zero _ hL.ne'
  field_simp

end Qatlib.Papers.TimeDepSim11.MainResults.TrotterTotalError
