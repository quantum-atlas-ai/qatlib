/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PhaseEst07.MainResults.VarianceState
import Qatlib.Papers.PhaseEst07.MainResults.Shared.PathShift

/-!
# Fidelity cost and its sine-state optimum

The amplitude `sourceFidelityAmplitude` adds a common phase to the normalized sine vector, and
`sourceFidelityObjective` sums adjacent correlations of two real sequences. The objective bound
gives the fidelity-cost lower bound, which is attained by the sine vector with zero imaginary
component. The phase-estimation setting is described in [VanDamEtAl2007].

## Main statements

* `source_fidelity_cost_ge`: For `N ≥ 1`, the fidelity cost of two sequences with combined
  squared norm one is at least `sin (π / (2 * (N + 2))) ^ 2`.
* `source_fidelity_cost_attained`: For `N ≥ 1`, the sine vector and zero sequence attain
  fidelity cost `sin (π / (2 * (N + 2))) ^ 2`.

## References

* [van Dam et al., 2007][VanDamEtAl2007]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PhaseEst07.MainResults.FidelityAppendix

open Qatlib.Papers.PhaseEst07.MainResults.VarianceState
open Qatlib.Papers.PhaseEst07.MainResults.Shared
open scoped BigOperators

/-- The sine-vector amplitude for `N + 1` coordinates multiplied by the common complex phase
`exp (I * ψphase)`. -/
noncomputable def sourceFidelityAmplitude (N : ℕ) (ψphase : ℝ) (j : ℕ) : ℂ :=
  Complex.exp (Complex.I * (ψphase : ℂ)) * (sourceVarianceVector (N + 1) j : ℂ)

/-- The explicit sine amplitude with normalization `sqrt (2 / (N + 2))` equals the corresponding
entry of `sourceVarianceVector (N + 1)`. -/
theorem source_fidelity_modulus_eq (N j : ℕ) :
    Real.sqrt (2 / ((N + 2 : ℕ) : ℝ)) *
        Real.sin (((j : ℝ) + 1) * Real.pi / ((N + 2 : ℕ) : ℝ))
      = sourceVarianceVector (N + 1) j := by
  unfold sourceVarianceVector
  rw [show ((N + 1) + 1 : ℕ) = N + 2 by ring]

/-- For `N ≥ 1`, the squared-sine fidelity minimum equals `sourceVarianceCost (N + 1)`. See [van
Dam et al., 2007][VanDamEtAl2007]. -/
theorem source_fidelity_minimum (N : ℕ) (hN : 1 ≤ N) :
    Real.sin (Real.pi / (2 * ((N + 2 : ℕ) : ℝ))) ^ 2
      = sourceVarianceCost (N + 1) := by
  rw [source_variance_minimum_cost (N + 1) (by omega)]

/-- The sum of the adjacent correlations of the real sequences `p` and `q` over `N` adjacent
pairs. -/
noncomputable def sourceFidelityObjective (N : ℕ) (p q : ℕ → ℝ) : ℝ :=
  (∑ j ∈ Finset.range N, p j * p (j + 1))
    + (∑ j ∈ Finset.range N, q j * q (j + 1))

/-- For `N ≥ 1`, two real sequences with combined squared norm one on `N + 1` coordinates have
fidelity objective at most `cos (π / (N + 2))`. See [van Dam et al., 2007][VanDamEtAl2007]. -/
theorem source_fidelity_objective_le (N : ℕ) (hN : 1 ≤ N) (p q : ℕ → ℝ)
    (hnorm : (∑ j ∈ Finset.range (N + 1), (p j) ^ 2)
        + (∑ j ∈ Finset.range (N + 1), (q j) ^ 2) = 1) :
    sourceFidelityObjective N p q
      ≤ Real.cos (Real.pi / ((N + 2 : ℕ) : ℝ)) := by
  have hm : 0 < N + 1 := by omega
  have hp := path_shift_le (N + 1) hm p
  have hq := path_shift_le (N + 1) hm q
  have hcos : Real.cos (theta (N + 1))
      = Real.cos (Real.pi / ((N + 2 : ℕ) : ℝ)) := by
    unfold theta
    congr 1
    push_cast
    ring
  have hN1 : N + 1 - 1 = N := by omega
  rw [hcos, hN1] at hp hq
  have hsum := add_le_add hp hq
  have hfac : Real.cos (Real.pi / ((N + 2 : ℕ) : ℝ))
        * (∑ j ∈ Finset.range (N + 1), (p j) ^ 2)
      + Real.cos (Real.pi / ((N + 2 : ℕ) : ℝ))
        * (∑ j ∈ Finset.range (N + 1), (q j) ^ 2)
      = Real.cos (Real.pi / ((N + 2 : ℕ) : ℝ))
        * ((∑ j ∈ Finset.range (N + 1), (p j) ^ 2)
          + (∑ j ∈ Finset.range (N + 1), (q j) ^ 2)) := by ring
  rw [hfac, hnorm, mul_one] at hsum
  unfold sourceFidelityObjective
  linarith

/-- For `N ≥ 1`, the fidelity cost of two sequences with combined squared norm one is at least
`sin (π / (2 * (N + 2))) ^ 2`. See [van Dam et al., 2007][VanDamEtAl2007]. -/
theorem source_fidelity_cost_ge (N : ℕ) (hN : 1 ≤ N) (p q : ℕ → ℝ)
    (hnorm : (∑ j ∈ Finset.range (N + 1), (p j) ^ 2)
        + (∑ j ∈ Finset.range (N + 1), (q j) ^ 2) = 1) :
    Real.sin (Real.pi / (2 * ((N + 2 : ℕ) : ℝ))) ^ 2
      ≤ (1 - sourceFidelityObjective N p q) / 2 := by
  have hobj := source_fidelity_objective_le N hN p q hnorm
  have hsq : Real.sin (Real.pi / (2 * ((N + 2 : ℕ) : ℝ))) ^ 2
      = (1 - Real.cos (Real.pi / ((N + 2 : ℕ) : ℝ))) / 2 := by
    have h2 : (2 : ℝ) * (Real.pi / (2 * ((N + 2 : ℕ) : ℝ)))
        = Real.pi / ((N + 2 : ℕ) : ℝ) := by field_simp
    rw [Real.sin_sq_eq_half_sub, h2]
    ring
  rw [hsq]
  linarith

/-- For `N ≥ 1`, the sine vector and zero sequence attain fidelity objective `cos (π / (N +
2))`. See [van Dam et al., 2007][VanDamEtAl2007]. -/
theorem source_fidelity_objective_attained (N : ℕ) (hN : 1 ≤ N) :
    sourceFidelityObjective N (sourceVarianceVector (N + 1)) (fun _ => 0)
      = Real.cos (Real.pi / ((N + 2 : ℕ) : ℝ)) := by
  unfold sourceFidelityObjective
  have hq0 : (∑ j ∈ Finset.range N, (fun _ => (0 : ℝ)) j * (fun _ => (0 : ℝ)) (j + 1)) = 0 := by
    simp
  rw [hq0, add_zero]
  have hcorr := source_variance_adjacent_correlation (N + 1) (by omega)
  have harg : Real.pi / (((N + 1) + 1 : ℕ) : ℝ) = Real.pi / ((N + 2 : ℕ) : ℝ) := by
    congr 1
  rw [harg] at hcorr
  have hsplit := Finset.sum_range_succ
    (fun j => sourceVarianceVector (N + 1) j * sourceVarianceVector (N + 1) (j + 1)) N
  rw [hsplit] at hcorr
  have hz : sourceVarianceVector (N + 1) N * sourceVarianceVector (N + 1) (N + 1) = 0 := by
    rw [source_variance_vector_end (N + 1), mul_zero]
  rw [hz, add_zero] at hcorr
  exact hcorr

/-- For `N ≥ 1`, the sine vector and zero sequence attain fidelity cost `sin (π / (2 * (N + 2)))
^ 2`. See [van Dam et al., 2007][VanDamEtAl2007]. -/
theorem source_fidelity_cost_attained (N : ℕ) (hN : 1 ≤ N) :
    (1 - sourceFidelityObjective N (sourceVarianceVector (N + 1)) (fun _ => 0)) / 2
      = Real.sin (Real.pi / (2 * ((N + 2 : ℕ) : ℝ))) ^ 2 := by
  rw [source_fidelity_objective_attained N hN]
  have hsq : Real.sin (Real.pi / (2 * ((N + 2 : ℕ) : ℝ))) ^ 2
      = (1 - Real.cos (Real.pi / ((N + 2 : ℕ) : ℝ))) / 2 := by
    have h2 : (2 : ℝ) * (Real.pi / (2 * ((N + 2 : ℕ) : ℝ)))
        = Real.pi / ((N + 2 : ℕ) : ℝ) := by field_simp
    rw [Real.sin_sq_eq_half_sub, h2]
    ring
  rw [hsq]

/-- For `N ≥ 1`, the sine vector on `N + 1` coordinates together with a zero sequence has
combined squared norm one. -/
theorem source_fidelity_norm_attained (N : ℕ) (hN : 1 ≤ N) :
    (∑ j ∈ Finset.range (N + 1), (sourceVarianceVector (N + 1) j) ^ 2)
      + (∑ j ∈ Finset.range (N + 1), ((fun _ => (0 : ℝ)) j) ^ 2) = 1 := by
  have h := source_variance_vector_normalized (N + 1) (by omega)
  have hq0 : (∑ j ∈ Finset.range (N + 1), ((fun _ => (0 : ℝ)) j) ^ 2) = 0 := by simp
  rw [hq0, add_zero, h]

end Qatlib.Papers.PhaseEst07.MainResults.FidelityAppendix
