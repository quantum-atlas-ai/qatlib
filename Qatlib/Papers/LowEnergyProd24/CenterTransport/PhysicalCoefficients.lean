/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.CenterTransport.PhysicalWeights
import Qatlib.Foundations.MatrixAlgebra.CommutatorExp.Centering

/-!
# Centered bounds for physical generator coefficients

Positive-degree coefficients of the physical product generator agree with those computed from
centered interactions. The module transfers weighted coefficient bounds to the physical
Hamiltonian and proves `physical_weighted_generator_hasSum` for the weighted generator series.
See [HejaziZiniArrazola2024].

## Main statements

* `physical_positive_coefficient`: For positive degree, the physical generator coefficient
  equals the coefficient computed from the normalized centered Hamiltonian.
* `physical_coefficient_weighted_bound`: For positive degree `n` and positive `J`, `k`, and `d`,
  the weighted physical coefficient is bounded by `L * (2 * J) * timeBudget stages` times `(2 *
  J * k * d * timeBudget stages)^n`, assuming every group has at most `L` labels.
* `physical_weighted_generator_hasSum`: The series of weighted physical coefficients multiplied
  by `t^n` sums to the weighted physical product generator.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.CenterTransport
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Foundations.MatrixAlgebra.CommutatorExp
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {N R M k d : ℕ} {J : ℝ}
local instance : NormedAlgebra ℝ (Matrix (Register N) (Register N) ℂ) := .restrictScalars ℝ ℂ _

/-- For positive degree, the physical generator coefficient equals the coefficient computed from
the normalized centered Hamiltonian. See [HejaziZiniArrazola2024]. -/
theorem physical_positive_coefficient (h : PhysicalHamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (n : ℕ) (hn : 0 < n) :
    physicalCoefficient h stages n=ProductError.computedCoefficient h.normalized stages n := by
  have hs :=
      generatorCoefficient_central_shift (stagePairs h stages) (stagePairs_central h stages) n
  rw [stagePairs_physical] at hs
  simp only [if_neg hn.ne', add_zero, stagePairs, List.map_map, Function.comp_def] at hs
  rw [ProductError.computedCoefficient_eq_actual]
  exact hs

/-- Imaginary-time weighting of any matrix is unchanged when the total physical Hamiltonian is
replaced by its centered total. -/
theorem physical_weight_centered (h : PhysicalHamiltonian N R M k d J)
    (A : Matrix (Register N) (Register N) ℂ) (lam : ℝ) :
    weighted h.total A lam=weighted h.normalized.total A lam := by
  have hz : Central ((h.totalCenter : ℂ) • (1 : Matrix (Register N) (Register N) ℂ)) :=
    scalar_identity_central _
  have hs := conjugation_add_central h.normalized.total A ((h.totalCenter : ℂ) • 1) hz lam
  have he (t : ℝ) (B : Matrix (Register N) (Register N) ℂ) : t • B=(t : ℂ) • B := by
    ext i j
    exact Complex.real_smul
  simpa only [he, Complex.ofReal_neg, ← physical_total_centered h, weighted] using hs

/-- For positive degree `n` and positive `J`, `k`, and `d`, the weighted physical coefficient is
bounded by `L * (2 * J) * timeBudget stages` times `(2 * J * k * d * timeBudget stages)^n`,
assuming every group has at most `L` labels. -/
theorem physical_coefficient_weighted_bound (h : PhysicalHamiltonian N R M k d J)
    (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d) (L : ℕ)
    (hL : ∀ m, (h.labels m).card ≤ L) (stages : List (ℝ × Fin M)) (n : ℕ) (hn : 0 < n) :
    ‖weighted h.total (physicalCoefficient h stages n) (1/(2*J*k*d))‖ ≤
      ((L : ℝ)*(2*J)*ProductError.timeBudget stages)*(2*J*k*d*ProductError.timeBudget stages)^n := by
  rw [physical_positive_coefficient h stages n hn, physical_weight_centered]
  exact ProductError.actual_coefficient_weighted_bound h.normalized hJ hk hd L hL stages n

/-- The series of weighted physical coefficients multiplied by `t^n` sums to the weighted
physical product generator. -/
theorem physical_weighted_generator_hasSum (h : PhysicalHamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (lam t : ℝ) :
    HasSum (fun n : ℕ => t^n • weighted h.total (physicalCoefficient h stages n) lam)
      (weighted h.total (generator (stages.map (stageGenerator h)) t) lam) := by
  have hs := (weightMap h lam).hasSum (physical_generator_hasSum h stages t)
  simpa only [map_smul, weightMap_apply] using hs
end Qatlib.Papers.LowEnergyProd24.CenterTransport
