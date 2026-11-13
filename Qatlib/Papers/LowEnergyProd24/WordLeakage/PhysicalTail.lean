/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.CenterTransport.PhysicalCoefficients
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Weighted defect tails for physical Hamiltonians

This module defines the original physical generator defect and sums its weighted coefficient
tail after lower-order cancellation. It bounds the weighted norm by a geometric majorant,
transporting the defect-tail estimates used in [HejaziZiniArrazola2024].

## Main statements

* `actual_defect_tail`: Sums the physical coefficient series starting at the cancellation order.
* `actual_defect_bound`: Bounds the weighted physical defect by the geometric tail expression.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.WordLeakage.Physical
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Papers.LowEnergyProd24.ProductError
open Qatlib.Papers.LowEnergyProd24.CenterTransport
open Qatlib.Foundations.MatrixAlgebra.CommutatorExp
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {N R M k d : ℕ} {J : ℝ}
local instance : NormedAlgebra ℝ (Matrix (Register N) (Register N) ℂ) := .restrictScalars ℝ ℂ _

/-- The instantaneous generator of the original physical product word minus the original total
generator. -/
def defect (h : PhysicalHamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :=
  generator (stages.map (stageGenerator h)) t-totalGenerator h

/-- For positive cancellation order `p`, the series of weighted physical coefficients with
powers `t ^ (n + p)` sums to the weighted physical defect. -/
theorem actual_defect_tail (h : PhysicalHamiltonian N R M k d J) (stages : List (ℝ × Fin M))
    (p : ℕ) (hp : 0 < p) (horder : lowerOrderCancellation h stages p) (lam t : ℝ) :
    HasSum (fun n : ℕ => t^(n+p) • weighted h.total (physicalCoefficient h stages (n+p)) lam)
      (weighted h.total (defect h stages t) lam) := by
  have hzero : physicalCoefficient h stages 0=totalGenerator h := by
    simpa only [if_pos rfl] using! horder 0 hp
  have hprefix : (∑ n ∈ Finset.range p, t^n • weighted h.total (physicalCoefficient h stages n) lam) =
      weighted h.total (totalGenerator h) lam := by
    rw [Finset.sum_eq_single 0]
    · rw [hzero]
      simp only [pow_zero, one_smul]
    · intro n hn hnzero
      have hc := horder n (Finset.mem_range.mp hn)
      rw [if_neg hnzero] at hc
      simp only [hc, weighted, mul_zero, zero_mul, smul_zero]
    · intro hn
      exact (hn (Finset.mem_range.mpr hp)).elim
  have hs := (hasSum_nat_add_iff' p).mpr (physical_weighted_generator_hasSum h stages lam t)
  rw [hprefix] at hs
  have he : weighted h.total (defect h stages t) lam =
      weighted h.total (generator (stages.map (stageGenerator h)) t) lam-
        weighted h.total (totalGenerator h) lam := by
    simp only [weighted, defect, mul_sub, sub_mul]
  rw [he]
  exact hs

/-- Under physical locality and lower-order cancellation, the weighted defect norm is bounded by
the explicit geometric tail with ratio `2 * J * k * d * timeBudget stages * t < 1`
[HejaziZiniArrazola2024]. -/
theorem actual_defect_bound (h : PhysicalHamiltonian N R M k d J)
    (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d) (L : ℕ)
    (hL : ∀ m, (h.labels m).card ≤ L) (stages : List (ℝ × Fin M))
    (p : ℕ) (hp : 0 < p) (horder : lowerOrderCancellation h stages p)
    (t : ℝ) (ht : 0 ≤ t) (hsmall : 2*J*k*d*timeBudget stages*t < 1) :
    ‖weighted h.total (defect h stages t) (1/(2*J*k*d))‖ ≤
      ((L : ℝ)*(2*J)*timeBudget stages)*(2*J*k*d*timeBudget stages*t)^p /
        (1-2*J*k*d*timeBudget stages*t) := by
  let D : ℝ := (L : ℝ)*(2*J)*timeBudget stages
  let C : ℝ := 2*J*k*d*timeBudget stages
  let x : ℝ := C*t
  have hA := timeBudget_nonneg stages
  have hx : 0 ≤ x := by dsimp [x, C]; positivity
  have hxnorm : ‖x‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hx]; exact hsmall
  have hm : HasSum (fun n : ℕ => (D*x^p)*x^n) ((D*x^p)/(1-x)) := by
    convert! (hasSum_geometric_of_norm_lt_one hxnorm).mul_left (D*x^p) using 1
  have hs := actual_defect_tail h stages p hp horder (1/(2*J*k*d)) t
  apply HasSum.norm_le_of_bounded hs hm
  intro n
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht _)]
  calc
    _ ≤ t^(n+p)*((L : ℝ)*(2*J)*timeBudget stages*(2*J*k*d*timeBudget stages)^(n+p)) :=
      mul_le_mul_of_nonneg_left (physical_coefficient_weighted_bound h hJ hk hd L hL stages (n+p) (by omega)) (pow_nonneg ht _)
    _ = _ := by
      dsimp only [D, x, C]
      rw [mul_pow, pow_add, pow_add]
      ring
end Qatlib.Papers.LowEnergyProd24.WordLeakage.Physical
