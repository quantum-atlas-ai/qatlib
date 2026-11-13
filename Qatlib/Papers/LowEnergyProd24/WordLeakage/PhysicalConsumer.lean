/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.WordLeakage.PhysicalLeakage
import Qatlib.Papers.LowEnergyProd24.WordLeakage.Majorant
import Qatlib.Papers.LowEnergyProd24.WordLeakage.ToleranceCutoff
import Qatlib.Papers.LowEnergyProd24.WordLeakage.LieConsumer

/-!
# Physical leakage bounds and explicit consumers

This module applies the source majorant, explicit tolerance cutoff, and Lie-word leakage results
to a `PhysicalHamiltonian`. The bounds use the original total Hamiltonian and original product
word, transporting the centered analysis of [HejaziZiniArrazola2024].

## Main statements

* `source_majorant`: Bounds physical product-word leakage by the source exponent.
* `tolerance_cutoff`: Makes physical leakage at most a prescribed positive tolerance.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.WordLeakage.Physical
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Papers.LowEnergyProd24.CenterTransport
open Qatlib.Foundations.MatrixAlgebra.CommutatorExp
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {N R M k d : ℕ} {J : ℝ}
local instance : NormedAlgebra ℝ (Matrix (Register N) (Register N) ℂ) := .restrictScalars ℝ ℂ _

/-- Under the physical locality, cancellation, and source small-step hypotheses, original
product-word leakage is bounded by energy-gap exponential decay with `sourceStepExponent`
[HejaziZiniArrazola2024]. -/
theorem source_majorant (h : PhysicalHamiltonian N R M k d J)
    (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d) (L : ℕ)
    (hL : ∀ m, (h.labels m).card ≤ L) (stages : List (ℝ × Fin M))
    (p : ℕ) (hp : 0 < p) (horder : lowerOrderCancellation h stages p)
    (s : ℝ) (hs : 0 ≤ s) (hsmall : sourceRate k d J stages*s < 1) (Δ Λ : ℝ) :
    ‖high h.total h.total_hermitian Λ*approximate h stages s*low h.total h.total_hermitian Δ‖ ≤
      Real.exp (-(1/(2*J*k*d))*(Λ-Δ)+sourceStepExponent L k d J stages p s) := by
  have hsmall' :=
      (mul_le_mul_of_nonneg_right (actual_rate_le_source k d J hJ.le stages) hs).trans_lt hsmall
  exact (actual_product_leakage h hJ hk hd L hL stages p hp horder s hs hsmall' Δ Λ).trans
    (Real.exp_le_exp.mpr (add_le_add le_rfl (actual_exponent_le_source L k d J hJ.le stages p s hs hsmall)))

/-- For any positive `θ`, physical product-word leakage above the explicit `toleranceCutoff` is
at most `θ` under the cancellation and small-step hypotheses. -/
theorem tolerance_cutoff (h : PhysicalHamiltonian N R M k d J)
    (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d) (L : ℕ)
    (hL : ∀ m, (h.labels m).card ≤ L) (stages : List (ℝ × Fin M))
    (p : ℕ) (hp : 0 < p) (horder : lowerOrderCancellation h stages p)
    (s : ℝ) (hs : 0 ≤ s) (hsmall : 2*J*k*d*ProductError.timeBudget stages*s < 1)
    (Δ θ : ℝ) (hθ : 0 < θ) :
    ‖high h.total h.total_hermitian (toleranceCutoff L k d J stages p s Δ θ)*
      approximate h stages s*low h.total h.total_hermitian Δ‖ ≤ θ := by
  have hn : (2*J*k*d : ℝ) ≠ 0 := by positivity
  have he : -(1/(2*J*k*d))*(toleranceCutoff L k d J stages p s Δ θ-Δ)+
      stepExponent L k d J stages p s=Real.log θ := by
    unfold toleranceCutoff
    field_simp
    ring
  simpa only [he, Real.exp_log hθ] using
    actual_product_leakage h hJ hk hd L hL stages p hp horder s hs hsmall Δ
      (toleranceCutoff L k d J stages p s Δ θ)

/-- The original physical Lie word satisfies lower-order cancellation at order one. -/
theorem lie_cancellation (h : PhysicalHamiltonian N R M k d J) : lowerOrderCancellation h (lieStages M) 1 := by
  intro n hn
  have hn0 : n=0 := by omega
  subst n
  change generatorCoefficient ((lieStages M).map (stageGenerator h)) 0=totalGenerator h
  rw [generatorCoefficient_zero]
  simp only [lieStages, List.map_map, Function.comp_def]
  have he : ((Finset.univ.toList : List (Fin M)).map (fun m => stageGenerator h (1,m))).sum =
      ∑ m : Fin M, stageGenerator h (1,m) := by
    simpa only [Finset.toList_toFinset] using
      (List.sum_toFinset (fun m : Fin M => stageGenerator h (1,m)) (Finset.nodup_toList Finset.univ)).symm
  rw [he]
  simp only [stageGenerator, totalGenerator]
  rw [← Finset.smul_sum]
  rfl

/-- The original physical Lie word satisfies the order-one exponential leakage bound for
nonnegative steps with `2 * J * k * d * M * s < 1`. -/
theorem lie_product_leakage (h : PhysicalHamiltonian N R M k d J)
    (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d) (L : ℕ)
    (hL : ∀ m, (h.labels m).card ≤ L) (s : ℝ) (hs : 0 ≤ s)
    (hsmall : 2*J*k*d*(M : ℝ)*s < 1) (Δ Λ : ℝ) :
    ‖high h.total h.total_hermitian Λ*approximate h (lieStages M) s*low h.total h.total_hermitian Δ‖ ≤
      Real.exp (-(1/(2*J*k*d))*(Λ-Δ)+stepExponent L k d J (lieStages M) 1 s) :=
  actual_product_leakage h hJ hk hd L hL (lieStages M) 1 (by norm_num)
    (lie_cancellation h) s hs (by simpa only [timeBudget_lieStages] using hsmall) Δ Λ
end Qatlib.Papers.LowEnergyProd24.WordLeakage.Physical
