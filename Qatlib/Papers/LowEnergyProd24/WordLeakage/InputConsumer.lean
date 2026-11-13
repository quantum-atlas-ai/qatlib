/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.CenterChoice
import Qatlib.Papers.LowEnergyProd24.WordLeakage.PhysicalConsumer
import Qatlib.Papers.LowEnergyProd24.RetainedError.PhysicalPositive
import Qatlib.Papers.LowEnergyProd24.RetainedBound.PhysicalCalculus

/-!
# Low-energy estimates from local Hamiltonian data

This module constructs `productWord` directly from `LocalData` and uses `maxGroupSize` and the
optimal interaction strength to instantiate leakage estimates. It also exposes tolerance,
positive-group cutoff, repeated-step, and state-tail results for the original input Hamiltonian
in [HejaziZiniArrazola2024].

## Main statements

* `actual_source_leakage`: Applies the source majorant to the original input word.
* `actual_input_state_tail`: Bounds repeated state error using the input high-energy tail.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.WordLeakage.Input
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Papers.LowEnergyProd24.CenterChoice
open Qatlib.Foundations.MatrixAlgebra.CommutatorExp
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {N R M k d : ℕ}
local instance : NormedAlgebra ℝ (Matrix (Register N) (Register N) ℂ) := .restrictScalars ℝ ℂ _

/-- The maximum number of interaction labels in any Hamiltonian group, expressed as the finite
supremum of the group cardinalities. -/
def maxGroupSize (h : LocalData N R M k d) : ℕ := Finset.univ.sup (fun m => (h.labels m).card)

/-- Each group contains at most `maxGroupSize h` interaction labels. -/
theorem labels_le_max (h : LocalData N R M k d) (m : Fin M) : (h.labels m).card ≤ maxGroupSize h :=
  Finset.le_sup (f := fun m => (h.labels m).card) (Finset.mem_univ m)

/-- The product exponential word formed from the original grouped local data with stage
generator `(-stage.1 * Complex.I) • h.grouped stage.2`. -/
def productWord (h : LocalData N R M k d) (stages : List (ℝ × Fin M)) (t : ℝ) :=
  word (stages.map (fun stage => ((-stage.1 : ℂ)*Complex.I) • h.grouped stage.2)) t

/-- The word constructed directly from local data equals the word of the associated physical
model. -/
theorem productWord_eq_model (h : LocalData N R M k d) (stages : List (ℝ × Fin M)) (t : ℝ) :
    productWord h stages t=CenterTransport.approximate (physicalModel h) stages t := rfl

/-- With the optimal interaction strength, lower-order cancellation, and the source small-step
condition, input-word leakage is bounded by energy-gap exponential decay multiplied by the
exponential of `sourceStepExponent` [HejaziZiniArrazola2024]. -/
theorem actual_source_leakage (h : LocalData N R M k d)
    (hJ : 0 < optimalStrength h) (hk : 0 < k) (hd : 0 < d)
    (stages : List (ℝ × Fin M)) (p : ℕ) (hp : 0 < p)
    (horder : CenterTransport.lowerOrderCancellation (physicalModel h) stages p)
    (s : ℝ) (hs : 0 ≤ s) (hsmall : sourceRate k d (optimalStrength h) stages*s < 1) (Δ Λ : ℝ) :
    ‖high h.total (original_total_hermitian h) Λ*productWord h stages s*low h.total (original_total_hermitian h) Δ‖ ≤
      Real.exp (-(1/(2*optimalStrength h*k*d))*(Λ-Δ)+sourceStepExponent (maxGroupSize h) k d (optimalStrength h) stages p s) :=
  Physical.source_majorant (physicalModel h) hJ hk hd (maxGroupSize h) (labels_le_max h)
    stages p hp horder s hs hsmall Δ Λ

/-- Under the Lie small-step condition, the first-order Lie word from local data satisfies the
exponential leakage bound with order-one `stepExponent` [HejaziZiniArrazola2024]. -/
theorem actual_lie_input_leakage (h : LocalData N R M k d)
    (hJ : 0 < optimalStrength h) (hk : 0 < k) (hd : 0 < d)
    (s : ℝ) (hs : 0 ≤ s) (hsmall : 2*optimalStrength h*k*d*(M : ℝ)*s < 1) (Δ Λ : ℝ) :
    ‖high h.total (original_total_hermitian h) Λ*productWord h (lieStages M) s*low h.total (original_total_hermitian h) Δ‖ ≤
      Real.exp (-(1/(2*optimalStrength h*k*d))*(Λ-Δ)+stepExponent (maxGroupSize h) k d (optimalStrength h) (lieStages M) 1 s) :=
  Physical.lie_product_leakage (physicalModel h) hJ hk hd (maxGroupSize h) (labels_le_max h) s hs hsmall Δ Λ

/-- For any positive `θ`, the explicit `toleranceCutoff` bounds input-word leakage by `θ` under
the cancellation and small-step hypotheses [HejaziZiniArrazola2024]. -/
theorem actual_input_tolerance (h : LocalData N R M k d)
    (hJ : 0 < optimalStrength h) (hk : 0 < k) (hd : 0 < d)
    (stages : List (ℝ × Fin M)) (p : ℕ) (hp : 0 < p)
    (horder : CenterTransport.lowerOrderCancellation (physicalModel h) stages p)
    (s : ℝ) (hs : 0 ≤ s) (hsmall : 2*optimalStrength h*k*d*ProductError.timeBudget stages*s < 1)
    (Δ θ : ℝ) (hθ : 0 < θ) :
    ‖high h.total (original_total_hermitian h)
        (toleranceCutoff (maxGroupSize h) k d (optimalStrength h) stages p s Δ θ)*
      productWord h stages s*low h.total (original_total_hermitian h) Δ‖ ≤ θ :=
  Physical.tolerance_cutoff (physicalModel h) hJ hk hd (maxGroupSize h) (labels_le_max h)
    stages p hp horder s hs hsmall Δ θ hθ

/-- For positive semidefinite input groups and any positive tolerance, there exists a positive
cutoff gap giving the enlarged-cutoff leading bound plus that tolerance for the compressed
nested commutator. -/
theorem actual_input_psd_cutoffs (h : LocalData N R M k d)
    (hp : ∀ m, (h.grouped m).PosSemidef) (hJ : 0 < optimalStrength h) (hk : 0 < k) (hd : 0 < d)
    (seed : Fin M) (xs : List (Fin M)) (Δ θ : ℝ) (hΔ : 0 ≤ Δ) (hθ : 0 < θ) :
    ∃ gap : ℝ, 0 < gap ∧
      ‖low h.total (original_total_hermitian h) Δ*RetainedError.Physical.nested (physicalModel h) seed xs*
        low h.total (original_total_hermitian h) Δ‖ ≤ 2^xs.length*(Δ+xs.length*gap)^(xs.length+1)+θ :=
  RetainedError.Physical.tolerance_cutoffs (physicalModel h) hp hJ hk hd (maxGroupSize h) (labels_le_max h) seed xs Δ θ hΔ hθ

/-- The input-word error after `r` powers on the low-energy input sector is at most `r` times
the corresponding one-step error [HejaziZiniArrazola2024]. -/
theorem actual_input_repeated_error (h : LocalData N R M k d) (stages : List (ℝ × Fin M)) (t Δ : ℝ) (r : ℕ) :
    ‖(productWord h stages t^r-evolve h.total t^r)*low h.total (original_total_hermitian h) Δ‖ ≤
      (r : ℝ)*‖(productWord h stages t-evolve h.total t)*low h.total (original_total_hermitian h) Δ‖ :=
  RetainedBound.Physical.repeated_error (physicalModel h) stages t Δ r

/-- For a unit input state, the error after `r` powers is bounded by `r` times the one-step
low-energy operator error plus twice the norm of the state's high-energy component
[HejaziZiniArrazola2024]. -/
theorem actual_input_state_tail (h : LocalData N R M k d) (stages : List (ℝ × Fin M))
    (t Δ : ℝ) (r : ℕ) (ψ : EuclideanSpace ℂ (Register N)) (hψ : ‖ψ‖=1) :
    ‖(Matrix.toEuclideanCLM (n := Register N) (𝕜 := ℂ)) (productWord h stages t^r-evolve h.total t^r) ψ‖ ≤
      (r : ℝ)*‖(productWord h stages t-evolve h.total t)*low h.total (original_total_hermitian h) Δ‖+
      2*‖(Matrix.toEuclideanCLM (n := Register N) (𝕜 := ℂ)) (high h.total (original_total_hermitian h) Δ) ψ‖ :=
  RetainedBound.Physical.state_tail (physicalModel h) stages t Δ r ψ hψ
end Qatlib.Papers.LowEnergyProd24.WordLeakage.Input
