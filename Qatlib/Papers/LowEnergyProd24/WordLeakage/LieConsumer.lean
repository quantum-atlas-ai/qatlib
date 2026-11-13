/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.WordLeakage.ActualLeakage

/-!
# First-order Lie product-word leakage

This module defines `lieStages`, containing each group once with coefficient one, and verifies
first-order cancellation. It specializes the general leakage estimate to this Lie product word,
giving a concrete first-order instance of [HejaziZiniArrazola2024].

## Main statements

* `actual_lie_cancellation`: Verifies lower-order cancellation at order one.
* `actual_lie_product_leakage`: Bounds Lie-word leakage when `2 * J * k * d * M * s < 1`.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.WordLeakage
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Papers.LowEnergyProd24.ProductError
open Qatlib.Foundations.MatrixAlgebra.CommutatorExp
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {N R M k d : ℕ} {J : ℝ}
local instance : NormedAlgebra ℝ (Matrix (Register N) (Register N) ℂ) := .restrictScalars ℝ ℂ _

/-- The zeroth computed generator coefficient equals the sum of the stage generators. -/
theorem actual_zero_coefficient (h : Hamiltonian N R M k d J) (stages : List (ℝ × Fin M)) :
    computedCoefficient h stages 0=(stages.map (stageGenerator h)).sum := by
  induction stages with
  | nil => rfl
  | cons stage stages ih =>
    rw [computedCoefficient_cons]
    simpa only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one,
      one_div_one, adIter, one_smul, if_pos rfl, List.map_cons, List.sum_cons] using!
      congrArg (fun A => stageGenerator h stage+A) ih

/-- The stage list obtained by enumerating every group in `Fin M` once with coefficient one. -/
def lieStages (M : ℕ) : List (ℝ × Fin M) := Finset.univ.toList.map (fun m => (1,m))

/-- The absolute coefficient time budget of `lieStages M` is `M`. -/
theorem timeBudget_lieStages (M : ℕ) : timeBudget (lieStages M) = (M : ℝ) := by
  simp only [timeBudget, lieStages, List.map_map, Function.comp_def, abs_one]
  simpa only [Finset.toList_toFinset, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] using!
      (List.sum_toFinset (fun _ : Fin M => (1 : ℝ)) (Finset.nodup_toList Finset.univ)).symm

/-- The Lie stage list satisfies `lowerOrderCancellation` at order one. -/
theorem actual_lie_cancellation (h : Hamiltonian N R M k d J) : lowerOrderCancellation h (lieStages M) 1 := by
  intro n hn
  have hn0 : n=0 := by omega
  subst n
  rw [actual_zero_coefficient]
  simp only [lieStages, List.map_map, Function.comp_def]
  have he : ((Finset.univ.toList : List (Fin M)).map (fun m => stageGenerator h (1,m))).sum =
      ∑ m : Fin M, stageGenerator h (1,m) := by
    simpa only [Finset.toList_toFinset] using!
      (List.sum_toFinset (fun m : Fin M => stageGenerator h (1,m)) (Finset.nodup_toList Finset.univ)).symm
  rw [he]
  simp only [stageGenerator, totalGenerator]
  rw [← Finset.smul_sum]
  rfl

/-- For a nonnegative step satisfying `2 * J * k * d * M * s < 1`, the Lie word satisfies the
exponential energy-gap leakage bound with the order-one step exponent. -/
theorem actual_lie_product_leakage (h : Hamiltonian N R M k d J)
    (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d) (L : ℕ)
    (hL : ∀ m, (h.labels m).card ≤ L) (s : ℝ) (hs : 0 ≤ s)
    (hsmall : 2*J*k*d*(M : ℝ)*s < 1) (Δ Λ : ℝ) :
    ‖high h.total h.total_hermitian Λ*approximate h (lieStages M) s*low h.total h.total_hermitian Δ‖ ≤
      Real.exp (-(1/(2*J*k*d))*(Λ-Δ)+stepExponent L k d J (lieStages M) 1 s) :=
  actual_product_word_leakage h hJ hk hd L hL (lieStages M) 1 (by norm_num)
    (actual_lie_cancellation h) s hs (by simpa only [timeBudget_lieStages] using! hsmall) Δ Λ
end Qatlib.Papers.LowEnergyProd24.WordLeakage
