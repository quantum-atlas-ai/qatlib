/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FermLinOpt04.MainResults.Model.GaussianMap
import Mathlib.Tactic
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.FermionExt

/-!
# Gaussian correlation-update identities

This module proves equality of the two rational matrix expressions `corrUpdate` and
`corrUpdate'` under determinant hypotheses and simplifies the update when `D = 0`. It also
expresses the covariance of a projected operator through a weighted measurement update under the
specified hypothesis away from the measured mode. These results formalize the indicated
identities from [Bravyi2005Fermionic].

## Main statements

* `corrUpdate_inverse_form`: equates the two matrix-inverse forms.
* `corrUpdate_zero_D`: simplifies the update to `B * M * Bᵀ + A`.
* `measurement_correlation_update`: gives the conditional covariance identity.

## References

* [Bravyi, 2005][Bravyi2005Fermionic]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Concepts.FermionAlgebra.CarJordanWigner
open Qatlib.Concepts.MpsAdaptation.MpsTransfer.FermionExt
open Qatlib.Papers.FermLinOpt04.MainResults.Model

namespace Qatlib.Papers.FermLinOpt04.MainResults.Claims

/-- Under nonvanishing determinant hypotheses for `M`, `M⁻¹ + D`, and `1 + M * D`, the two
correlation-update expressions agree. These are the inverse forms of the update formula in
[Bravyi2005Fermionic]. -/
theorem corrUpdate_inverse_form {n : ℕ}
    (A B D M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (hM : M.det ≠ 0) (hMD : (M⁻¹ + D).det ≠ 0) (hI : (1 + M * D).det ≠ 0) :
    corrUpdate A B D M = corrUpdate' A B D M := by
  have huM : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  have hstep : M⁻¹ + D = M⁻¹ * (1 + M * D) := by
    rw [Matrix.mul_add, Matrix.mul_one,
      Matrix.nonsing_inv_mul_cancel_left (A := M) D huM]
  have hinv : (M⁻¹ + D)⁻¹ = (1 + M * D)⁻¹ * M := by
    rw [hstep, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv M huM]
  unfold corrUpdate corrUpdate'
  rw [hinv]
  noncomm_ring

/-- For invertible `M` and `D = 0`, the correlation update is `B * M * Bᵀ + A`. -/
theorem corrUpdate_zero_D {n : ℕ} (A B M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ)
    (hM : M.det ≠ 0) :
    corrUpdate A B (0 : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) M = B * M * Bᵀ + A := by
  have huM : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  unfold corrUpdate
  rw [add_zero, Matrix.nonsing_inv_nonsing_inv M huM]

/-- Under the specified covariance relation away from the measured mode, the covariance of the
projected operator equals its Born weight times `measurementUpdate`. -/
theorem measurement_correlation_update {n : ℕ} (M : Fock n)
    (k : Fin n) (b : Bool)
    (hAway : ∀ a c : Fin (2 * n), ¬ isModeMajorana k a → ¬ isModeMajorana k c →
      covarianceMatrix (measurementProjector k b * M) a c
        = bornWeight M k b * covarianceMatrix M a c) :
    covarianceMatrix (measurementProjector k b * M)
      = bornWeight M k b • measurementUpdate (covarianceMatrix M) k b :=
  covarianceMatrix_measurement_eq_update M k b hAway

end Qatlib.Papers.FermLinOpt04.MainResults.Claims
