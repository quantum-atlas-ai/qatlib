/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ImaginaryFlow.LeastSquares.ComplexAnsatz
import Qatlib.Papers.TranscorrChem20.MainResults.ImaginaryTime.MatrixEvolution

/-!
# McLachlan equations for a complex transcorrelated ansatz

This module specializes real-parameter least squares to a normalized complex state ansatz driven
by `tc H g`. It identifies the tangent orthogonality, the equivalence between global cost
minimization and the real normal equation, and the inverse-metric parameter update when the
metric is invertible. See [McArdleTew2020].

## Main statements

* `tc_ansatz_minimum_iff_normal_equation`: Characterization of global McLachlan minimizers.
* `tc_complex_ansatz_minimizer`: An inverse-metric minimizer under metric invertibility.
* `tc_euler_step`: Algebraic Euler parameter update.

## References

* [McArdle and Tew, 2020][McArdleTew2020]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.ImaginaryFlow.LeastSquares
open Qatlib.Papers.TranscorrChem20.MainResults.ImaginaryTime

namespace Qatlib.Papers.TranscorrChem20.MainResults.McLachlan

section
variable {d n : ℕ}
local instance : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin d)) :=
  InnerProductSpace.rclikeToReal ℂ (EuclideanSpace ℂ (Fin d))

/-- Each coordinate tangent of a differentiable normalized complex ansatz has zero real inner
product with the state. -/
theorem actual_ansatz_tangents (Φ : (Fin n → ℝ) → State d) (θ : Fin n → ℝ)
    (D : (Fin n → ℝ) →L[ℝ] State d) (hD : HasFDerivAt Φ D θ)
    (hnorm : ∀ x, ‖Φ x‖ = 1) (i : Fin n) :
    (inner ℂ (D (Pi.single i 1)) (Φ θ)).re = 0 :=
  normalized_ansatz_tangent Φ θ D hD hnorm (Pi.single i 1)

/-- For a differentiable normalized ansatz, a real parameter rate globally minimizes the
transcorrelated McLachlan cost exactly when it solves the metric normal equation. See
[McArdleTew2020]. -/
theorem tc_ansatz_minimum_iff_normal_equation (H g : Op d)
    (Φ : (Fin n → ℝ) → State d) (θ : Fin n → ℝ)
    (D : (Fin n → ℝ) →L[ℝ] State d) (hD : HasFDerivAt Φ D θ)
    (hnorm : ∀ x, ‖Φ x‖ = 1) (v : Fin n → ℝ) :
    let tangents := fun i : Fin n => D (Pi.single i 1)
    let Htc := Matrix.toEuclideanLin (tc H g)
    (∀ x, mclachlanCost tangents
      (Htc (Φ θ) - (inner ℂ (Φ θ) (Htc (Φ θ))).re • Φ θ) v ≤
      mclachlanCost tangents
        (Htc (Φ θ) - (inner ℂ (Φ θ) (Htc (Φ θ))).re • Φ θ) x) ↔
      (metricMatrix tangents).mulVec v =
        -gradientVector tangents (Htc.restrictScalars ℝ) (Φ θ) := by
  let tangents := fun i : Fin n => D (Pi.single i 1)
  let Htc := Matrix.toEuclideanLin (tc H g)
  let w := Htc (Φ θ) - (inner ℂ (Φ θ) (Htc (Φ θ))).re • Φ θ
  exact (stationary_iff_global_min tangents w v).symm.trans
    (stationary_iff_normal_equation tangents (Htc.restrictScalars ℝ) (Φ θ)
      (normalized_coordinate_tangents Φ θ D hD hnorm) v)

/-- For a differentiable normalized ansatz with invertible metric matrix, the metric is positive
semidefinite and `inverseRate` globally minimizes the McLachlan cost. See [McArdleTew2020]. -/
theorem tc_complex_ansatz_minimizer (H g : Op d) (Φ : (Fin n → ℝ) → State d)
    (θ : Fin n → ℝ) (D : (Fin n → ℝ) →L[ℝ] State d) (hD : HasFDerivAt Φ D θ)
    (hnorm : ∀ x, ‖Φ x‖ = 1)
    [Invertible (metricMatrix (fun i : Fin n => D (Pi.single i 1)))] :
    let tangents := fun i : Fin n => D (Pi.single i 1)
    let Htc := Matrix.toEuclideanLin (tc H g)
    (metricMatrix tangents).PosSemidef ∧
      ∀ v, mclachlanCost tangents
        (Htc (Φ θ) - (inner ℂ (Φ θ) (Htc (Φ θ))).re • Φ θ)
        (inverseRate tangents (Htc.restrictScalars ℝ) (Φ θ)) ≤
      mclachlanCost tangents (Htc (Φ θ) - (inner ℂ (Φ θ) (Htc (Φ θ))).re • Φ θ) v :=
  complex_ansatz_inverse_minimizer Φ θ D hD hnorm (Matrix.toEuclideanLin (tc H g))

/-- The Euler update using `inverseRate` equals subtraction of the step size times the inverse
metric applied to the gradient vector. See [McArdleTew2020]. -/
theorem tc_euler_step (H g : Op d) (Φ : (Fin n → ℝ) → State d) (θ : Fin n → ℝ)
    (D : (Fin n → ℝ) →L[ℝ] State d) (δ : ℝ) :
    let tangents := fun i : Fin n => D (Pi.single i 1)
    let Htc := (Matrix.toEuclideanLin (tc H g)).restrictScalars ℝ
    θ + δ • inverseRate tangents Htc (Φ θ) =
      θ - δ • ((metricMatrix tangents)⁻¹.mulVec (gradientVector tangents Htc (Φ θ))) :=
  euler_update _ _ _ θ δ

end
end Qatlib.Papers.TranscorrChem20.MainResults.McLachlan
