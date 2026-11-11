/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.TangentProject.Projection
import Qatlib.Foundations.MatrixGeometry.TangentProject.AmbientGradient

/-!
# Real derivatives of matrix energy expectations

Defines the real energy `energy O ψ U = Re Tr(O U ψ Uᴴ)` and computes its Fréchet derivative
using the conjugation derivative. For Hermitian `O` and `ψ`, `energy_fderiv_frobenius`
identifies the derivative with the real Frobenius pairing against `2 • (O * U * ψ)`. See
[HunzikerEtAl2003] for related background.

## Main statements

* `energy_hasFDerivAt`: The energy function has real Fréchet derivative `energyDerivative O ψ U`
  at `U`.
* `energy_fderiv_frobenius`: For Hermitian `O` and `ψ`, the energy derivative on `V` equals the
  real Frobenius pairing of `2 • (O * U * ψ)` with `V`.

## References

* [Hunziker et al., 2003][HunzikerEtAl2003]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace Qatlib.Foundations.MatrixGeometry.TangentProject
variable {n : Type*} [Fintype n] [DecidableEq n]
local instance : NormedAlgebra ℝ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℝ ℂ _

/-- The real trace expectation `Re Tr(O * U * ψ * Uᴴ)`. -/
def energy (O ψ U : Matrix n n ℂ) : ℝ := (O * stateMap ψ U).trace.re

/-- The matrix trace viewed as a real continuous linear map to the complex numbers. -/
def traceCLM : Matrix n n ℂ →L[ℝ] ℂ :=
  (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap

/-- The real continuous linear map taking a variation to the real trace of `O` times the
corresponding variation of `stateMap`. -/
def energyDerivative (O ψ U : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp (traceCLM.comp
    ((ContinuousLinearMap.mul ℝ (Matrix n n ℂ) O).comp (stateDerivative ψ U)))

/-- The energy function has real Fréchet derivative `energyDerivative O ψ U` at `U`. -/
theorem energy_hasFDerivAt (O ψ U : Matrix n n ℂ) :
    HasFDerivAt (energy O ψ) (energyDerivative O ψ U) U := by
  have h := Complex.reCLM.hasFDerivAt.comp U
    ((traceCLM (n := n)).hasFDerivAt.comp U ((stateMap_hasFDerivAt ψ U).const_mul O))
  convert! h using 1

/-- The energy derivative on a variation `V` is `Re Tr(O * (V * ψ * Uᴴ + U * ψ * Vᴴ))`. -/
theorem energy_fderiv_apply (O ψ U V : Matrix n n ℂ) :
    fderiv ℝ (energy O ψ) U V = (O * (V * ψ * Uᴴ + U * ψ * Vᴴ)).trace.re := by
  rw [(energy_hasFDerivAt O ψ U).fderiv]
  change (O * stateDerivative ψ U V).trace.re = _
  rw [stateDerivative_apply]

omit [DecidableEq n] in

/-- Taking the conjugate transpose of a complex matrix preserves the real part of its trace. -/
theorem trace_re_adjoint (A : Matrix n n ℂ) : Aᴴ.trace.re = A.trace.re := by
  rw [Matrix.trace_conjTranspose]
  rfl

/-- For Hermitian `O` and `ψ`, the energy derivative on `V` equals the real Frobenius pairing of
`2 • (O * U * ψ)` with `V`. -/
theorem energy_fderiv_frobenius (O ψ U V : Matrix n n ℂ) (hO : Oᴴ = O) (hψ : ψᴴ = ψ) :
    fderiv ℝ (energy O ψ) U V = realFrob ((2 : ℝ) • (O * U * ψ)) V := by
  rw [energy_fderiv_apply]
  have hcyc : (O * (V * ψ * Uᴴ)).trace = (ψ * Uᴴ * O * V).trace := by
    calc
      _ = ((O * V) * (ψ * Uᴴ)).trace := by congr 1; noncomm_ring
      _ = ((ψ * Uᴴ) * (O * V)).trace := Matrix.trace_mul_comm _ _
      _ = _ := by congr 1; noncomm_ring
  have hconj : (O * (U * ψ * Vᴴ)).trace.re = (ψ * Uᴴ * O * V).trace.re := by
    rw [← trace_re_adjoint (O * (U * ψ * Vᴴ))]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hO, hψ]
    rw [Matrix.trace_mul_comm]
    simpa only [Matrix.mul_assoc] using congrArg Complex.re hcyc
  simp only [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  rw [hcyc, hconj]
  simp only [realFrob, Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_mul,
    hO, hψ, Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
  change (ψ * Uᴴ * O * V).trace.re + (ψ * Uᴴ * O * V).trace.re =
    2 * (ψ * (Uᴴ * O) * V).trace.re
  rw [← Matrix.mul_assoc ψ Uᴴ O]
  ring
