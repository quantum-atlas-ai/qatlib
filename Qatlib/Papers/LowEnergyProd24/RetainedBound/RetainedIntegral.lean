/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.RetainedBound.ProjectedDefect

/-!
# Duhamel integrals for retained product-formula error

This module proves continuity of the defect and Duhamel kernel and defines `sandwichMap` to pass
energy projections through the integral. It derives retained-error bounds in both generator and
Hamiltonian conventions for the analysis in [HejaziZiniArrazola2024].

## Main statements

* `actual_retained_duhamel`: Expresses the error between two spectral cutoffs as a projected
  Duhamel integral.
* `actual_source_retained_integral`: Bounds retained error using the Hamiltonian defect and
  product-word leakage.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.RetainedBound
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Papers.LowEnergyProd24.ProductError
open Qatlib.Papers.LowEnergyProd24.ImaginaryLeak
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
open Qatlib.Foundations.MatrixAlgebra.CommutatorExp
variable {N R M k d : ℕ} {J : ℝ}
local instance : NormedAlgebra ℝ (Matrix (Register N) (Register N) ℂ) := .restrictScalars ℝ ℂ _

/-- The generator defect of a fixed product word is continuous in time. -/
theorem actual_defect_continuous (h : Hamiltonian N R M k d J) (stages : List (ℝ × Fin M)) :
    Continuous (defect h stages) := (generator_continuous _).sub continuous_const

/-- For fixed final time, the Duhamel kernel is continuous in the integration variable. -/
theorem actual_kernel_continuous (h : Hamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :
    Continuous (fun s : ℝ => evolve h.total (t-s)*defect h stages s*approximate h stages s) := by
  have hU : Continuous (fun s : ℝ => evolve h.total (t-s)) := by
    simpa only [← total_generator_exp h] using!
      (exp_time_continuous (totalGenerator h)).comp (continuous_const.sub continuous_id)
  exact (hU.mul (actual_defect_continuous h stages)).mul (word_continuous _)

/-- The real continuous linear map sending `A` to its product with the low-energy projector at
`Λ` on the left and at `Δ` on the right. -/
def sandwichMap (h : Hamiltonian N R M k d J) (Δ Λ : ℝ) :
    Matrix (Register N) (Register N) ℂ →L[ℝ] Matrix (Register N) (Register N) ℂ :=
  (right (low h.total h.total_hermitian Δ)).comp (left (low h.total h.total_hermitian Λ))

/-- Evaluating `sandwichMap` gives the matrix product with the output and input low-energy
projectors. -/
theorem sandwichMap_apply (h : Hamiltonian N R M k d J) (Δ Λ : ℝ) (A : Matrix (Register N) (Register N) ℂ) :
    sandwichMap h Δ Λ A=low h.total h.total_hermitian Λ*A*low h.total h.total_hermitian Δ := rfl

/-- The product-formula error between the two energy cutoffs equals the integral of the
correspondingly projected Duhamel kernel. -/
theorem actual_retained_duhamel (h : Hamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (t Δ Λ : ℝ) :
    low h.total h.total_hermitian Λ*(approximate h stages t-evolve h.total t)*low h.total h.total_hermitian Δ =
      ∫ s in (0 : ℝ)..t, low h.total h.total_hermitian Λ*
        (evolve h.total (t-s)*defect h stages s*approximate h stages s)*low h.total h.total_hermitian Δ := by
  have hi := (sandwichMap h Δ Λ).intervalIntegral_comp_comm (μ := MeasureTheory.volume)
    ((actual_kernel_continuous h stages t).intervalIntegrable 0 t)
  change sandwichMap h Δ Λ (approximate h stages t-evolve h.total t) =
    ∫ s in (0 : ℝ)..t, sandwichMap h Δ Λ (evolve h.total (t-s)*defect h stages s*approximate h stages s)
  rw [actual_duhamel]
  exact hi.symm

/-- For nonnegative time, retained error is bounded by the integral of the compressed generator
defect norm plus the integral of the defect norm times leakage. -/
theorem actual_retained_integral_bound (h : Hamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (t Δ Λ : ℝ) (ht : 0 ≤ t) :
    ‖low h.total h.total_hermitian Λ*(approximate h stages t-evolve h.total t)*low h.total h.total_hermitian Δ‖ ≤
      (∫ s in (0 : ℝ)..t, ‖low h.total h.total_hermitian Λ*defect h stages s*low h.total h.total_hermitian Λ‖)+
      (∫ s in (0 : ℝ)..t, ‖defect h stages s‖*
        ‖high h.total h.total_hermitian Λ*approximate h stages s*low h.total h.total_hermitian Δ‖) := by
  have hD := actual_defect_continuous h stages
  have hW : Continuous (approximate h stages) := word_continuous _
  have hfirst : Continuous (fun s : ℝ => ‖low h.total h.total_hermitian Λ*defect h stages s*low h.total h.total_hermitian Λ‖) :=
    ((continuous_const.mul hD).mul continuous_const).norm
  have hsecond : Continuous (fun s : ℝ => ‖defect h stages s‖*
      ‖high h.total h.total_hermitian Λ*approximate h stages s*low h.total h.total_hermitian Δ‖) :=
    hD.norm.mul (((continuous_const.mul hW).mul continuous_const).norm)
  have hkernel : Continuous (fun s : ℝ => low h.total h.total_hermitian Λ*
      (evolve h.total (t-s)*defect h stages s*approximate h stages s)*low h.total h.total_hermitian Δ) :=
    (continuous_const.mul (actual_kernel_continuous h stages t)).mul continuous_const
  rw [actual_retained_duhamel]
  calc
    _ ≤ ∫ s in (0 : ℝ)..t, ‖low h.total h.total_hermitian Λ*
        (evolve h.total (t-s)*defect h stages s*approximate h stages s)*low h.total h.total_hermitian Δ‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht
    _ ≤ ∫ s in (0 : ℝ)..t,
        (‖low h.total h.total_hermitian Λ*defect h stages s*low h.total h.total_hermitian Λ‖+
        ‖defect h stages s‖*‖high h.total h.total_hermitian Λ*approximate h stages s*low h.total h.total_hermitian Δ‖) :=
      intervalIntegral.integral_mono_on ht (hkernel.norm.intervalIntegrable 0 t)
        ((hfirst.add hsecond).intervalIntegrable 0 t) (fun s _ => actual_retained_kernel_bound h stages t s Δ Λ)
    _ = _ := intervalIntegral.integral_add (hfirst.intervalIntegrable 0 t) (hsecond.intervalIntegrable 0 t)

/-- Compressing the generator defect and the Hamiltonian defect at the same cutoff gives equal
operator norms. -/
theorem actual_compressed_defect_norm (h : Hamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (s Λ : ℝ) :
    ‖low h.total h.total_hermitian Λ*defect h stages s*low h.total h.total_hermitian Λ‖ =
      ‖low h.total h.total_hermitian Λ*hamiltonianDefect h stages s*low h.total h.total_hermitian Λ‖ := by
  rw [actual_defect_phase h stages s, mul_smul_comm, smul_mul_assoc, norm_smul, norm_neg,
      Complex.norm_I, one_mul]

/-- For nonnegative time, retained error is bounded by the compressed Hamiltonian defect
integral plus the Hamiltonian defect norm weighted by product-word leakage. -/
theorem actual_source_retained_integral (h : Hamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (t Δ Λ : ℝ) (ht : 0 ≤ t) :
    ‖low h.total h.total_hermitian Λ*(approximate h stages t-evolve h.total t)*low h.total h.total_hermitian Δ‖ ≤
      (∫ s in (0 : ℝ)..t, ‖low h.total h.total_hermitian Λ*hamiltonianDefect h stages s*low h.total h.total_hermitian Λ‖)+
      (∫ s in (0 : ℝ)..t, ‖hamiltonianDefect h stages s‖*
        ‖high h.total h.total_hermitian Λ*approximate h stages s*low h.total h.total_hermitian Δ‖) := by
  simpa only [actual_compressed_defect_norm, actual_defect_norm] using!
      actual_retained_integral_bound h stages t Δ Λ ht
end Qatlib.Papers.LowEnergyProd24.RetainedBound
