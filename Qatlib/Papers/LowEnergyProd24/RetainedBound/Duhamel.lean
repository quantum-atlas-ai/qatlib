/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.ImaginaryLeak.InteractionWeight
import Qatlib.Foundations.MatrixAlgebra.CommutatorExp.DuhamelWord

/-!
# Duhamel identities for product formulas

This module defines the generator defect `defect` and its Hamiltonian form `hamiltonianDefect`
for a product exponential word. It proves exact Duhamel identities and bounds the full operator
error by the integral of the defect norm, as used in [HejaziZiniArrazola2024].

## Main statements

* `actual_duhamel_phased`: Expresses the product-formula error as an integral with the
  Hamiltonian defect.
* `actual_full_defect_integral`: Bounds the error norm by the integrated defect norm for
  nonnegative time.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option autoImplicit false
set_option maxHeartbeats 200000
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

/-- The difference between the instantaneous generator of the product word and the total
Hamiltonian generator. -/
def defect (h : Hamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :=
  generator (stages.map (stageGenerator h)) t-totalGenerator h

/-- The Hamiltonian form of the generator defect, obtained by multiplying `defect` by
`Complex.I`. -/
def hamiltonianDefect (h : Hamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :=
  Complex.I • defect h stages t

/-- The generator defect equals `-Complex.I` times the Hamiltonian defect. -/
theorem actual_defect_phase (h : Hamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :
    defect h stages t = (-Complex.I) • hamiltonianDefect h stages t := by
  simp only [hamiltonianDefect, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]

/-- The generator defect and the Hamiltonian defect have equal operator norms. -/
theorem actual_defect_norm (h : Hamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :
    ‖defect h stages t‖ = ‖hamiltonianDefect h stages t‖ := by
  rw [actual_defect_phase h stages t, norm_smul, norm_neg, Complex.norm_I, one_mul]

/-- The product-formula error equals the Duhamel integral of the generator defect between exact
and approximate evolutions. -/
theorem actual_duhamel (h : Hamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :
    approximate h stages t-evolve h.total t =
      ∫ s in (0 : ℝ)..t, evolve h.total (t-s)*defect h stages s*approximate h stages s := by
  have he := word_duhamel (totalGenerator h) (stages.map (stageGenerator h)) t
  simp only [← total_generator_exp h, defect, approximate]
  exact he

/-- The product-formula error equals the Duhamel integral with integrand containing
`(-Complex.I) • hamiltonianDefect` [HejaziZiniArrazola2024]. -/
theorem actual_duhamel_phased (h : Hamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :
    approximate h stages t-evolve h.total t =
      ∫ s in (0 : ℝ)..t, evolve h.total (t-s)*((-Complex.I) • hamiltonianDefect h stages s)*approximate h stages s := by
  simpa only [← actual_defect_phase] using actual_duhamel h stages t

/-- For nonnegative time, the operator norm of the product-formula error is bounded by the
integral of the Hamiltonian defect norm. -/
theorem actual_full_defect_integral (h : Hamiltonian N R M k d J) (stages : List (ℝ × Fin M))
    (t : ℝ) (ht : 0 ≤ t) :
    ‖approximate h stages t-evolve h.total t‖ ≤ ∫ s in (0 : ℝ)..t, ‖hamiltonianDefect h stages s‖ := by
  rw [actual_duhamel]
  calc
    _ ≤ ∫ s in (0 : ℝ)..t, ‖evolve h.total (t-s)*defect h stages s*approximate h stages s‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro s hs
      change ‖evolve h.total
          (t-s)*defect h stages s*approximate h stages s‖ = ‖hamiltonianDefect h stages s‖
      rw [CStarRing.norm_mul_mem_unitary _ (approximate_unitary h stages s),
        CStarRing.norm_mem_unitary_mul _ (evolve_unitary _ h.total_hermitian (t-s)), actual_defect_norm]
end Qatlib.Papers.LowEnergyProd24.RetainedBound
