/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.ImaginaryLeak.InteractionWeight
import Qatlib.Foundations.MatrixAlgebra.CommutatorExp.DuhamelWord
set_option warningAsError false

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

def defect (h : Hamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :=
  generator (stages.map (stageGenerator h)) t-totalGenerator h

def hamiltonianDefect (h : Hamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :=
  Complex.I • defect h stages t

theorem actual_defect_phase (h : Hamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :
    defect h stages t = (-Complex.I) • hamiltonianDefect h stages t := by
  simp only [hamiltonianDefect, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]

theorem actual_defect_norm (h : Hamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :
    ‖defect h stages t‖ = ‖hamiltonianDefect h stages t‖ := by
  rw [actual_defect_phase h stages t, norm_smul, norm_neg, Complex.norm_I, one_mul]

theorem actual_duhamel (h : Hamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :
    approximate h stages t-evolve h.total t =
      ∫ s in (0 : ℝ)..t, evolve h.total (t-s)*defect h stages s*approximate h stages s := by
  have he := word_duhamel (totalGenerator h) (stages.map (stageGenerator h)) t
  simp only [← total_generator_exp h, defect, approximate]
  exact he

theorem actual_duhamel_phased (h : Hamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :
    approximate h stages t-evolve h.total t =
      ∫ s in (0 : ℝ)..t, evolve h.total (t-s)*((-Complex.I) • hamiltonianDefect h stages s)*approximate h stages s := by
  simpa only [← actual_defect_phase] using actual_duhamel h stages t

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
