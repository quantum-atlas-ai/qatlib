/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.ProductError.ActualWord
import Qatlib.Papers.LowEnergyProd24.ImaginaryLeak.LocalConjugation
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.ImaginaryLeak
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Papers.LowEnergyProd24.ProductError
open Qatlib.Foundations.MatrixAlgebra.CommutatorExp
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {N R M k d : ℕ} {J : ℝ}
local instance : NormedAlgebra ℝ (Matrix (Register N) (Register N) ℂ) := .restrictScalars ℝ ℂ _

theorem total_generator_exp (h : Hamiltonian N R M k d J) (t : ℝ) :
    NormedSpace.exp (t • totalGenerator h) = evolve h.total t := by
  congr 1
  ext i j
  simp only [totalGenerator, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  ring

theorem weighted_exact_evolve (h : Hamiltonian N R M k d J) (lam t : ℝ) :
    weighted h.total (evolve h.total t) lam = evolve h.total t := by
  let E := NormedSpace.exp ((lam : ℂ) • h.total)
  let F := NormedSpace.exp ((-lam : ℂ) • h.total)
  let U := evolve h.total t
  have hc : Commute E U :=
    (((Commute.refl h.total).smul_left (lam : ℂ)).smul_right (((-t : ℂ)*Complex.I))).exp
  have he (s : ℝ) : s • h.total = (s : ℂ) • h.total := by
    ext i j
    exact Complex.real_smul
  have hEF : E*F=1 := by
    simpa only [E, F, he, neg_neg, Complex.ofReal_neg] using exp_neg_time_mul h.total (-lam)
  change E*U*F=U
  rw [hc.eq, mul_assoc, hEF, mul_one]

theorem actual_interaction_generator_norm (h : Hamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (lam t : ℝ) :
    ‖weighted h.total (interactionGenerator (totalGenerator h) (stages.map (stageGenerator h)) t) lam‖ =
      ‖weighted h.total (generator (stages.map (stageGenerator h)) t-totalGenerator h) lam‖ := by
  change ‖weighted h.total (NormedSpace.exp ((-t) • totalGenerator h) *
    (generator (stages.map (stageGenerator h)) t-totalGenerator h) *
      NormedSpace.exp (t • totalGenerator h)) lam‖ = _
  rw [total_generator_exp h (-t), total_generator_exp h t,
    weighted_mul, weighted_mul, weighted_exact_evolve, weighted_exact_evolve]
  rw [CStarRing.norm_mul_mem_unitary _ (evolve_unitary _ h.total_hermitian t),
    CStarRing.norm_mem_unitary_mul _ (evolve_unitary _ h.total_hermitian (-t))]

theorem actual_weighted_interaction_derivative (h : Hamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (lam t : ℝ) :
    HasDerivAt (fun s => weighted h.total (relative h stages s) lam)
      (weighted h.total (interactionGenerator (totalGenerator h) (stages.map (stageGenerator h)) t) lam *
        weighted h.total (relative h stages t) lam) t := by
  have hd := ((relative_hasDerivAt h stages t).const_mul (NormedSpace.exp ((lam : ℂ) • h.total))).mul_const
    (NormedSpace.exp ((-lam : ℂ) • h.total))
  have heq : weighted h.total (interactionGenerator (totalGenerator h) (stages.map (stageGenerator h)) t * relative h stages t) lam =
      weighted h.total (interactionGenerator (totalGenerator h) (stages.map (stageGenerator h)) t) lam *
        weighted h.total (relative h stages t) lam := weighted_mul _ _ _ _
  change HasDerivAt _ (weighted h.total
    (interactionGenerator (totalGenerator h) (stages.map (stageGenerator h)) t * relative h stages t) lam) t at hd
  rw [heq] at hd
  exact hd
end Qatlib.Papers.LowEnergyProd24.ImaginaryLeak
