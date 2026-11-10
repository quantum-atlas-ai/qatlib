/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.ProductError.CoefficientRecursion
import Qatlib.Foundations.MatrixAlgebra.CommutatorExp.GeneratorSeries
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 250000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.ProductError
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Foundations.MatrixAlgebra.CommutatorExp
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {N R M k d : ℕ} {J : ℝ}
local instance : NormedAlgebra ℝ (Matrix (Register N) (Register N) ℂ) := .restrictScalars ℝ ℂ _

theorem computedCoefficient_eq_actual (h : Hamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (n : ℕ) :
    computedCoefficient h stages n = generatorCoefficient (stages.map (stageGenerator h)) n := by
  induction stages generalizing n with
  | nil => simp only [computedCoefficient, lieTerms, List.map_nil, List.sum_nil, generatorCoefficient]
  | cons stage stages ih =>
    rw [computedCoefficient_cons, List.map_cons, generatorCoefficient]
    congr 1
    apply Finset.sum_congr rfl
    intro ij hij
    rw [ih, one_div]

theorem actual_generator_hasSum (h : Hamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :
    HasSum (fun n : ℕ => t^n • computedCoefficient h stages n)
      (generator (stages.map (stageGenerator h)) t) := by
  simpa only [computedCoefficient_eq_actual] using
      generator_hasSum (stages.map (stageGenerator h)) t

def weightMap (h : Hamiltonian N R M k d J) (lam : ℝ) :
    Matrix (Register N) (Register N) ℂ →L[ℝ] Matrix (Register N) (Register N) ℂ :=
  (right (NormedSpace.exp ((-lam : ℂ) • h.total))).comp (left (NormedSpace.exp ((lam : ℂ) • h.total)))

theorem weightMap_apply (h : Hamiltonian N R M k d J) (lam : ℝ) (A : Matrix (Register N) (Register N) ℂ) :
    weightMap h lam A = weighted h.total A lam := rfl

theorem actual_weighted_generator_hasSum (h : Hamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (lam t : ℝ) :
    HasSum (fun n : ℕ => t^n • weighted h.total (computedCoefficient h stages n) lam)
      (weighted h.total (generator (stages.map (stageGenerator h)) t) lam) := by
  have hs := (weightMap h lam).hasSum (actual_generator_hasSum h stages t)
  simpa only [map_smul, weightMap_apply] using hs

def lowerOrderCancellation (h : Hamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (p : ℕ) : Prop :=
  ∀ n < p, computedCoefficient h stages n = if n=0 then totalGenerator h else 0
end Qatlib.Papers.LowEnergyProd24.ProductError
