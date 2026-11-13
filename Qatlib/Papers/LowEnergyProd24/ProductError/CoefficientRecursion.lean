/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.ProductError.CoefficientBounds

/-!
# Recursion for evaluated generator coefficients

Evaluation commutes with real scaling and repeated commutators distribute over finite sums.
These identities prove `computedCoefficient_cons`, the antidiagonal recursion for the generator
coefficients after prepending a stage to a product word. See [HejaziZiniArrazola2024].

## Main statements

* `LieTerm.scale_evaluate`: Evaluating a Lie term after scaling its coefficient by a real number
  equals scaling its evaluated matrix by that number.
* `computedCoefficient_cons`: Prepending a stage adds its generator at degree zero and otherwise
  convolves the remaining coefficients with iterated commutators of that stage generator,
  weighted by reciprocal factorials.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.ProductError
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Foundations.MatrixAlgebra.CommutatorExp
variable {N R M k d : ℕ} {J : ℝ}
local instance : NormedAlgebra ℝ (Matrix (Register N) (Register N) ℂ) := .restrictScalars ℝ ℂ _

/-- Evaluating a Lie term after scaling its coefficient by a real number equals scaling its
evaluated matrix by that number. -/
theorem LieTerm.scale_evaluate (h : Hamiltonian N R M k d J) (c : ℝ) (term : LieTerm M) :
    (term.scale c).evaluate h = c • term.evaluate h := by
  ext i j
  simp only [LieTerm.scale, LieTerm.evaluate, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
  ring

/-- Repeated commutation with a fixed matrix distributes over a finite list sum. -/
theorem adIter_list_sum {α : Type*} (K : Matrix (Register N) (Register N) ℂ) (n : ℕ)
    (l : List α) (f : α → Matrix (Register N) (Register N) ℂ) :
    adIter K n (l.map f).sum = (l.map (fun a => adIter K n (f a))).sum := by
  rw [← adMap_pow_apply, map_list_sum]
  simp only [List.map_map, Function.comp_def, adMap_pow_apply]

/-- Prepending a stage adds its generator at degree zero and otherwise convolves the remaining
coefficients with iterated commutators of that stage generator, weighted by reciprocal
factorials. -/
theorem computedCoefficient_cons (h : Hamiltonian N R M k d J)
    (stage : ℝ × Fin M) (stages : List (ℝ × Fin M)) (n : ℕ) :
    computedCoefficient h (stage::stages) n = (if n=0 then stageGenerator h stage else 0) +
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, (1/(ij.1.factorial : ℝ)) •
        adIter (stageGenerator h stage) ij.1 (computedCoefficient h stages ij.2) := by
  simp only [computedCoefficient, lieTerms, List.map_append, List.sum_append, Hamiltonian.flatMap_sum,
    List.map_map, Function.comp_def]
  congr 1
  · split_ifs <;> simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      LieTerm.evaluate, RetainedError.nested, stageGenerator]
  · have he (ij : ℕ × ℕ) :
        ((lieTerms stages ij.2).map (fun term => ((term.raise stage ij.1).scale (1/(ij.1.factorial : ℝ))).evaluate h)).sum =
          (1/(ij.1.factorial : ℝ)) • adIter (stageGenerator h stage) ij.1
            ((lieTerms stages ij.2).map (LieTerm.evaluate h)).sum := by
      simp only [LieTerm.scale_evaluate, LieTerm.raise_evaluate, adIter_list_sum, List.smul_sum,
          List.map_map, Function.comp_def]
    simp_rw [he]
    simpa only [Finset.toList_toFinset] using
      (List.sum_toFinset (fun ij : ℕ × ℕ => (1/(ij.1.factorial : ℝ)) •
        adIter (stageGenerator h stage) ij.1 ((lieTerms stages ij.2).map (LieTerm.evaluate h)).sum)
        (Finset.nodup_toList (Finset.HasAntidiagonal.antidiagonal n))).symm
end Qatlib.Papers.LowEnergyProd24.ProductError
