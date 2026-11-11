/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LowEnergyProd24.WordLeakage.GeneratorTail
import Qatlib.Papers.LowEnergyProd24.ImaginaryLeak.PolynomialGrowth

/-!
# Weighted product-word and leakage bounds

This module defines `growthCoefficient` and its integrated form `stepExponent` for a product
word with lower-order cancellation. It bounds the weighted interaction generator and weighted
word, obtaining exponential leakage across energy cutoffs for the analysis in
[HejaziZiniArrazola2024].

## Main statements

* `actual_weighted_word_bound`: Bounds the weighted word norm by `exp stepExponent`.
* `actual_product_word_leakage`: Combines the weighted bound with exponential energy-gap decay.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.WordLeakage
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Papers.LowEnergyProd24.ProductError
open Qatlib.Papers.LowEnergyProd24.RetainedBound
open Qatlib.Papers.LowEnergyProd24.ImaginaryLeak
open Qatlib.Foundations.MatrixAlgebra.CommutatorExp
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
variable {N R M k d : ℕ} {J : ℝ}
local instance : NormedAlgebra ℝ (Matrix (Register N) (Register N) ℂ) := .restrictScalars ℝ ℂ _

/-- The uniform generator-growth coefficient with numerator `L * (2 * J) * timeBudget stages *
(2 * J * k * d * timeBudget stages) ^ p` and the small-step geometric denominator. -/
def growthCoefficient (L k d : ℕ) (J : ℝ) (stages : List (ℝ × Fin M)) (p : ℕ) (s : ℝ) : ℝ :=
  ((L : ℝ)*(2*J)*timeBudget stages)*(2*J*k*d*timeBudget stages)^p /
    (1-2*J*k*d*timeBudget stages*s)

/-- The integrated growth majorant `growthCoefficient * s ^ (p + 1) / (p + 1)`. -/
def stepExponent (L k d : ℕ) (J : ℝ) (stages : List (ℝ × Fin M)) (p : ℕ) (s : ℝ) : ℝ :=
  growthCoefficient L k d J stages p s * s^(p+1)/(p+1)

/-- The relative propagator and the product word have equal weighted operator norms for every
real weight and time. -/
theorem actual_relative_weighted_norm (h : Hamiltonian N R M k d J)
    (stages : List (ℝ × Fin M)) (lam t : ℝ) :
    ‖weighted h.total (relative h stages t) lam‖ = ‖weighted h.total (approximate h stages t) lam‖ := by
  have he : relative h stages t = evolve h.total (-t)*approximate h stages t := by
    change NormedSpace.exp ((-t) • totalGenerator h)*word _ t = _
    rw [total_generator_exp]
    rfl
  rw [he, weighted_mul, weighted_exact_evolve]
  exact CStarRing.norm_mem_unitary_mul _ (evolve_unitary _ h.total_hermitian (-t))

/-- With lower-order cancellation through order `p - 1` and the stated small-step condition, the
weighted interaction-generator norm on `0 ≤ t ≤ s` is at most `growthCoefficient * t ^ p`. -/
theorem actual_uniform_generator_bound (h : Hamiltonian N R M k d J)
    (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d) (L : ℕ)
    (hL : ∀ m, (h.labels m).card ≤ L) (stages : List (ℝ × Fin M))
    (p : ℕ) (hp : 0 < p) (horder : lowerOrderCancellation h stages p)
    (s : ℝ) (hsmall : 2*J*k*d*timeBudget stages*s < 1)
    (t : ℝ) (ht : 0 ≤ t) (hts : t ≤ s) :
    ‖weighted h.total (interactionGenerator (totalGenerator h) (stages.map (stageGenerator h)) t) (1/(2*J*k*d))‖ ≤
      growthCoefficient L k d J stages p s * t^p := by
  let C : ℝ := 2*J*k*d*timeBudget stages
  let D : ℝ := (L : ℝ)*(2*J)*timeBudget stages
  have hA := timeBudget_nonneg stages
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCt : C*t < 1 := (mul_le_mul_of_nonneg_left hts hC).trans_lt hsmall
  have hb := actual_weighted_defect_bound h hJ hk hd L hL stages p hp horder t ht hCt
  rw [actual_interaction_generator_norm]
  change ‖weighted h.total (defect h stages t) (1/(2*J*k*d))‖ ≤ _
  calc
    _ ≤ D*(C*t)^p/(1-C*t) := hb
    _ = (D*C^p*t^p)/(1-C*t) := by rw [mul_pow]; ring
    _ ≤ (D*C^p*t^p)/(1-C*s) :=
      div_le_div_of_nonneg_left (by dsimp [D]; positivity) (by linarith) (by nlinarith)
    _ = _ := by dsimp [growthCoefficient, C, D]; ring

/-- For nonnegative small steps and positive order with lower-order cancellation, the weighted
product-word norm is at most `exp (stepExponent L k d J stages p s)`. -/
theorem actual_weighted_word_bound (h : Hamiltonian N R M k d J)
    (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d) (L : ℕ)
    (hL : ∀ m, (h.labels m).card ≤ L) (stages : List (ℝ × Fin M))
    (p : ℕ) (hp : 0 < p) (horder : lowerOrderCancellation h stages p)
    (s : ℝ) (hs : 0 ≤ s) (hsmall : 2*J*k*d*timeBudget stages*s < 1) :
    ‖weighted h.total (approximate h stages s) (1/(2*J*k*d))‖ ≤ Real.exp (stepExponent L k d J stages p s) := by
  let lam : ℝ := 1/(2*J*k*d)
  let f : ℝ → Matrix (Register N) (Register N) ℂ :=
      fun t => weighted h.total (relative h stages t) lam
  let f' : ℝ → Matrix (Register N) (Register N) ℂ := fun t =>
    weighted h.total (interactionGenerator (totalGenerator h) (stages.map (stageGenerator h)) t) lam * f t
  have hder (t : ℝ) : HasDerivAt f (f' t) t := actual_weighted_interaction_derivative h stages lam t
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun t => (hder t).continuousAt)
  have hzero : relative h stages 0=1 := interaction_zero _ _
  have hweightone : weighted h.total 1 lam=1 := by
    simpa only [evolve, neg_zero, Complex.ofReal_zero, zero_mul, zero_smul,
        NormedSpace.exp_zero] using weighted_exact_evolve h lam 0
  have h0 : ‖f 0‖ ≤ 1 := by simp only [f, hzero, hweightone, norm_one, le_refl]
  have hbound (t : ℝ) (ht : t ∈ Set.Ico 0 s) :
      ‖f' t‖ ≤ growthCoefficient L k d J stages p s*t^p*‖f t‖ := by
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
      (actual_uniform_generator_bound h hJ hk hd L hL stages p hp horder s hsmall t ht.1 ht.2.le) (norm_nonneg _))
  have hb := polynomial_growth f f' (growthCoefficient L k d J stages p s) 1 s p (by norm_num)
    hf.continuousOn (fun t _ => (hder t).hasDerivWithinAt) h0 hbound s ⟨hs, le_rfl⟩
  simpa only [one_mul, f, actual_relative_weighted_norm, stepExponent] using hb

/-- Under the locality, cancellation, and small-step hypotheses, leakage from the input cutoff
`Δ` to above `Λ` is at most `exp (-(Λ - Δ) / (2 * J * k * d) + stepExponent L k d J stages p
s)`. -/
theorem actual_product_word_leakage (h : Hamiltonian N R M k d J)
    (hJ : 0 < J) (hk : 0 < k) (hd : 0 < d) (L : ℕ)
    (hL : ∀ m, (h.labels m).card ≤ L) (stages : List (ℝ × Fin M))
    (p : ℕ) (hp : 0 < p) (horder : lowerOrderCancellation h stages p)
    (s : ℝ) (hs : 0 ≤ s) (hsmall : 2*J*k*d*timeBudget stages*s < 1) (Δ Λ : ℝ) :
    ‖high h.total h.total_hermitian Λ*approximate h stages s*low h.total h.total_hermitian Δ‖ ≤
      Real.exp (-(1/(2*J*k*d))*(Λ-Δ)+stepExponent L k d J stages p s) := by
  calc
    _ ≤ Real.exp (-(1/(2*J*k*d))*(Λ-Δ))*‖weighted h.total (approximate h stages s) (1/(2*J*k*d))‖ :=
      weighted_leakage h.total (approximate h stages s) h.total_hermitian Δ Λ (1/(2*J*k*d)) (by positivity)
    _ ≤ Real.exp (-(1/(2*J*k*d))*(Λ-Δ))*Real.exp (stepExponent L k d J stages p s) :=
      mul_le_mul_of_nonneg_left (actual_weighted_word_bound h hJ hk hd L hL stages p hp horder s hs hsmall) (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm
end Qatlib.Papers.LowEnergyProd24.WordLeakage
