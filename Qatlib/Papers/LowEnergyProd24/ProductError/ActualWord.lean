/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.CommutatorExp.ExponentialWord
import Qatlib.Foundations.MatrixGeometry.SpectralCutoff.Evolution
import Qatlib.Papers.LowEnergyProd24.LocalModel.Hamiltonian

/-!
# Actual product words and repeated-step errors

The definitions `approximate` and `relative` form the exponential product word of real-weighted
grouped generators and its interaction-picture version. The module proves their differential
equations and unitarity, then bounds the low-energy error of `r` repeated steps by `r` times the
one-step error. See [HejaziZiniArrazola2024].

## Main statements

* `approximate_hasDerivAt`: The derivative of the approximate product word is its product
  generator multiplied on the left of the word.
* `approximate_unitary`: The approximate product word is unitary for every real time and every
  list of real stage weights.
* `actual_repeated_error`: On the total-energy sector at most `Δ`, the norm difference between
  `r` powers of the approximate and exact one-step evolutions is at most `r` times their
  one-step norm difference.

## References

* [Hejazi et al., 2024][HejaziZiniArrazola2024]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 120000
noncomputable section
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace Qatlib.Papers.LowEnergyProd24.ProductError
open Qatlib.Papers.LowEnergyProd24.LocalModel
open Qatlib.Foundations.MatrixGeometry.SpectralCutoff
open Qatlib.Foundations.MatrixAlgebra.CommutatorExp
variable {N R M k d : ℕ} {J : ℝ}
local instance : NormedAlgebra ℝ (Matrix (Register N) (Register N) ℂ) := .restrictScalars ℝ ℂ _

/-- The skew-Hermitian generator `-i * stage.1` times the grouped Hamiltonian selected by
`stage.2`. -/
def stageGenerator (h : Hamiltonian N R M k d J) (stage : ℝ × Fin M) : Matrix (Register N) (Register N) ℂ :=
  ((-stage.1 : ℂ)*Complex.I) • h.grouped stage.2

/-- The skew-Hermitian generator `-i` times the total Hamiltonian. -/
def totalGenerator (h : Hamiltonian N R M k d J) : Matrix (Register N) (Register N) ℂ :=
  ((-1 : ℂ)*Complex.I) • h.total

/-- The exponential product word at time `t` built from the indicated real-weighted grouped
generators. -/
def approximate (h : Hamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :=
  word (stages.map (stageGenerator h)) t

/-- The product word in the interaction picture relative to the total Hamiltonian generator. -/
def relative (h : Hamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :=
  interaction (totalGenerator h) (stages.map (stageGenerator h)) t

/-- The exponential of a stage generator at time `t` equals evolution under its grouped
Hamiltonian for time `stage.1 * t`. -/
theorem stage_exp (h : Hamiltonian N R M k d J) (stage : ℝ × Fin M) (t : ℝ) :
    NormedSpace.exp (t • stageGenerator h stage) = evolve (h.grouped stage.2) (stage.1*t) := by
  congr 1
  ext i j
  simp only [stageGenerator, Matrix.smul_apply, Complex.real_smul, smul_eq_mul,
    Complex.ofReal_mul]
  ring

/-- The derivative of the approximate product word is its product generator multiplied on the
left of the word. See [HejaziZiniArrazola2024]. -/
theorem approximate_hasDerivAt (h : Hamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :
    HasDerivAt (approximate h stages) (generator (stages.map (stageGenerator h)) t * approximate h stages t) t :=
  word_hasDerivAt _ _

/-- The derivative of the relative product word is its interaction generator multiplied on the
left of the relative word. -/
theorem relative_hasDerivAt (h : Hamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :
    HasDerivAt (relative h stages)
      (interactionGenerator (totalGenerator h) (stages.map (stageGenerator h)) t * relative h stages t) t :=
  interaction_hasDerivAt _ _ _

/-- The approximate product word is unitary for every real time and every list of real stage
weights. -/
theorem approximate_unitary (h : Hamiltonian N R M k d J) (stages : List (ℝ × Fin M)) (t : ℝ) :
    approximate h stages t ∈ unitary (Matrix (Register N) (Register N) ℂ) := by
  induction stages with
  | nil => exact one_mem _
  | cons stage stages ih =>
    change NormedSpace.exp (t • stageGenerator h stage) * approximate h stages t ∈ _
    rw [stage_exp]
    exact mul_mem (evolve_unitary _ (h.grouped_hermitian stage.2) _) ih

/-- On the total-energy sector at most `Δ`, the norm difference between `r` powers of the
approximate and exact one-step evolutions is at most `r` times their one-step norm
difference. -/
theorem actual_repeated_error (h : Hamiltonian N R M k d J) (stages : List (ℝ × Fin M))
    (t Δ : ℝ) (r : ℕ) :
    ‖(approximate h stages t ^ r - evolve h.total t ^ r) * low h.total h.total_hermitian Δ‖ ≤
      (r : ℝ)*‖(approximate h stages t - evolve h.total t) * low h.total h.total_hermitian Δ‖ := by
  let W := approximate h stages t
  let U := evolve h.total t
  let P := low h.total h.total_hermitian Δ
  have hW : W ∈ unitary (Matrix (Register N) (Register N) ℂ) := approximate_unitary h stages t
  have hU : U ∈ unitary (Matrix (Register N) (Register N) ℂ) := evolve_unitary _ h.total_hermitian t
  have hc : Commute U P := evolve_low_commute h.total h.total_hermitian t Δ
  change ‖(W^r-U^r)*P‖ ≤ (r : ℝ)*‖(W-U)*P‖
  induction r with
  | zero => simp
  | succ r ih =>
    have hpr : U^r*P = P*U^r := (hc.pow_left r).eq
    have he : (W^(r+1)-U^(r+1))*P = W*((W^r-U^r)*P)+((W-U)*P)*U^r := by
      rw [pow_succ', pow_succ']
      calc
        _ = W*((W^r-U^r)*P)+(W-U)*(U^r*P) := by noncomm_ring
        _ = _ := by rw [hpr]; noncomm_ring
    rw [he]
    calc
      _ ≤ ‖W*((W^r-U^r)*P)‖+‖((W-U)*P)*U^r‖ := norm_add_le _ _
      _ = ‖(W^r-U^r)*P‖+‖(W-U)*P‖ := by
        rw [CStarRing.norm_mem_unitary_mul _ hW, CStarRing.norm_mul_mem_unitary _ (pow_mem hU r)]
      _ ≤ (r : ℝ)*‖(W-U)*P‖+‖(W-U)*P‖ := by linarith only [ih]
      _ = _ := by push_cast; ring
end Qatlib.Papers.LowEnergyProd24.ProductError
