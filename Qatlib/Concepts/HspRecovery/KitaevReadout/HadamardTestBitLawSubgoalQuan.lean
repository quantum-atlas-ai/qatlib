/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.KitaevReadout.HadamardTestBitLawSubgoalStat

/-!
# Born probabilities for the eigenphase Hadamard test

This module proves the ancilla output state and bit probabilities of a Hadamard test on an
eigenvector. `hadamardTestBitLawSubgoal` packages the state identity and the cosine-dependent
probabilities used in the phase estimation method of [Kitaev1995].

## Main statements

* `eigenPhase_norm`: a phase factor has unit norm.
* `hadamardTestBitState_born`: the probabilities are `(1 + cos (2πφ))/2` and `(1 - cos
  (2πφ))/2`.
* `hadamardTestBitLawSubgoal`: the full eigenvector state identity and bit law.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SpectralFilter.PhaseReadout

namespace Qatlib.Concepts.HspRecovery.KitaevReadout
open Matrix
open scoped BigOperators

/-- Expresses `eigenPhase φ` as the complex exponential of the real angle `2 * π * φ` multiplied
by the imaginary unit. -/
theorem eigenPhase_eq_exp_real (φ : ℝ) :
    eigenPhase φ = Complex.exp (((2 * Real.pi * φ : ℝ) : ℂ) * Complex.I) := by
  unfold eigenPhase
  congr 1
  push_cast
  ring

/-- Every phase factor `eigenPhase φ` has norm one. -/
theorem eigenPhase_norm (φ : ℝ) : ‖eigenPhase φ‖ = 1 := by
  rw [eigenPhase_eq_exp_real, Complex.norm_exp_ofReal_mul_I]

/-- The false and true Born probabilities of the eigenphase ancilla state are `(1 + cos (2πφ)) /
2` and `(1 - cos (2πφ)) / 2`, respectively. -/
theorem hadamardTestBitState_born (φ : ℝ) :
    BornProb (hadamardTestBitState (eigenPhase φ)) false =
        (1 + Real.cos (2 * Real.pi * φ)) / 2 ∧
    BornProb (hadamardTestBitState (eigenPhase φ)) true =
        (1 - Real.cos (2 * Real.pi * φ)) / 2 := by
  have hns : Complex.normSq (eigenPhase φ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, eigenPhase_norm]
    norm_num
  have hre : (eigenPhase φ).re = Real.cos (2 * Real.pi * φ) := by
    rw [eigenPhase_eq_exp_real]
    simp [Complex.exp_re, Complex.mul_re, Complex.mul_im]
  constructor
  · change ‖(1 + eigenPhase φ) / 2‖ ^ 2 = _
    rw [norm_div, div_pow, ← Complex.normSq_eq_norm_sq]
    norm_num [Complex.normSq_add, hns, hre]
    ring
  · change ‖(1 - eigenPhase φ) / 2‖ ^ 2 = _
    rw [norm_div, div_pow, ← Complex.normSq_eq_norm_sq]
    norm_num [Complex.normSq_sub, hns, hre]
    ring

/-- On an eigenvector of `U`, the controlled matrix preserves the first tensor factor and
multiplies the true-control amplitude by the corresponding eigenphase. -/
private theorem controlled_eigenstate {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (ψ : QState I) (φ : ℝ)
    (hU : U *ᵥ ψ = eigenPhase φ • ψ) (ν : QState Bool) :
    ApplyGate (eigenphaseControlledGate I U) (TensorState ψ ν) =
      TensorState ψ (fun b => (if b then eigenPhase φ else 1) * ν b) := by
  funext p
  obtain ⟨i, b⟩ := p
  cases b
  · simp [ApplyGate, Matrix.mulVec, dotProduct, eigenphaseControlledGate,
      TensorState, Fintype.sum_prod_type, Matrix.one_apply]
  · have hi := congrFun hU i
    change (∑ k : I, U i k * ψ k) = eigenPhase φ * ψ i at hi
    simp only [ApplyGate, Matrix.mulVec, dotProduct, eigenphaseControlledGate,
      Matrix.of_apply, TensorState]
    rw [Fintype.sum_prod_type]
    simp
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, hi]
    ring

/-- Proves the Hadamard test output identity on an eigenvector and the cosine-dependent
probabilities of both ancilla bits, as used in [Kitaev1995]. -/
theorem hadamardTestBitLawSubgoal : HadamardTestBitLawSubgoal := by
  intro I _ _ U ψ φ hU
  refine ⟨?_, hadamardTestBitState_born φ⟩
  have hh : ∀ w : QState Bool, ApplyGate Hadamard w =
      fun b => (Real.sqrt 2 : ℂ)⁻¹ * (w false + if b then -w true else w true) := by
    intro w
    funext b
    cases b <;> simp [ApplyGate, Hadamard, Matrix.mulVec, dotProduct] <;> ring
  have hfirst : ApplyGate Hadamard (Ket false) = fun _ => (Real.sqrt 2 : ℂ)⁻¹ := by
    rw [hh]
    funext b
    cases b <;> simp [Ket]
  unfold hadamardTestGate
  rw [ApplyGate, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  change ApplyGate (TensorGate (1 : Matrix I I ℂ) Hadamard)
    (ApplyGate (eigenphaseControlledGate I U)
      (ApplyGate (TensorGate (1 : Matrix I I ℂ) Hadamard) (TensorState ψ (Ket false)))) = _
  rw [applyGate_tensorGate, applyGate_one, hfirst, controlled_eigenstate U ψ φ hU,
    applyGate_tensorGate, applyGate_one, hh]
  congr 1
  funext b
  have hn : (Real.sqrt 2 : ℂ)⁻¹ * (Real.sqrt 2 : ℂ)⁻¹ = (2 : ℂ)⁻¹ :=
    inv_sqrt_mul_inv_sqrt (by norm_num : 0 < (2 : ℕ))
  cases b
  · simp [hadamardTestBitState]
    linear_combination (1 + eigenPhase φ) * hn
  · simp [hadamardTestBitState]
    linear_combination (1 - eigenPhase φ) * hn

end Qatlib.Concepts.HspRecovery.KitaevReadout
