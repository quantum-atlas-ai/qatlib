/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QGradient20.MainResults.PhysicalStep

/-!
# The conditioned physical gradient state

`normalizedOutput` normalizes the successful dressed vector at branch parameter one third, and
`outputState` is its pure mixed-state representation. `actual_conditioned_state` identifies the
unnormalized completely positive success output as its Born probability times this state;
decoding yields the same classical gradient step. The mathematical context is [GaoEtAl2021].

## Main statements

* `actual_conditioned_state`: The completely positive success map applied to the dressed input
  density matrix equals the actual success probability times the density matrix of
  `outputState`.
* `normalizedOutput_decode`: For positive tensor order, coordinate-ratio decoding of the
  normalized output gives the signed classical gradient step with rate `decodedRate A x (1/3)`.

## References

* [Gao et al., 2021][GaoEtAl2021]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open Matrix
open Qatlib.Concepts.ChannelTheory.Naimark
open scoped BigOperators Matrix.Norms.L2Operator
namespace Qatlib.Papers.QGradient20.MainResults.PhysicalStep
open Qatlib.Papers.QGradient20.Polynomial
open Qatlib.Papers.QGradient20.DressedUpdate
open Qatlib.Papers.QGradient20.FilterBranch
variable {I : Type} [Fintype I] [DecidableEq I]

/-- At branch parameter `1/3`, the successful dressed vector has strictly positive norm. -/
theorem outputVector_norm_pos {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) (ascent : Bool) : 0 < ‖outputVector A x (1/3) ascent‖ := by
  have h := outputVector_mass_third A x ascent
  nlinarith [norm_nonneg (outputVector A x (1/3) ascent)]

/-- The successful dressed vector at branch parameter `1/3` divided by its Euclidean norm. -/
def normalizedOutput {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) (ascent : Bool) : EuclideanSpace ℂ (Option I) :=
  ‖outputVector A x (1/3) ascent‖⁻¹ • outputVector A x (1/3) ascent

/-- The normalized successful dressed output has norm one. -/
theorem normalizedOutput_norm {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) (ascent : Bool) : ‖normalizedOutput A x ascent‖ = 1 := by
  rw [normalizedOutput,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (outputVector_norm_pos A x ascent))]
  exact inv_mul_cancel₀ (outputVector_norm_pos A x ascent).ne'

/-- The pure mixed state associated with the normalized successful dressed output. -/
def outputState {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) (ascent : Bool) : MState (Option I) :=
  MState.pure (ContractionBorn.ketOfUnit (normalizedOutput A x ascent) (normalizedOutput_norm A x ascent))

/-- The completely positive success map applied to the dressed input density matrix equals the
actual success probability times the density matrix of `outputState`. See [GaoEtAl2021]. -/
theorem actual_conditioned_state {p : ℕ}
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) (ascent : Bool) :
    (ContractionInstrument.successCP (successOperator none (complexDerivative A x) (1/3) ascent)).map (inputState x).m =
      (((gradientReadout A x (1/3) (by norm_num) ascent).measure (inputState x)) true : ℝ) •
        (outputState A x ascent).m := by
  rw [actual_success_density,actual_gradient_Born]
  ext i j
  change outputVector A x (1/3) ascent i * star (outputVector A x (1/3) ascent j) =
    (‖outputVector A x (1/3) ascent‖ ^ 2 : ℝ) •
      ((‖outputVector A x (1/3) ascent‖⁻¹ : ℝ) • outputVector A x (1/3) ascent i *
        star ((‖outputVector A x (1/3) ascent‖⁻¹ : ℝ) • outputVector A x (1/3) ascent j))
  have hn : (‖outputVector A x (1/3) ascent‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (outputVector_norm_pos A x ascent).ne'
  simp only [Complex.real_smul,Complex.star_def,map_mul,Complex.ofReal_inv,Complex.ofReal_pow,map_inv₀]
  rw [Complex.conj_ofReal]
  field_simp [hn]

/-- For positive tensor order, coordinate-ratio decoding of the normalized output gives the
signed classical gradient step with rate `decodedRate A x (1/3)`. See [GaoEtAl2021]. -/
theorem normalizedOutput_decode {p : ℕ} (hp : 0 < p)
    (A : Matrix (TensorIndex p (Option I)) (TensorIndex p (Option I)) ℝ)
    (x : I → ℝ) (ascent : Bool) (i : I) :
    normalizedOutput A x ascent (some i) / normalizedOutput A x ascent none =
      ((x i + branchSign ascent * decodedRate A x (1/3) * gradient A (homogeneousInput x) (some i) : ℝ) : ℂ) := by
  have hn : (‖outputVector A x (1/3) ascent‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (outputVector_norm_pos A x ascent).ne'
  have hc : outputVector A x (1/3) ascent none ≠ 0 := by
    rw [outputVector_none]
    apply Complex.ofReal_ne_zero.mpr
    exact mul_ne_zero (by norm_num) (normalizer_pos x).ne'
  have he : normalizedOutput A x ascent (some i) / normalizedOutput A x ascent none =
      outputVector A x (1/3) ascent (some i) / outputVector A x (1/3) ascent none := by
    simp only [normalizedOutput,PiLp.smul_apply,Complex.real_smul,Complex.ofReal_inv]
    field_simp
  rw [he]
  exact outputVector_decode hp A x (1/3) (by norm_num) ascent i

end Qatlib.Papers.QGradient20.MainResults.PhysicalStep
