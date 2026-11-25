/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation.ActualReadout

@[expose] public section

/-!
# Counting-register laws on spectral superpositions

[KerenidisPrakash2017], Algorithm 5.1, applies a powered phase-estimation
program to a superposition in the walk register. The finite program is
linear in the input amplitudes. On an orthonormal eigenfamily the
counting-register marginal is a mixture of the eigenstate marginals,
including when two eigenphases agree. The family can be incomplete if
the supplied input is in its span.

[Fixed source](https://arxiv.org/abs/1603.08675v3)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QRecommender16.Recommendations

open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge (relabelState)
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Papers.QAlgorithms97.MainResults.PhaseEstimation
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout (qpeKernel)
open scoped Classical BigOperators

/-- Executing any finite powered program transports a finite linear combination term by term. -/
theorem execute_powered_sum {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    {bits : ℕ} (U : Matrix I I ℂ) (program : List (PoweredProgram.Instruction bits))
    (v : J → QState (Reg bits × I)) (c : J → ℂ) :
    PoweredProgram.execute U program (∑ j, c j • v j) =
      ∑ j, c j • PoweredProgram.execute U program (v j) := by
  induction program generalizing v with
  | nil => rfl
  | cons instruction rest ih =>
    simp only [PoweredProgram.execute, ApplyGate, Matrix.mulVec_sum, Matrix.mulVec_smul]
    exact ih _

/-- The executed phase-estimation word on a supplied eigenstate combination produces the
corresponding combination of phase kernels tensored with their target states. -/
theorem powered_word_spectral_run {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    (bits : ℕ) (U : Matrix I I ℂ) (v : J → QState I) (c : J → ℂ) (phase : J → ℝ)
    (hEigen : ∀ j, U *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * phase j) • v j) :
    PoweredProgram.execute U (PoweredProgram.word bits)
      (TensorState (Ket (ZeroStr bits)) (∑ j, c j • v j)) =
        ∑ j, c j • TensorState
          (relabelState (bitVecEquiv bits).symm (qpeKernel (2 ^ bits) (phase j))) (v j) := by
  have hTensor : TensorState (Ket (ZeroStr bits)) (∑ j, c j • v j) =
      ∑ j, c j • TensorState (Ket (ZeroStr bits)) (v j) := by
    funext p
    simp only [TensorState, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hTensor, execute_powered_sum]
  simp_rw [PoweredProgram.word_run bits U (phase _) (v _) (hEigen _)]

/-- The marginal of any counting-register event is the weighted sum of its masses
under the individual eigenstate inputs. The weights are squared coefficient norms. -/
theorem powered_word_spectral_event {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    (bits : ℕ) (U : Matrix I I ℂ) (v : J → QState I) (c : J → ℂ) (phase : J → ℝ)
    (hOrthogonal : ∀ j k, Inner (v j) (v k) = if j = k then 1 else 0)
    (hEigen : ∀ j, U *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * phase j) • v j)
    (events : Finset (Reg bits)) :
    MeasureProb (PoweredProgram.execute U (PoweredProgram.word bits)
        (TensorState (Ket (ZeroStr bits)) (∑ j, c j • v j))) (events ×ˢ (Finset.univ : Finset I)) =
      ∑ j, ‖c j‖ ^ 2 * MeasureProb (PoweredProgram.execute U (PoweredProgram.word bits)
        (TensorState (Ket (ZeroStr bits)) (v j))) (events ×ˢ (Finset.univ : Finset I)) := by
  let kernel (j : J) := relabelState (bitVecEquiv bits).symm (qpeKernel (2 ^ bits) (phase j))
  have hSlice (z : Reg bits) :
      (fun i => (∑ j, c j • TensorState (kernel j) (v j)) (z, i)) =
        ∑ j, (c j * kernel j z) • v j := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, TensorState, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hMass (j : J) :
      MeasureProb (PoweredProgram.execute U (PoweredProgram.word bits)
        (TensorState (Ket (ZeroStr bits)) (v j))) (events ×ˢ (Finset.univ : Finset I)) =
        ∑ z ∈ events, ‖kernel j z‖ ^ 2 := by
    have hn : Normalized (v j) := (normalized_iff_inner_self _).mpr (by simpa using hOrthogonal j j)
    rw [PoweredProgram.word_run bits U (phase j) (v j) (hEigen j)]
    exact measureProb_tensorState_left hn _ _
  rw [powered_word_spectral_run bits U v c phase hEigen]
  simp_rw [hMass]
  simp only [MeasureProb, Finset.sum_product, BornProb]
  change (∑ z ∈ events, ∑ i,
    ‖(fun i => (∑ j, c j • TensorState (kernel j) (v j)) (z, i)) i‖ ^ 2) = _
  calc
    _ = ∑ z ∈ events, ∑ j, ‖c j * kernel j z‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro z _
      rw [hSlice z, sum_norm_sq_orthonormal v _ hOrthogonal]
    _ = _ := by
      simp_rw [norm_mul, mul_pow]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]

/-- If a counting event implements a keep decision on every eigenbranch up to
the same probability error, its measured mass on a unit combination is within
that error of the ideal retained spectral weight. -/
theorem powered_spectral_acceptance_error {I J : Type} [Fintype I] [DecidableEq I] [Fintype J]
    (bits : ℕ) (U : Matrix I I ℂ) (v : J → QState I) (c : J → ℂ) (phase : J → ℝ)
    (hOrthogonal : ∀ j k, Inner (v j) (v k) = if j = k then 1 else 0)
    (hEigen : ∀ j, U *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * phase j) • v j)
    (hCoefficients : ∑ j, ‖c j‖ ^ 2 = 1)
    (accepted : Finset (Reg bits)) (keep : J → Prop) (error : ℝ)
    (hDecision : ∀ j, |MeasureProb (PoweredProgram.execute U (PoweredProgram.word bits)
      (TensorState (Ket (ZeroStr bits)) (v j))) (accepted ×ˢ (Finset.univ : Finset I)) -
        (if keep j then 1 else 0)| ≤ error) :
    |MeasureProb (PoweredProgram.execute U (PoweredProgram.word bits)
      (TensorState (Ket (ZeroStr bits)) (∑ j, c j • v j))) (accepted ×ˢ (Finset.univ : Finset I)) -
        ∑ j, ‖c j‖ ^ 2 * (if keep j then 1 else 0)| ≤ error := by
  rw [powered_word_spectral_event bits U v c phase hOrthogonal hEigen, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ j, ‖c j‖ ^ 2 * error := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hDecision j) (sq_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, hCoefficients, one_mul]

end Qatlib.Papers.QRecommender16.Recommendations
