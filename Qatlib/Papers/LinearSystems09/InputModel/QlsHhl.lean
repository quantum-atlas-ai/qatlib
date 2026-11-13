/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LinearSystems09.InputModel.QlsHhlDefs

/-!
# HHL input-model interface statements

This module collects interface statements for the HHL input model in [HarrowHassidimLloyd2009].
The `clause55_endpoint` and `clause60_endpoint` theorems package dilation and signed-filter
properties, while the remaining endpoints record preparation, storage, error-budget,
runtime-scale, and Simon-exponent facts.

## Main statements

* `clause55_endpoint`: Collects the scaled dilation and least-squares reduction properties.
* `clause60_endpoint`: Collects symmetry, mass bounds, and normalization for consistent signed
  filters.
* `clause53_endpoint`: Packages envelope symmetry and preparation bit bounds.

## References

* [Harrow et al., 2009][HarrowHassidimLloyd2009]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
open Qatlib.Papers.LinearSystems09.InputModel

set_option autoImplicit false

namespace Qatlib.Papers.LinearSystems09.InputModel.QlsHhl

open Matrix
open Qatlib
open Qatlib.Concepts.QlsReadoutSpec.RectDilation
open Qatlib.Concepts.HhlErrorBridge.FilterStability

/-- Collects the Hermitianity, quarter-scaling, and block entries of the scaled dilation,
existence of a rectangular reduction, and absence of a direction when the least-squares
vector vanishes. -/
theorem clause55_endpoint :
    (∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ),
      (qlsScaledDilation A).IsHermitian) ∧
    (∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ),
      qlsScaledDilation A = (1 / 4 : ℂ) • hermitianDilation A) ∧
    (∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ),
      (∀ (i i' : Fin m), qlsScaledDilation A (Sum.inl i) (Sum.inl i') = 0) ∧
        (∀ (i : Fin m) (j : Fin n),
          qlsScaledDilation A (Sum.inl i) (Sum.inr j) = (1 / 4 : ℂ) * A i j) ∧
        (∀ (j : Fin n) (i : Fin m),
          qlsScaledDilation A (Sum.inr j) (Sum.inl i) = (1 / 4 : ℂ) * star (A i j)) ∧
        (∀ (j j' : Fin n), qlsScaledDilation A (Sum.inr j) (Sum.inr j') = 0)) ∧
    (∀ (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
      (A : Matrix O I ℂ) (b : QState O),
      ∃ R : Qatlib.Concepts.QlsReadoutSpec.RectDilation.DilationReduction O I,
        R.A = A ∧ R.b = b ∧ R.ReducesAt) ∧
    (∀ (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
      (A : Matrix O I ℂ) (b : QState O),
      leastSquaresVector A b = 0 → leastSquaresDirection A b = none) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro m n A
    exact qlsScaledDilation_isHermitian A
  · intro m n A
    exact qlsScaledDilation_eq_quarter_hermitianDilation A
  · intro m n A
    exact qlsScaledDilation_block_content A
  · intro O I _ _ _ _ A b
    exact qlsDilation_reduces A b
  · intro O I _ _ _ _ A b h
    exact leastSquaresDirection_none_of_zero_vector A b h

/-- Collects evenness, agreement with the unsigned mass on nonnegative inputs, the unit mass
bound, zero-mode flags, and normalization of consistent signed filters at positive `d`. -/
theorem clause60_endpoint :
    (∀ (F : SignedSinEnvelopeFilter) (hF : F.Consistent) (d θ : ℝ) (hd : 0 < d),
      signedKernelMass F d θ = signedKernelMass F d (-θ)) ∧
    (∀ (F : SignedSinEnvelopeFilter) (hF : F.Consistent) (d θ : ℝ) (hd : 0 < d)
      (hθ : 0 ≤ θ),
      signedKernelMass F d θ =
        sinEnvelopeFilterF d θ ^ 2 + sinEnvelopeFilterG d θ ^ 2) ∧
    (∀ (F : SignedSinEnvelopeFilter) (hF : F.Consistent) (d θ : ℝ) (hd : 0 < d),
      signedKernelMass F d θ ≤ 1) ∧
    (∀ (F : SignedSinEnvelopeFilter) (hF : F.Consistent) (d : ℝ) (hd : 0 < d),
      F.filterF d 0 = 0 ∧ F.filterG d 0 = 1 / 2) ∧
    (∀ (F : SignedSinEnvelopeFilter) (hF : F.Consistent) (d θ : ℝ) (hd : 0 < d),
      ∑ s : Fin 3, ‖F.hVector d θ s‖ ^ 2 = 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro F hF d θ hd
    exact signedKernelMass_even F hF d θ hd
  · intro F hF d θ hd hθ
    exact signedKernelMass_eq_unsigned F hF d θ hd hθ
  · intro F hF d θ hd
    exact signedKernelMass_le_one F hF d θ hd
  · intro F hF d hd
    exact signedFilter_zeroMode_flag F hF d hd
  · intro F hF d θ hd
    exact signed_hVector_normalized F hF d θ hd

/-- Collects the denominator bit bound, monotonicity of table storage, and the sum and
first-argument monotonicity of the total error budget. -/
theorem clause57_endpoint :
    (∀ q : ℕ, q < 2 ^ denominatorBits q) ∧
    (∀ M M' q q' : ℕ, M ≤ M' → q ≤ q' →
      tableStorageBits M q ≤ tableStorageBits M' q') ∧
    (∀ a b c d : ℝ, qlsErrorBudget a b c d = a + b + c + d) ∧
    (∀ a a' b c d : ℝ, a ≤ a' →
      qlsErrorBudget a b c d ≤ qlsErrorBudget a' b c d) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q
    exact denominatorBits_spec q
  · intro M M' q q' hM hq
    exact tableStorageBits_mono M M' q q' hM hq
  · intro a b c d
    exact qlsErrorBudget_sum a b c d
  · intro a a' b c d h
    exact qlsErrorBudget_mono a a' b c d h

/-- Collects reflection symmetry of the sine envelope, the pointwise-to-Euclidean error bound,
and the preparation angle-bit and stage-count bounds. -/
theorem clause53_endpoint :
    (∀ (M : ℕ) (hM : 0 < M) (τ : Fin M),
      envelopeAmplitude M τ =
        envelopeAmplitude M ⟨M - 1 - τ.val, by omega⟩) ∧
    (∀ (M : ℕ) (ψ χ : QState (Fin M)) {δ : ℝ}, 0 ≤ δ →
      (∀ τ, ‖χ τ - ψ τ‖ ≤ δ) →
      Real.sqrt (∑ τ : Fin M, ‖χ τ - ψ τ‖ ^ 2) ≤ Real.sqrt (M : ℝ) * δ) ∧
    (∀ (M k : ℕ),
      totalAngleBits M k ≤ (M.log2 + 1) * (k + M.log2 + 2)) ∧
    (∀ (M : ℕ), bisectionStages M = M.log2 + 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M hM τ
    exact envelopeAmplitude_symmetry M hM τ
  · intro M ψ χ δ hδ h
    exact amplitude_perturbation_l2 M ψ χ hδ h
  · intro M k
    exact totalAngleBits_poly M k
  · intro M
    exact emitter_stage_count M

/-- Collects monotonicity of the source runtime scale in preparation cost and inverse precision,
together with the lower bound one for the synthesis access factor. -/
theorem clause4_endpoint :
    (∀ (κ T_B T_B' s logN epsInv : ℕ), T_B ≤ T_B' →
      qlsSourceScale κ T_B s logN epsInv ≤ qlsSourceScale κ T_B' s logN epsInv) ∧
    (∀ (κ T_B s logN epsInv epsInv' : ℕ), epsInv ≤ epsInv' →
      qlsSourceScale κ T_B s logN epsInv ≤ qlsSourceScale κ T_B s logN epsInv') ∧
    (∀ (M k : ℕ), qlsSynthAccessFactor M k ≥ 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro κ T_B T_B' s logN epsInv h
    exact qlsSourceScale_mono_prep κ T_B T_B' s logN epsInv h
  · intro κ T_B s logN epsInv epsInv' h
    exact qlsSourceScale_mono_eps κ T_B s logN epsInv epsInv' h
  · intro M k
    exact qlsSynthAccessCorrection_bound M k

/-- Combines the lower bound one for the synthesis access factor with the explicit formula for
the source runtime scale. -/
theorem clause54_endpoint :
    (∀ (M k : ℕ), qlsSynthAccessFactor M k ≥ 1) ∧
    (∀ (κ T_B s logN epsInv : ℕ),
      qlsSourceScale κ T_B s logN epsInv = κ * T_B + κ ^ 2 * s ^ 2 * logN * epsInv) := by
  refine ⟨?_, ?_⟩
  · intro M k
    exact qlsSynthAccessCorrection_bound M k
  · intro κ T_B s logN epsInv
    rfl

/-- Collects the birthday-scale bound, the reduced Simon exponent identity, and the strict
exponential comparison when `3 * α + 4 * β < 1 / 2`. -/
theorem clause6_endpoint :
    (∀ n : ℕ, 2 ^ (n / 2) ≤ simonBirthdayBound n) ∧
    (∀ α β n : ℝ, simonReducedExponent α β n = (3 * α + 4 * β) * n) ∧
    (∀ (α β n : ℝ), 3 * α + 4 * β < 1 / 2 → 0 < n →
      Real.exp ((simonReducedExponent α β n) * Real.log 2)
        < Real.exp (((1 / 2 : ℝ) * n) * Real.log 2)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact simonBirthdayBound_ge n
  · intro α β n
    exact simonReducedExponent_eq α β n
  · intro α β n h hn
    exact simon_reduction_below_birthday α β n h hn

end Qatlib.Papers.LinearSystems09.InputModel.QlsHhl
