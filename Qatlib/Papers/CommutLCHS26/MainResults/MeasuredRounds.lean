/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.Postselection
import Qatlib.Foundations.OperatorErrors.OperatorError
import Qatlib.Concepts.HhlAlgorithms.GridExactHHL.GridHHLSolutionOutput

/-!
# Repeated measured rounds

This module describes successive applications of an operator followed by successful range
projections in the setting of [AftabAnTrivisa2026]. The unnormalized `branch`, its `mass`, and
the decoded optional `output` are related to powers of the compressed operator.

The conservation results track first-failure masses, while `output_of_error` transfers an
operator approximation bound to a normalized output guarantee.

## Main statements

* `history_conservation`: conservation of mass across the complete measurement history.
* `output_of_error`: positive success mass and a normalized output error bound.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.MeasuredRounds

open Matrix
open scoped BigOperators Classical Matrix.Norms.L2Operator
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- The unnormalized branch obtained by embedding `ψ` with `R` and retaining the successful
projection after each application of `U`. -/
def branch (U : Matrix H H ℂ) (R : Matrix H I ℂ) : ℕ → QState I → QState H
  | 0, ψ => R *ᵥ ψ
  | n + 1, ψ => ProjectiveBranch (rangeProjector R) true (ApplyGate U (branch U R n ψ))

/-- The total squared norm of the branch surviving `n` measured rounds. -/
def mass (U : Matrix H H ℂ) (R : Matrix H I ℂ) (n : ℕ) (ψ : QState I) : ℝ :=
  MeasureProb (branch U R n ψ) Finset.univ

/-- The mass of the failed projection after applying `U` to the branch surviving `n` rounds. -/
def firstFailure (U : Matrix H H ℂ) (R : Matrix H I ℂ) (n : ℕ) (ψ : QState I) : ℝ :=
  ProjectiveBranchMass (rangeProjector R) false (ApplyGate U (branch U R n ψ))

/-- The surviving branch after decoding by the conjugate transpose of `R`. -/
def decoded (U : Matrix H H ℂ) (R : Matrix H I ℂ) (n : ℕ) (ψ : QState I) : QState I :=
  Rᴴ *ᵥ branch U R n ψ

/-- The conditional normalized state of the decoded branch, when its mass is nonzero. -/
def output (U : Matrix H H ℂ) (R : Matrix H I ℂ) (n : ℕ) (ψ : QState I) : Option (QState I) :=
  ConditionalState (decoded U R n ψ)

/-- The optional state produced by sequentially conditioning on success in each measured round. -/
def selectiveRun (U : Matrix H H ℂ) (R : Matrix H I ℂ) : ℕ → QState I → Option (QState H)
  | 0, ψ => ConditionalState (R *ᵥ ψ)
  | n + 1, ψ => (selectiveRun U R n ψ).bind
      (fun φ => ProjectiveConditionalState (rangeProjector R) true (ApplyGate U φ))

omit [Fintype I] [DecidableEq I] in

/-- Conditioning before applying a gate and selecting a projective outcome gives the same
optional state as directly conditioning the resulting branch. -/
theorem selective_step (U P : Matrix H H ℂ) (x : QState H) :
    (ConditionalState x).bind (fun φ => ProjectiveConditionalState P true (ApplyGate U φ)) =
      ProjectiveConditionalState P true (ApplyGate U x) := by
  by_cases hx : x = 0
  · simp [hx, ProjectiveConditionalState, ProjectiveBranch, ApplyGate]
  · have hn : 0 < ‖stateVector x‖ := norm_pos_iff.mpr
      (fun h => hx ((stateVector_eq_zero_iff x).mp h))
    have he : PostMeasure x Finset.univ = ((‖stateVector x‖⁻¹ : ℝ) : ℂ) • x := by
      rw [postMeasure_univ_eq_smul]
      ext i
      simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
    rw [conditionalState_eq_some_of_ne_zero hx, Option.bind_some, he]
    simp only [ProjectiveConditionalState, ProjectiveBranch, if_true, ApplyGate, Matrix.mulVec_smul]
    exact Qatlib.Concepts.HhlAlgorithms.GridExactHHL.conditionalState_smul (inv_pos.mpr hn) _

omit [DecidableEq I] in

/-- The sequential selective run equals the conditional state of the unnormalized surviving
branch. -/
theorem selectiveRun_eq (U : Matrix H H ℂ) (R : Matrix H I ℂ) (n : ℕ) (ψ : QState I) :
    selectiveRun U R n ψ = ConditionalState (branch U R n ψ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [selectiveRun, ih, selective_step]
    rfl

/-- The branch after `n` rounds is the embedding of the `n`th power of the compressed operator
applied to the input. -/
theorem branch_eq (U : Matrix H H ℂ) (R : Matrix H I ℂ) (n : ℕ) (ψ : QState I) :
    branch U R n ψ = R *ᵥ ((compress R U R) ^ n *ᵥ ψ) := by
  induction n with
  | zero => simp [branch]
  | succ n ih =>
    rw [branch, ih, projectiveBranch_eq_postselection]
    simp only [postselectionVector, pow_succ', Matrix.mulVec_mulVec]

/-- For an isometric embedding, decoding the surviving branch gives the `n`th power of the
compressed operator applied to the input. -/
theorem decoded_eq (U : Matrix H H ℂ) (R : Matrix H I ℂ) (hR : IsIsometry R)
    (n : ℕ) (ψ : QState I) : decoded U R n ψ = (compress R U R) ^ n *ᵥ ψ := by
  rw [decoded, branch_eq, Matrix.mulVec_mulVec, show Rᴴ * R = 1 from hR, Matrix.one_mulVec]

/-- Reembedding the decoded branch recovers the surviving branch when `R` is an isometry. -/
theorem reembed_decoded (U : Matrix H H ℂ) (R : Matrix H I ℂ) (hR : IsIsometry R)
    (n : ℕ) (ψ : QState I) : R *ᵥ decoded U R n ψ = branch U R n ψ := by
  rw [decoded_eq U R hR, branch_eq]

/-- For an isometric embedding, conditioning the surviving branch equals reembedding its
optional decoded output. -/
theorem conditional_branch (U : Matrix H H ℂ) (R : Matrix H I ℂ) (hR : IsIsometry R)
    (n : ℕ) (ψ : QState I) :
    ConditionalState (branch U R n ψ) = (output U R n ψ).map (fun φ => R *ᵥ φ) := by
  rw [← reembed_decoded U R hR, IsIsometry.conditionalState_mulVec hR]
  rfl

/-- For an isometric embedding, the sequential selective run equals the reembedded optional
decoded output. -/
theorem selectiveRun_output (U : Matrix H H ℂ) (R : Matrix H I ℂ) (hR : IsIsometry R)
    (n : ℕ) (ψ : QState I) :
    selectiveRun U R n ψ = (output U R n ψ).map (fun φ => R *ᵥ φ) := by
  rw [selectiveRun_eq, conditional_branch U R hR]

/-- For an isometric embedding, the surviving mass is the squared norm of the compressed
operator power applied to the input. -/
theorem mass_eq (U : Matrix H H ℂ) (R : Matrix H I ℂ) (hR : IsIsometry R)
    (n : ℕ) (ψ : QState I) :
    mass U R n ψ = ‖stateVector ((compress R U R) ^ n *ᵥ ψ)‖ ^ 2 := by
  rw [mass, branch_eq, IsIsometry.measureProb_mulVec hR, stateVector_norm_sq]

omit [DecidableEq I] in

/-- The surviving branch mass is nonnegative. -/
theorem mass_nonneg (U : Matrix H H ℂ) (R : Matrix H I ℂ) (n : ℕ) (ψ : QState I) :
    0 ≤ mass U R n ψ := measureProb_nonneg _ _

omit [DecidableEq I] in

/-- The mass of the first failed projection is nonnegative. -/
theorem firstFailure_nonneg (U : Matrix H H ℂ) (R : Matrix H I ℂ) (n : ℕ) (ψ : QState I) :
    0 ≤ firstFailure U R n ψ := projectiveBranchMass_nonneg _ _ _

/-- For unitary `U` and isometric `R`, the mass before a round splits into its failure mass and
its surviving mass. -/
theorem step_conservation (U : Matrix H H ℂ) (hU : U ∈ unitaryGroup H ℂ)
    (R : Matrix H I ℂ) (hR : IsIsometry R) (n : ℕ) (ψ : QState I) :
    firstFailure U R n ψ + mass U R (n + 1) ψ = mass U R n ψ := by
  have h := projectiveBranchMass_add (rangeProjector_isOrthogonalProjector hR)
    (ApplyGate U (branch U R n ψ))
  rw [measureProb_applyGate_univ hU] at h
  exact h

/-- The surviving mass plus the sum of all earlier first-failure masses equals the initial total
mass for unitary `U` and isometric `R`. -/
theorem history_conservation (U : Matrix H H ℂ) (hU : U ∈ unitaryGroup H ℂ)
    (R : Matrix H I ℂ) (hR : IsIsometry R) (n : ℕ) (ψ : QState I) :
    mass U R n ψ + ∑ j ∈ Finset.range n, firstFailure U R j ψ = MeasureProb ψ Finset.univ := by
  induction n with
  | zero => simp [mass, branch, IsIsometry.measureProb_mulVec hR]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    linarith [step_conservation U hU R hR n ψ]

/-- For a normalized input, unitary `U`, and isometric `R`, the surviving mass lies in `[0, 1]`. -/
theorem mass_mem_Icc (U : Matrix H H ℂ) (hU : U ∈ unitaryGroup H ℂ)
    (R : Matrix H I ℂ) (hR : IsIsometry R) (n : ℕ) (ψ : QState I) (hψ : Normalized ψ) :
    mass U R n ψ ∈ Set.Icc (0 : ℝ) 1 := by
  have h := history_conservation U hU R hR n ψ
  rw [measureProb_univ hψ] at h
  have hn := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range n) => firstFailure_nonneg U R j ψ)
  exact ⟨mass_nonneg U R n ψ, by linarith⟩

/-- If the compressed operator power is within `η ≤ 1` of a unitary, its surviving mass on a
normalized input is at least `(1 - η)²`. -/
theorem mass_lower (U : Matrix H H ℂ) (R : Matrix H I ℂ) (hR : IsIsometry R)
    (n : ℕ) (V : Matrix I I ℂ) (hV : V ∈ unitaryGroup I ℂ) (η : ℝ) (hη : η ≤ 1)
    (he : ‖(compress R U R) ^ n - V‖ ≤ η) (ψ : QState I) (hψ : Normalized ψ) :
    (1 - η) ^ 2 ≤ mass U R n ψ := by
  have hclose := stateVector_mulVec_norm_le ((compress R U R) ^ n - V) ψ
  rw [(normalized_iff_stateVector_norm ψ).mp hψ, mul_one] at hclose
  have hn : ‖stateVector (V *ᵥ ψ)‖ = 1 := by
    rw [IsIsometry.stateVector_norm (show IsIsometry V from hV.1),
      (normalized_iff_stateVector_norm ψ).mp hψ]
  have hd : ‖stateVector ((compress R U R) ^ n *ᵥ ψ) - stateVector (V *ᵥ ψ)‖ ≤ η := by
    simpa only [Matrix.sub_mulVec, stateVector, WithLp.toLp_sub] using hclose.trans he
  have hl := (norm_sub_norm_le (stateVector (V *ᵥ ψ))
    (stateVector ((compress R U R) ^ n *ᵥ ψ))).trans (by simpa only [norm_sub_rev] using hd)
  rw [hn] at hl
  rw [mass_eq U R hR]
  exact pow_le_pow_left₀ (by linarith) (by linarith : 1 - η ≤ _) 2

/-- If the compressed operator power is within `η ≤ 1` of a unitary, the total first-failure
mass is at most `2η`, assuming unitary `U` and isometric `R`. -/
theorem failure_sum_le (U : Matrix H H ℂ) (hU : U ∈ unitaryGroup H ℂ)
    (R : Matrix H I ℂ) (hR : IsIsometry R) (n : ℕ) (V : Matrix I I ℂ)
    (hV : V ∈ unitaryGroup I ℂ) (η : ℝ) (hη : η ≤ 1)
    (he : ‖(compress R U R) ^ n - V‖ ≤ η) (ψ : QState I) (hψ : Normalized ψ) :
    ∑ j ∈ Finset.range n, firstFailure U R j ψ ≤ 2 * η := by
  have hc := history_conservation U hU R hR n ψ
  rw [measureProb_univ hψ] at hc
  have hl := mass_lower U R hR n V hV η hη he ψ hψ
  nlinarith [sq_nonneg η]

/-- If the compressed operator power is within `η < 1` of a unitary, the surviving mass is
positive and the decoded output satisfies `IsNormalizedApplication` with error `2η`. -/
theorem output_of_error (U : Matrix H H ℂ) (R : Matrix H I ℂ) (hR : IsIsometry R)
    (n : ℕ) (V : Matrix I I ℂ) (hV : V ∈ unitaryGroup I ℂ) (η : ℝ) (hη : η < 1)
    (he : ‖(compress R U R) ^ n - V‖ ≤ η) (ψ : QState I) (hψ : Normalized ψ) :
    0 < mass U R n ψ ∧ ∃ φ : QState I,
      output U R n ψ = some φ ∧ IsNormalizedApplication V ψ φ (2 * η) := by
  have hclose := stateVector_mulVec_norm_le ((compress R U R) ^ n - V) ψ
  rw [(normalized_iff_stateVector_norm ψ).mp hψ, mul_one] at hclose
  have hn : ‖stateVector (V *ᵥ ψ)‖ = 1 := by
    rw [IsIsometry.stateVector_norm (show IsIsometry V from hV.1),
      (normalized_iff_stateVector_norm ψ).mp hψ]
  have hd : ‖stateVector ((compress R U R) ^ n *ᵥ ψ) - stateVector (V *ᵥ ψ)‖ ≤ η := by
    simpa only [Matrix.sub_mulVec, stateVector, WithLp.toLp_sub] using hclose.trans he
  obtain ⟨hy, herr⟩ := normalize_error_of_gap hd (by rwa [hn])
  have hv : (compress R U R) ^ n *ᵥ ψ ≠ 0 := by
    intro hz
    apply hy
    rw [hz]
    rfl
  have hp : 0 < mass U R n ψ := by
    have hl := mass_lower U R hR n V hV η hη.le he ψ hψ
    have hs : 0 < (1 - η) ^ 2 := sq_pos_of_pos (by linarith)
    exact hs.trans_le hl
  refine ⟨hp, PostMeasure ((compress R U R) ^ n *ᵥ ψ) Finset.univ, ?_, ?_, ?_, ?_⟩
  · rw [output, decoded_eq U R hR]
    exact conditionalState_eq_some_of_ne_zero hv
  · intro hz
    rw [hz, stateVector, WithLp.toLp_zero, norm_zero] at hn
    norm_num at hn
  · exact normalized_of_conditionalState_eq_some (conditionalState_eq_some_of_ne_zero hv)
  · rw [stateVector_postMeasure_univ]
    simpa only [hn, div_one] using herr

end Qatlib.Papers.CommutLCHS26.MainResults.MeasuredRounds
