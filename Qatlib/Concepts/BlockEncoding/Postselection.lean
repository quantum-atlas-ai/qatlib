/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.Basic
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Postselection and error bounds for block encodings

`postselectionVector`, `postselectionProbability`, and `postselectionOutput` describe the
compressed output, its projective branch mass, and its conditional normalized state. The module
relates these constructions to Euclidean norms and proves probability and normalized output
error bounds for approximate block encodings.

The mathematical background is described in [GilyenSuLowWiebe2019].

## Main statements

* `postselectionProbability_eq_norm_sq`: branch mass equals the compressed squared norm.
* `BlockEncoding.postselection_probability_error`: absolute error in the scaled success
  probability.
* `BlockEncoding.postselection_output_of_gap`: positive success and output accuracy under a norm
  gap.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding

namespace Qatlib.Concepts.BlockEncoding.Postselection
open Matrix

section Perturbation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `y` is within `η` of `x` and `η < ‖x‖`, then `y` is nonzero and the normalized vectors
differ by at most `2 * η / ‖x‖`. -/
theorem normalize_error_of_gap {x y : E} {η : ℝ}
    (hclose : ‖y - x‖ ≤ η) (hgap : η < ‖x‖) :
    y ≠ 0 ∧
      ‖NormedSpace.normalize y - NormedSpace.normalize x‖ ≤ 2 * η / ‖x‖ := by
  have hη : 0 ≤ η := (norm_nonneg _).trans hclose
  have hx : 0 < ‖x‖ := lt_of_le_of_lt hη hgap
  have hy : y ≠ 0 := by
    intro hz
    have hbad : ‖x‖ ≤ η := by simpa [hz] using hclose
    exact (not_le_of_gt hgap) hbad
  have hxy : ‖x - y‖ ≤ η := by
    rw [norm_sub_rev]
    exact hclose
  have habs : |‖x‖ - ‖y‖| ≤ η := (abs_norm_sub_norm_le x y).trans hxy
  have hdecomp :
      ‖x‖ • (NormedSpace.normalize y - NormedSpace.normalize x) =
        (y - x) + (‖x‖ - ‖y‖) • NormedSpace.normalize y := by
    rw [smul_sub, sub_smul, NormedSpace.norm_smul_normalize,
      NormedSpace.norm_smul_normalize]
    abel
  have hscaled :
      ‖x‖ * ‖NormedSpace.normalize y - NormedSpace.normalize x‖ ≤ 2 * η := by
    calc
      _ = ‖‖x‖ • (NormedSpace.normalize y - NormedSpace.normalize x)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (norm_nonneg x)]
      _ = ‖(y - x) + (‖x‖ - ‖y‖) • NormedSpace.normalize y‖ :=
        congrArg norm hdecomp
      _ ≤ ‖y - x‖ + ‖(‖x‖ - ‖y‖) • NormedSpace.normalize y‖ := norm_add_le _ _
      _ = ‖y - x‖ + |‖x‖ - ‖y‖| := by
        rw [norm_smul, NormedSpace.norm_normalize hy, Real.norm_eq_abs, mul_one]
      _ ≤ η + η := add_le_add hclose habs
      _ = 2 * η := (two_mul η).symm
  refine ⟨hy, (le_div_iff₀ hx).2 ?_⟩
  simpa only [mul_comm] using hscaled

omit [NormedSpace ℝ E] in

/-- A norm error at most `η` bounds the difference of squared norms by `η * (2 * ‖x‖ + η)`. -/
theorem norm_sq_error {x y : E} {η : ℝ} (hclose : ‖y - x‖ ≤ η) :
    |‖y‖ ^ 2 - ‖x‖ ^ 2| ≤ η * (2 * ‖x‖ + η) := by
  have hη : 0 ≤ η := (norm_nonneg _).trans hclose
  have habs : |‖y‖ - ‖x‖| ≤ η := (abs_norm_sub_norm_le y x).trans hclose
  have hb : ‖y‖ ≤ ‖x‖ + η := by
    have := (le_abs_self (‖y‖ - ‖x‖)).trans habs
    linarith
  calc
    |‖y‖ ^ 2 - ‖x‖ ^ 2| = |‖y‖ - ‖x‖| * (‖y‖ + ‖x‖) := by
      rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact mul_comm _ _
    _ ≤ η * (‖y‖ + ‖x‖) :=
      mul_le_mul_of_nonneg_right habs (add_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ η * (2 * ‖x‖ + η) := mul_le_mul_of_nonneg_left (by linarith) hη
end Perturbation

/-- A state amplitude function viewed as a vector in complex Euclidean space. -/
noncomputable abbrev stateVector {I : Type*} (ψ : QState I) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 ψ

section States
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in

/-- The squared Euclidean norm of a state vector equals its total measurement mass. -/
theorem stateVector_norm_sq (ψ : QState I) :
    ‖stateVector ψ‖ ^ 2 = MeasureProb ψ Finset.univ := by
  simpa [MeasureProb, BornProb, stateVector] using
    (EuclideanSpace.norm_sq_eq (WithLp.toLp 2 ψ : EuclideanSpace ℂ I))

/-- A state is normalized exactly when its Euclidean state vector has norm one. -/
theorem normalized_iff_stateVector_norm (ψ : QState I) :
    Normalized ψ ↔ ‖stateVector ψ‖ = 1 := by
  constructor
  · intro hψ
    have hs : ‖stateVector ψ‖ ^ 2 = 1 := by
      rw [stateVector_norm_sq, measureProb_univ hψ]
    have hn := norm_nonneg (stateVector ψ)
    nlinarith
  · intro hψ
    change MeasureProb ψ Finset.univ = 1
    rw [← stateVector_norm_sq, hψ]
    norm_num

omit [Fintype I] [DecidableEq I] in

/-- The Euclidean state vector is zero exactly when the amplitude function is zero. -/
theorem stateVector_eq_zero_iff (ψ : QState I) : stateVector ψ = 0 ↔ ψ = 0 := by
  constructor
  · intro h
    exact congrArg WithLp.ofLp h
  · intro h
    subst ψ
    rfl

/-- Postmeasurement on the full outcome set scales the state by the inverse of its Euclidean
norm. -/
theorem postMeasure_univ_eq_smul (ψ : QState I) :
    PostMeasure ψ Finset.univ = ‖stateVector ψ‖⁻¹ • ψ := by
  have hs : Real.sqrt (MeasureProb ψ Finset.univ) = ‖stateVector ψ‖ := by
    rw [← stateVector_norm_sq]
    exact Real.sqrt_sq (norm_nonneg _)
  funext i
  simp [PostMeasure, collapse_apply, hs, Complex.real_smul]

/-- Postmeasurement on the full outcome set corresponds to Euclidean normalization. -/
theorem stateVector_postMeasure_univ (ψ : QState I) :
    stateVector (PostMeasure ψ Finset.univ) = NormedSpace.normalize (stateVector ψ) := by
  rw [postMeasure_univ_eq_smul]
  rfl

/-- A nonzero state has conditional state equal to its full-set postmeasurement normalization. -/
theorem conditionalState_eq_some_of_ne_zero {ψ : QState I} (hψ : ψ ≠ 0) :
    ConditionalState ψ = some (PostMeasure ψ Finset.univ) := by
  have hn : 0 < ‖stateVector ψ‖ := norm_pos_iff.mpr fun h => hψ ((stateVector_eq_zero_iff ψ).mp h)
  have hp : 0 < MeasureProb ψ Finset.univ := by
    rw [← stateVector_norm_sq]
    positivity
  simp [ConditionalState, hp]

/-- The conditional state is absent exactly when the amplitude vector is zero. -/
theorem conditionalState_eq_none_iff (ψ : QState I) : ConditionalState ψ = none ↔ ψ = 0 := by
  constructor
  · intro h
    by_contra hn
    rw [conditionalState_eq_some_of_ne_zero hn] at h
    contradiction
  · intro h
    subst ψ
    exact conditionalState_zero
end States

open scoped Matrix.Norms.L2Operator

/-- The Euclidean norm of a matrix output is bounded by the matrix operator norm times the input
norm. -/
theorem stateVector_mulVec_norm_le {I O : Type*} [Fintype I] [Fintype O]
    [DecidableEq I] (A : Matrix O I ℂ) (ψ : QState I) :
    ‖stateVector (A *ᵥ ψ)‖ ≤ ‖A‖ * ‖stateVector ψ‖ :=
  Matrix.l2_opNorm_mulVec A (stateVector ψ)

/-- For a unit input, a contraction within `η` of `B` has output squared norm at least `(‖Bψ‖ -
η)²`, normalized output error at most `2 * η / ‖Bψ‖`, and output norm at most one, provided
`η < ‖Bψ‖`. -/
theorem contractive_mulVec_output_of_gap {I : Type*} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (ψ : QState I) (η : ℝ)
    (hA : ‖A‖ ≤ 1) (herr : ‖A - B‖ ≤ η) (hψ : ‖stateVector ψ‖ = 1)
    (hgap : η < ‖stateVector (B *ᵥ ψ)‖) :
    (‖stateVector (B *ᵥ ψ)‖ - η) ^ 2 ≤ ‖stateVector (A *ᵥ ψ)‖ ^ 2 ∧
      ‖NormedSpace.normalize (stateVector (A *ᵥ ψ)) -
        NormedSpace.normalize (stateVector (B *ᵥ ψ))‖ ≤
          2 * η / ‖stateVector (B *ᵥ ψ)‖ ∧
      ‖stateVector (A *ᵥ ψ)‖ ≤ 1 := by
  have hclose : ‖stateVector (A *ᵥ ψ) - stateVector (B *ᵥ ψ)‖ ≤ η := by
    have hm := stateVector_mulVec_norm_le (A - B) ψ
    rw [hψ, mul_one] at hm
    simpa only [Matrix.sub_mulVec, stateVector, WithLp.toLp_sub] using hm.trans herr
  have hlow : ‖stateVector (B *ᵥ ψ)‖ - η ≤ ‖stateVector (A *ᵥ ψ)‖ := by
    have hn := (norm_sub_norm_le (stateVector (B *ᵥ ψ)) (stateVector (A *ᵥ ψ))).trans
      (by simpa only [norm_sub_rev] using hclose)
    linarith
  refine ⟨pow_le_pow_left₀ (by linarith) hlow 2,
    (normalize_error_of_gap hclose hgap).2, ?_⟩
  exact (stateVector_mulVec_norm_le A ψ).trans (by rw [hψ, mul_one]; exact hA)

/-- The condition that `Aψ` is nonzero and the normalized state `φ` lies within `η` of its
Euclidean normalization. -/
def IsNormalizedApplication {I O : Type*} [Fintype I] [Fintype O]
    (A : Matrix O I ℂ) (ψ : QState I) (φ : QState O) (η : ℝ) : Prop :=
  A *ᵥ ψ ≠ 0 ∧ Normalized φ ∧
    ‖stateVector φ - NormedSpace.normalize (stateVector (A *ᵥ ψ))‖ ≤ η

end Qatlib.Concepts.BlockEncoding.Postselection

namespace Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Matrix
open Qatlib
open scoped Matrix.Norms.L2Operator

section Frame
variable {H I : Type*} [Fintype H] [Fintype I] [DecidableEq I]

/-- An isometric matrix preserves the inner product of state amplitude vectors. -/
theorem IsIsometry.inner_mulVec {V : Matrix H I ℂ} (hV : IsIsometry V)
    (ψ φ : QState I) : Qatlib.Foundations.PureStateMath.Inner (V *ᵥ ψ) (V *ᵥ φ) = Qatlib.Foundations.PureStateMath.Inner ψ φ := by
  have h : Vᴴ * V = 1 := hV
  simp only [Qatlib.Foundations.PureStateMath.Inner]
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, h,
    Matrix.vecMul_one]

variable [DecidableEq H]

/-- An isometric matrix preserves total measurement mass. -/
theorem IsIsometry.measureProb_mulVec {V : Matrix H I ℂ} (hV : IsIsometry V)
    (ψ : QState I) : MeasureProb (V *ᵥ ψ) Finset.univ = MeasureProb ψ Finset.univ := by
  have he := IsIsometry.inner_mulVec hV ψ ψ
  rw [inner_self, inner_self, ← Complex.ofReal_sum, ← Complex.ofReal_sum] at he
  exact Complex.ofReal_injective he

/-- An isometric matrix preserves the Euclidean norm of state vectors. -/
theorem IsIsometry.stateVector_norm {V : Matrix H I ℂ} (hV : IsIsometry V)
    (ψ : QState I) : ‖stateVector (V *ᵥ ψ)‖ = ‖stateVector ψ‖ := by
  have he : ‖stateVector (V *ᵥ ψ)‖ ^ 2 = ‖stateVector ψ‖ ^ 2 := by
    simp only [stateVector_norm_sq, IsIsometry.measureProb_mulVec hV]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he

/-- An isometric matrix sends normalized states to normalized states. -/
theorem IsIsometry.normalized_mulVec {V : Matrix H I ℂ} (hV : IsIsometry V)
    {ψ : QState I} (hψ : Normalized ψ) : Normalized (V *ᵥ ψ) := by
  rw [normalized_iff_stateVector_norm, IsIsometry.stateVector_norm hV]
  exact (normalized_iff_stateVector_norm ψ).mp hψ

/-- Conditional normalization commutes with an isometric matrix, including the zero state. -/
theorem IsIsometry.conditionalState_mulVec {V : Matrix H I ℂ} (hV : IsIsometry V)
    (ψ : QState I) :
    ConditionalState (V *ᵥ ψ) = (ConditionalState ψ).map (fun φ => V *ᵥ φ) := by
  unfold ConditionalState
  rw [IsIsometry.measureProb_mulVec hV]
  split_ifs with hp
  · simp only [Option.map_some, postMeasure_univ_eq_smul, IsIsometry.stateVector_norm hV,
      Matrix.mulVec_smul]
  · rfl
end Frame

section Postselection
variable {H I O : Type*} [Fintype H] [Fintype I] [Fintype O]
  [DecidableEq H] [DecidableEq I] [DecidableEq O]

/-- The unnormalized output obtained by applying the compressed matrix `compress L U R` to the
input state. -/
noncomputable def postselectionVector (U : Matrix H H ℂ) (L : Matrix H O ℂ)
    (R : Matrix H I ℂ) (ψ : QState I) : QState O := compress L U R *ᵥ ψ

/-- The success branch mass for projection onto the range matrix of `L` after embedding with `R`
and applying `U`. -/
noncomputable def postselectionProbability (U : Matrix H H ℂ) (L : Matrix H O ℂ)
    (R : Matrix H I ℂ) (ψ : QState I) : ℝ :=
  ProjectiveBranchMass (rangeProjector L) true (ApplyGate U (R *ᵥ ψ))

/-- The optional normalized conditional state of the compressed output vector. -/
noncomputable def postselectionOutput (U : Matrix H H ℂ) (L : Matrix H O ℂ)
    (R : Matrix H I ℂ) (ψ : QState I) : Option (QState O) :=
  ConditionalState (postselectionVector U L R ψ)

omit [DecidableEq I] [DecidableEq O] in

/-- The successful projective branch is the postselection vector embedded through `L`. -/
theorem projectiveBranch_eq_postselection (U : Matrix H H ℂ) (L : Matrix H O ℂ)
    (R : Matrix H I ℂ) (ψ : QState I) :
    ProjectiveBranch (rangeProjector L) true (ApplyGate U (R *ᵥ ψ)) =
      L *ᵥ postselectionVector U L R ψ := by
  simp only [ProjectiveBranch, if_true, ApplyGate, rangeProjector, postselectionVector,
    compress, Matrix.mulVec_mulVec, Matrix.mul_assoc]

omit [DecidableEq I] in

/-- If `L` is isometric, the postselection probability equals the squared Euclidean norm of the
compressed output. -/
theorem postselectionProbability_eq_norm_sq {L : Matrix H O ℂ} (hL : IsIsometry L)
    (U : Matrix H H ℂ) (R : Matrix H I ℂ) (ψ : QState I) :
    postselectionProbability U L R ψ = ‖stateVector (postselectionVector U L R ψ)‖ ^ 2 := by
  unfold postselectionProbability ProjectiveBranchMass
  rw [projectiveBranch_eq_postselection, IsIsometry.measureProb_mulVec hL, stateVector_norm_sq]

omit [DecidableEq I] in

/-- For an isometric left frame, the projective conditional state is the postselection output
mapped through that frame. -/
theorem projectiveConditionalState_eq_postselection {L : Matrix H O ℂ} (hL : IsIsometry L)
    (U : Matrix H H ℂ) (R : Matrix H I ℂ) (ψ : QState I) :
    ProjectiveConditionalState (rangeProjector L) true (ApplyGate U (R *ᵥ ψ)) =
      (postselectionOutput U L R ψ).map (fun φ => L *ᵥ φ) := by
  unfold ProjectiveConditionalState postselectionOutput
  rw [projectiveBranch_eq_postselection, IsIsometry.conditionalState_mulVec hL]

/-- Unitary evolution between isometric frames gives a postselection probability in `[0, 1]` for
normalized input. -/
theorem postselectionProbability_mem_Icc {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (hL : IsIsometry L) (hR : IsIsometry R) {ψ : QState I} (hψ : Normalized ψ) :
    postselectionProbability U L R ψ ∈ Set.Icc (0 : ℝ) 1 := by
  have hn := normalized_applyGate hU (IsIsometry.normalized_mulVec hR hψ)
  have hsum := projectiveBranchMass_add (rangeProjector_isOrthogonalProjector hL)
    (ApplyGate U (R *ᵥ ψ))
  rw [measureProb_univ hn] at hsum
  have hfalse := projectiveBranchMass_nonneg (rangeProjector L) false
    (ApplyGate U (R *ᵥ ψ))
  refine ⟨projectiveBranchMass_nonneg _ _ _, ?_⟩
  unfold postselectionProbability
  linarith

/-- For normalized input, a block encoding bounds the difference between `Aψ` and the scaled
postselection vector by `ε`. -/
theorem BlockEncoding.postselection_error {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ} {α ε : ℝ}
    (h : BlockEncoding A U L R α ε) {ψ : QState I} (hψ : Normalized ψ) :
    ‖stateVector (A *ᵥ ψ) - α • stateVector (postselectionVector U L R ψ)‖ ≤ ε := by
  have he := stateVector_mulVec_norm_le (A - α • compress L U R) ψ
  rw [(normalized_iff_stateVector_norm ψ).mp hψ, mul_one] at he
  have hb := he.trans h.error_le
  simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, WithLp.toLp_sub, WithLp.toLp_smul,
    postselectionVector, stateVector] using hb

/-- The scaled success probability differs from `‖Aψ‖²` by at most `ε * (2 * ‖Aψ‖ + ε)` on
normalized input. -/
theorem BlockEncoding.postselection_probability_error {A : Matrix O I ℂ}
    {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ} {α ε : ℝ}
    (h : BlockEncoding A U L R α ε) {ψ : QState I} (hψ : Normalized ψ) :
    |α ^ 2 * postselectionProbability U L R ψ - ‖stateVector (A *ᵥ ψ)‖ ^ 2| ≤
      ε * (2 * ‖stateVector (A *ᵥ ψ)‖ + ε) := by
  have he : ‖α • stateVector (postselectionVector U L R ψ) - stateVector (A *ᵥ ψ)‖ ≤ ε := by
    rw [norm_sub_rev]
    exact BlockEncoding.postselection_error h hψ
  have hm := norm_sq_error he
  rw [norm_smul, Real.norm_of_nonneg h.normalization_pos.le, mul_pow,
    ← postselectionProbability_eq_norm_sq h.left_isometry] at hm
  exact hm

/-- If `ε < ‖Aψ‖` on normalized input, postselection has positive probability and returns a
normalized application with error at most `2 * ε / ‖Aψ‖`. -/
theorem BlockEncoding.postselection_output_of_gap {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ} {α ε : ℝ}
    (h : BlockEncoding A U L R α ε) {ψ : QState I} (hψ : Normalized ψ)
    (hgap : ε < ‖stateVector (A *ᵥ ψ)‖) :
    0 < postselectionProbability U L R ψ ∧
      ∃ φ : QState O, postselectionOutput U L R ψ = some φ ∧
        IsNormalizedApplication A ψ φ (2 * ε / ‖stateVector (A *ᵥ ψ)‖) := by
  have he : ‖α • stateVector (postselectionVector U L R ψ) - stateVector (A *ᵥ ψ)‖ ≤ ε := by
    rw [norm_sub_rev]
    exact BlockEncoding.postselection_error h hψ
  obtain ⟨hy, herr⟩ := normalize_error_of_gap he hgap
  have hv : postselectionVector U L R ψ ≠ 0 := by
    intro hz
    apply hy
    simp [hz]
  have ht : A *ᵥ ψ ≠ 0 := by
    intro hz
    have hn : ‖stateVector (A *ᵥ ψ)‖ = 0 := by simp [hz]
    rw [hn] at hgap
    exact (not_lt_of_ge h.error_nonneg) hgap
  have hn : 0 < ‖stateVector (postselectionVector U L R ψ)‖ :=
    norm_pos_iff.mpr fun hz => hv ((stateVector_eq_zero_iff _).mp hz)
  constructor
  · rw [postselectionProbability_eq_norm_sq h.left_isometry]
    positivity
  · refine ⟨PostMeasure (postselectionVector U L R ψ) Finset.univ,
      conditionalState_eq_some_of_ne_zero hv, ht, ?_, ?_⟩
    · exact normalized_of_conditionalState_eq_some (conditionalState_eq_some_of_ne_zero hv)
    · rw [stateVector_postMeasure_univ]
      simpa only [NormedSpace.normalize_smul_of_pos h.normalization_pos] using herr

/-- If `ε ≤ ‖Aψ‖` on normalized input, the success probability is at least `((‖Aψ‖ - ε) / α)²`. -/
theorem BlockEncoding.postselection_probability_lower {A : Matrix O I ℂ}
    {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ} {α ε : ℝ}
    (h : BlockEncoding A U L R α ε) {ψ : QState I} (hψ : Normalized ψ)
    (hgap : ε ≤ ‖stateVector (A *ᵥ ψ)‖) :
    ((‖stateVector (A *ᵥ ψ)‖ - ε) / α) ^ 2 ≤ postselectionProbability U L R ψ := by
  have hr := norm_sub_norm_le (stateVector (A *ᵥ ψ))
    (α • stateVector (postselectionVector U L R ψ))
  have he := BlockEncoding.postselection_error h hψ
  rw [norm_smul, Real.norm_of_nonneg h.normalization_pos.le] at hr
  have hlow : (‖stateVector (A *ᵥ ψ)‖ - ε) / α ≤
      ‖stateVector (postselectionVector U L R ψ)‖ := by
    apply (div_le_iff₀ h.normalization_pos).2
    nlinarith
  rw [postselectionProbability_eq_norm_sq h.left_isometry]
  exact pow_le_pow_left₀ (div_nonneg (sub_nonneg.mpr hgap) h.normalization_pos.le) hlow 2
end Postselection
end Qatlib.Concepts.BlockEncoding.Postselection.Encoding
