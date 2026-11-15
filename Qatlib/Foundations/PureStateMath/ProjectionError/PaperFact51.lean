/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
public import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

set_option autoImplicit false
namespace Qatlib.Foundations.PureStateMath.ProjectionError
open Matrix

/-- Shows that an orthogonal projector contracts the Euclidean norm. -/
private theorem projector_contractive
    {I : Type*} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℂ) (hP : IsOrthogonalProjector P) (v : QState I) :
    ‖toEuclidean_fromVec (P *ᵥ v)‖ ≤ ‖toEuclidean_fromVec v‖ := by
  have hm := projectiveBranchMass_add hP v
  have hn (w : QState I) : MeasureProb w Finset.univ = ‖toEuclidean_fromVec w‖ ^ 2 := by
    simpa only [MeasureProb, BornProb] using (norm_toEuclidean_fromVec_sq w).symm
  change MeasureProb ((1 - P) *ᵥ v) Finset.univ +
    MeasureProb (P *ᵥ v) Finset.univ = MeasureProb v Finset.univ at hm
  rw [hn, hn, hn] at hm
  nlinarith [sq_nonneg ‖toEuclidean_fromVec ((1 - P) *ᵥ v)‖,
    norm_nonneg (toEuclidean_fromVec v), norm_nonneg (toEuclidean_fromVec (P *ᵥ v))]

/-- Chooses a unit complex phase that rotates a complex number to have real part equal to its
norm. -/
private theorem aligned_phase (c : ℂ) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ (star z * c).re = ‖c‖ := by
  by_cases hc : c = 0
  · subst c
    exact ⟨1, by simp, by simp⟩
  · have hr : 0 < ‖c‖ := norm_pos_iff.mpr hc
    refine ⟨c / (‖c‖ : ℂ), ?_, ?_⟩
    · simp [Complex.norm_real, hr.ne']
    · rw [star_div₀, Complex.star_def, Complex.conj_ofReal, div_mul_eq_mul_div,
        ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      simp [pow_two, hr.ne']

/-- Bounds the squared difference of projected amplitudes of normalized states by twice their
infidelity. -/
theorem fact51_amplitude_error_sq_le_infidelity
    {I : Type*} [Fintype I] [DecidableEq I]
    (P : Matrix I I ℂ) (hP : IsOrthogonalProjector P)
    (ψ χ : QState I) (hψ : Normalized ψ) (hχ : Normalized χ) :
    |‖toEuclidean_fromVec (P *ᵥ ψ)‖ - ‖toEuclidean_fromVec (P *ᵥ χ)‖| ^ 2 ≤
      2 * (1 - Complex.normSq (Inner ψ χ)) := by
  let x := toEuclidean_fromVec ψ
  let y := toEuclidean_fromVec χ
  have hx : ‖x‖ = 1 := (normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ
  have hy : ‖y‖ = 1 := (normalized_iff_norm_toEuclidean_fromVec χ).mp hχ
  have hc : inner ℂ x y = Inner ψ χ := inner_euclidean_fromVec ψ χ
  obtain ⟨z, hz, halign⟩ := aligned_phase (inner ℂ x y)
  have hzn : ‖z • x‖ = 1 := by rw [norm_smul, hz, hx, one_mul]
  have hi : (inner ℂ (z • x) y).re = ‖inner ℂ x y‖ := by
    simpa only [inner_smul_left] using! halign
  have hdist : ‖z • x - y‖ ^ 2 = 2 - 2 * ‖inner ℂ x y‖ := by
    rw [norm_sub_sq (𝕜 := ℂ), hzn, hy]
    change 1 ^ 2 - 2 * (inner ℂ (z • x) y).re + 1 ^ 2 = _
    rw [hi]
    ring
  have hwrap : toEuclidean_fromVec (z • ψ - χ) = z • x - y := rfl
  have hpz : ‖toEuclidean_fromVec (P *ᵥ (z • ψ))‖ =
      ‖toEuclidean_fromVec (P *ᵥ ψ)‖ := by
    rw [Matrix.mulVec_smul]
    change ‖z • toEuclidean_fromVec (P *ᵥ ψ)‖ = _
    rw [norm_smul, hz, one_mul]
  have herr : |‖toEuclidean_fromVec (P *ᵥ ψ)‖ - ‖toEuclidean_fromVec (P *ᵥ χ)‖| ≤
      ‖z • x - y‖ := by
    rw [← hpz]
    calc
      _ ≤ ‖toEuclidean_fromVec (P *ᵥ (z • ψ)) - toEuclidean_fromVec (P *ᵥ χ)‖ :=
        abs_norm_sub_norm_le _ _
      _ = ‖toEuclidean_fromVec (P *ᵥ (z • ψ - χ))‖ := by
        rw [Matrix.mulVec_sub]
        rfl
      _ ≤ ‖toEuclidean_fromVec (z • ψ - χ)‖ := projector_contractive P hP _
      _ = ‖z • x - y‖ := congrArg norm hwrap
  have hcs : ‖inner ℂ x y‖ ≤ 1 := by
    simpa only [hx, hy, one_mul] using norm_inner_le_norm x y
  have hsq := mul_self_le_mul_self (abs_nonneg _) herr
  rw [← pow_two, ← pow_two, hdist] at hsq
  rw [Complex.normSq_eq_norm_sq, ← hc]
  nlinarith [norm_nonneg (inner ℂ x y)]

end Qatlib.Foundations.PureStateMath.ProjectionError
