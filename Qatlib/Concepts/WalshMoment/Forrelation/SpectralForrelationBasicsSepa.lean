/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalshMoment.Forrelation.SpectralForrelationBasicsStat
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm

/-!
# Bounds and optimal witnesses for spectral forrelation

This module proves that spectral forrelation lies in `[0, 1]`, bounds every normalized witness
mass by it, and constructs a normalized witness attaining that bound. The proof combines
contraction bounds for characteristic projectors and the Hadamard transform with compactness of
the finite-dimensional unit sphere. It also proves that an identically false predicate on either
side makes spectral forrelation zero.

The operator-norm interpretation of quantum states and transformations is standard in
[Watrous2018].

## Key declarations

* `charProjector_norm_le_one` and `forrMatrix_norm_le_one` establish the contraction bounds.
* `forrWitnessMass_le_spectral` gives the upper bound for normalized witnesses.
* `spectral_attained` supplies an optimal normalized witness.
* `spectralForrelationBasics` assembles the full specification.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option warningAsError false

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.WalshMoment.Forrelation

namespace Qatlib.Concepts.WalshMoment.Forrelation.SpectralForrelationBasicsSepa

open Matrix

open scoped Matrix.Norms.L2Operator

/-- The characteristic projector of any Boolean predicate has Euclidean operator norm at most
one. -/
private theorem charProjector_norm_le_one (n : ℕ) (f : Reg n → Bool) :
    ‖charProjector n f‖ ≤ 1 := by
  rw [charProjector, Matrix.l2_opNorm_diagonal, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  by_cases h : f i
  · simp only [if_pos h]
    norm_num
  · simp only [if_neg h]
    norm_num

/-- The product `charProjector n U * HadamardN n * charProjector n S` has Euclidean operator
norm at most one. -/
private theorem forrMatrix_norm_le_one (n : ℕ) (S U : Reg n → Bool) :
    ‖charProjector n U * HadamardN n * charProjector n S‖ ≤ 1 := by
  have h1 := Matrix.l2_opNorm_mul (charProjector n U * HadamardN n) (charProjector n S)
  have h2 := Matrix.l2_opNorm_mul (charProjector n U) (HadamardN n)
  rw [Qatlib.Concepts.ReferenceError.RefTraceError.l2_norm_unitary_eq_one (hadamardN_unitary n)] at h2
  have h3 : (0 : ℝ) ≤ ‖charProjector n U * HadamardN n‖ := norm_nonneg _
  have h4 : (0 : ℝ) ≤ ‖charProjector n U‖ := norm_nonneg _
  have h5 : (0 : ℝ) ≤ ‖charProjector n S‖ := norm_nonneg _
  have h6 := charProjector_norm_le_one n U
  have h7 := charProjector_norm_le_one n S
  nlinarith

/-- The witness mass of any normalized state is at most the spectral forrelation value. -/
private theorem forrWitnessMass_le_spectral (n : ℕ) (S U : Reg n → Bool)
    (ψ : QState (Reg n)) (hψ : Normalized ψ) :
    forrWitnessMass n S U ψ ≤ spectralForrelation n S U := by
  have h1 := l2_norm_mulVec_fromVec_le
    (charProjector n U * HadamardN n * charProjector n S) ψ
  rw [(normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ, mul_one] at h1
  have h2 : (0 : ℝ) ≤ ‖toEuclidean_fromVec
      ((charProjector n U * HadamardN n * charProjector n S).mulVec ψ)‖ := norm_nonneg _
  have h3 : (0 : ℝ) ≤ ‖charProjector n U * HadamardN n * charProjector n S‖ := norm_nonneg _
  unfold forrWitnessMass spectralForrelation
  nlinarith

/-- There exists a normalized witness whose mass is at least the spectral forrelation value.
Together with the upper bound for normalized witnesses, this gives attainment of that value. -/
private theorem spectral_attained (n : ℕ) (S U : Reg n → Bool) :
    ∃ ψ : QState (Reg n), Normalized ψ ∧
      spectralForrelation n S U ≤ forrWitnessMass n S U ψ := by
  classical
  set M : EuclideanSpace ℂ (Reg n) →L[ℂ] EuclideanSpace ℂ (Reg n) :=
    ((Matrix.toEuclideanCLM (𝕜 := ℂ) : Matrix (Reg n) (Reg n) ℂ ≃⋆ₐ[ℂ]
      (EuclideanSpace ℂ (Reg n) →L[ℂ] EuclideanSpace ℂ (Reg n))))
      (charProjector n U * HadamardN n * charProjector n S) with hM
  set f : EuclideanSpace ℂ (Reg n) → ℝ := fun x => ‖M x‖ ^ 2 with hf
  have hcont : ContinuousOn f (Metric.sphere (0 : EuclideanSpace ℂ (Reg n)) 1) :=
    ((M.continuous.norm).pow 2).continuousOn
  have hcomp : IsCompact (Metric.sphere (0 : EuclideanSpace ℂ (Reg n)) 1) :=
    isCompact_sphere 0 1
  have hvpos : (0 : ℝ) < ‖toEuclidean_fromVec (fun _ : Reg n => (1 : ℂ))‖ := by
    have h1 : ‖toEuclidean_fromVec (fun _ : Reg n => (1 : ℂ))‖ ^ 2
        = ∑ x : Reg n, ‖(1 : ℂ)‖ ^ 2 := norm_toEuclidean_fromVec_sq _
    have h2 : (0 : ℝ) < ∑ x : Reg n, ‖(1 : ℂ)‖ ^ 2 :=
      Finset.sum_pos (fun x _ => by norm_num) (Finset.univ_nonempty)
    have h3 : (0 : ℝ) ≤ ‖toEuclidean_fromVec (fun _ : Reg n => (1 : ℂ))‖ := norm_nonneg _
    nlinarith
  have hmem0 : ‖toEuclidean_fromVec (fun _ : Reg n => (1 : ℂ))‖⁻¹ •
      toEuclidean_fromVec (fun _ : Reg n => (1 : ℂ)) ∈
      Metric.sphere (0 : EuclideanSpace ℂ (Reg n)) 1 := by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      _root_.abs_of_nonneg (le_of_lt (inv_pos.mpr hvpos)),
      inv_mul_cancel₀ (ne_of_gt hvpos)]
  obtain ⟨x₀, hx₀, hmax⟩ :=
    hcomp.exists_isMaxOn ⟨_, hmem0⟩ hcont
  refine ⟨toVec_fromEuclidean x₀, ?_, ?_⟩
  · rw [normalized_iff_norm_toEuclidean_fromVec,
      toEuclidean_fromVec_toVec_fromEuclidean x₀]
    have h1 := Metric.mem_sphere.mp hx₀
    rw [dist_zero_right] at h1
    exact h1
  · have hmass : forrWitnessMass n S U (toVec_fromEuclidean x₀) = f x₀ := by
      have hap := toEuclideanCLM_applyGate
        (charProjector n U * HadamardN n * charProjector n S) (toVec_fromEuclidean x₀)
      rw [toEuclidean_fromVec_toVec_fromEuclidean x₀] at hap
      unfold forrWitnessMass
      rw [show (charProjector n U * HadamardN n * charProjector n S).mulVec
          (toVec_fromEuclidean x₀) = ApplyGate (charProjector n U * HadamardN n *
            charProjector n S) (toVec_fromEuclidean x₀) from rfl, ← hap]
    have hC : (0 : ℝ) ≤ ‖M x₀‖ := norm_nonneg _
    have hbnd : ∀ x : EuclideanSpace ℂ (Reg n), ‖M x‖ ≤ ‖M x₀‖ * ‖x‖ := by
      intro x
      by_cases hx : x = 0
      · rw [hx, map_zero, norm_zero]
        simp
      · have hxn : (0 : ℝ) < ‖x‖ := by
          have hn : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
          rcases lt_or_eq_of_le hn with h | h
          · exact h
          · exact absurd (norm_eq_zero.mp h.symm) hx
        have hmem : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : EuclideanSpace ℂ (Reg n)) 1 := by
          rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
            _root_.abs_of_nonneg (le_of_lt (inv_pos.mpr hxn)),
            inv_mul_cancel₀ (ne_of_gt hxn)]
        have h1 : f (‖x‖⁻¹ • x) ≤ f x₀ := hmax hmem
        rw [hf] at h1
        have h2 : (0 : ℝ) ≤ ‖M (‖x‖⁻¹ • x)‖ := norm_nonneg _
        have h3 : ‖M (‖x‖⁻¹ • x)‖ ≤ ‖M x₀‖ := by nlinarith
        have hms : M (‖x‖⁻¹ • x) = ((‖x‖⁻¹ : ℝ) : ℂ) • M x := by
          have h1 : M (‖x‖⁻¹ • x) = M (((‖x‖⁻¹ : ℝ) : ℂ) • x) := by congr 1
          rw [h1, M.map_smul]
        rw [hms, norm_smul] at h3
        have hco : ‖((‖x‖⁻¹ : ℝ) : ℂ)‖ = ‖x‖⁻¹ := by simp
        rw [hco] at h3
        have hrw : ‖x‖ * ‖x‖⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hxn)
        have h5 : ‖x‖ * (‖x‖⁻¹ * ‖M x‖) ≤ ‖x‖ * ‖M x₀‖ :=
          mul_le_mul_of_nonneg_left h3 hxn.le
        rw [← mul_assoc, hrw, one_mul] at h5
        exact h5.trans (le_of_eq (mul_comm _ _))
    have hnorm : ‖M‖ ≤ ‖M x₀‖ := ContinuousLinearMap.opNorm_le_bound M hC hbnd
    have hAn : (0 : ℝ) ≤ ‖M‖ := norm_nonneg _
    have hA : ‖charProjector n U * HadamardN n * charProjector n S‖ = ‖M‖ := by
      rw [Matrix.cstar_norm_def]
    rw [hmass, spectralForrelation, hA]
    simp only [hf]
    nlinarith

/-- Spectral forrelation lies in `[0, 1]`, bounds all normalized witness masses, and has a
normalized witness meeting any target at most that value. It vanishes if either oracle
predicate is identically false. -/
theorem spectralForrelationBasics : SpectralForrelationBasics := by
  intro n S U
  refine ⟨sq_nonneg _, ?_, fun ψ hψ => forrWitnessMass_le_spectral n S U ψ hψ,
    fun α hα => (spectral_attained n S U).imp fun ψ hψ => ⟨hψ.1, hα.trans hψ.2⟩,
    ?_, ?_⟩
  · unfold spectralForrelation
    have h := forrMatrix_norm_le_one n S U
    have hn : (0 : ℝ) ≤ ‖charProjector n U * HadamardN n * charProjector n S‖ :=
      norm_nonneg _
    nlinarith
  · intro hS
    have hzero : charProjector n (fun _ => false) = 0 := by
      ext x y
      simp [charProjector]
    rw [spectralForrelation, hS, hzero]
    norm_num
  · intro hU
    have hzero : charProjector n (fun _ => false) = 0 := by
      ext x y
      simp [charProjector]
    rw [spectralForrelation, hU, hzero]
    norm_num

end Qatlib.Concepts.WalshMoment.Forrelation.SpectralForrelationBasicsSepa
