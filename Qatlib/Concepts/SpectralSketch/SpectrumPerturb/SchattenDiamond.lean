/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.SchattenDiamondDefs

/-!
# Schatten trace norms and diamond norm bounds

This module relates `schattenPower` at exponent one to the matrix trace norm and proves its
triangle, unitary invariance, adjoint, and dual characterizations. It also exposes finite
dimensional diamond norm stabilization, norm bounds, and attainment, with quantum information
background in [Watrous2018].

## Main statements

* `schattenPower_one`: identifies exponent one with the trace norm.
* `schattenPower_one_dual`: characterizes the trace norm by unitary trace pairings.
* `diamondNorm_attained`: gives a finite maximizing amplification.
* `channel_discrimination_diamond_bound`: bounds amplified output trace norms using the diamond
  norm of a map difference.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.PhaseGeometry.Phase

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Concepts.SpectralSketch.SpectrumPerturb

open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open scoped Classical BigOperators ENNReal Matrix.Norms.L2Operator ComplexOrder MatrixOrder

set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {m k : Type} [Fintype m] [Fintype k]

/-- The submonoid of complex square matrices obtained from the unitary group. -/
noncomputable def unitarySubmonoid (k : Type) [Fintype k] : Submonoid (Matrix k k ℂ) :=
  @Matrix.unitaryGroup k (Classical.decEq k) (inferInstance : Fintype k) ℂ
    Complex.commRing Complex.instStarRing

/-- The Gram matrix `Aᴴ * A` is Hermitian. -/
theorem gram_isHermitian (A : Matrix m k ℂ) : (Aᴴ * A).IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_self A

/-- The trace norm of a rectangular matrix is the sum of the square roots of the eigenvalues of
its Gram matrix. -/
theorem traceNorm_eq_sum_sqrt_gram (A : Matrix m k ℂ) :
    Matrix.traceNorm A =
      ∑ i : k, Real.sqrt ((gram_isHermitian A).eigenvalues i) := by
  have hH : (Aᴴ * A).IsHermitian := gram_isHermitian A
  unfold Matrix.traceNorm
  rw [CFC.sqrt_eq_real_sqrt (Aᴴ * A)
    (Matrix.nonneg_iff_posSemidef.mpr A.posSemidef_conjTranspose_mul_self),
    cfcₙ_eq_cfc, Matrix.IsHermitian.cfc_eq hH, Matrix.IsHermitian.cfc]
  simp [Matrix.trace_mul_comm, Matrix.mul_assoc]

/-- The unified Schatten value at the top exponent equals the imported operator norm endpoint
`schattenTop`. -/
theorem schattenUnified_top (A : Matrix m k ℂ) :
    schattenUnified (⊤ : SchattenExponent) A = Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.schattenTop A := rfl

/-- The unified Schatten value at a finite real exponent `p` equals `schattenPower p`. -/
theorem schattenUnified_some (p : ℝ) (A : Matrix m k ℂ) :
    schattenUnified (WithTop.some p) A = schattenPower p A := rfl

/-- The Schatten power expression is nonnegative for every real exponent. -/
theorem schattenPower_nonneg (p : ℝ) (A : Matrix m k ℂ) : 0 ≤ schattenPower p A := by
  rw [schattenPower]
  refine Real.rpow_nonneg ?_ _
  exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _

/-- For square matrices, `schattenPower` agrees with the imported Schatten expression. -/
theorem schattenPower_eq_frozen_schatten (p : ℝ) (A : Matrix k k ℂ) :
    schattenPower p A = Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.schatten p A := by
  have hH : (Aᴴ * A).IsHermitian := gram_isHermitian A
  have hM : A.conjTranspose * A.conjTransposeᴴ = Aᴴ * A := by
    rw [Matrix.conjTranspose_conjTranspose]
  have hX := Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose
  have heq : hX.eigenvalues = hH.eigenvalues := by
    rw [Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff]
    rw [hM]
  rw [schattenPower, Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.schatten]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [singularValues, heq]

/-- The Schatten power expression at exponent one equals the matrix trace norm. -/
theorem schattenPower_one (A : Matrix m k ℂ) : schattenPower 1 A = Matrix.traceNorm A := by
  rw [schattenPower]
  simp only [inv_one, Real.rpow_one]
  exact (traceNorm_eq_sum_sqrt_gram A).symm

/-- The unified Schatten value at exponent one equals the matrix trace norm. -/
theorem schattenUnified_one (A : Matrix m k ℂ) :
    schattenUnified (WithTop.some 1) A = Matrix.traceNorm A := by
  simp only [schattenUnified]
  exact schattenPower_one A

/-- The Schatten power expression at exponent one agrees with the imported exponent-one Schatten
expression. -/
theorem schattenPower_one_eq_frozen (A : Matrix k k ℂ) :
    schattenPower 1 A = Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.schatten 1 A :=
  schattenPower_eq_frozen_schatten 1 A

/-- The exponent-one Schatten value satisfies the triangle inequality for square matrices. -/
theorem schattenPower_one_add_le [DecidableEq k] (A B : Matrix k k ℂ) :
    schattenPower 1 (A + B) ≤ schattenPower 1 A + schattenPower 1 B := by
  rw [schattenPower_one, schattenPower_one, schattenPower_one]
  exact Matrix.traceNorm_add_le A B

/-- The top-exponent unified Schatten value satisfies the triangle inequality. -/
theorem schattenUnified_top_add_le (A B : Matrix m k ℂ) :
    schattenUnified (⊤ : SchattenExponent) (A + B)
      ≤ schattenUnified (⊤ : SchattenExponent) A
        + schattenUnified (⊤ : SchattenExponent) B := by
  rw [schattenUnified_top, schattenUnified_top, schattenUnified_top]
  unfold Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.schattenTop
  exact norm_add_le _ _

/-- Unitary conjugation preserves the exponent-one Schatten value. -/
theorem schattenPower_one_unitary_conj (U : Matrix k k ℂ) (A : Matrix k k ℂ)
    (hU : U ∈ Matrix.unitaryGroup k ℂ) :
    schattenPower 1 (U * A * Uᴴ) = schattenPower 1 A := by
  rw [schattenPower_one, schattenPower_one]
  exact Matrix.traceNorm_unitary_conj (A := A) (U := ⟨U, hU⟩)

/-- Left and right multiplication by unitary matrices preserves the exponent-one Schatten value. -/
theorem schattenPower_one_unitary_two_sided (U V : Matrix k k ℂ) (A : Matrix k k ℂ)
    (hU : U ∈ Matrix.unitaryGroup k ℂ) (hV : V ∈ Matrix.unitaryGroup k ℂ) :
    schattenPower 1 (U * A * Vᴴ) = schattenPower 1 A := by
  rw [schattenPower_one, schattenPower_one, Matrix.mul_assoc]
  exact (Matrix.traceNorm_isometry_left
    ((Matrix.mem_unitaryGroup_iff_isometry U).mp hU).1).trans
    (Matrix.traceNorm_isometry_right
    ((Matrix.mem_unitaryGroup_iff_isometry V).mp hV).1)

/-- Conjugate transposition preserves the exponent-one Schatten value of a square matrix. -/
theorem schattenPower_one_conjTranspose (A : Matrix k k ℂ) :
    schattenPower 1 Aᴴ = schattenPower 1 A := by
  rw [schattenPower_one, schattenPower_one]
  exact Matrix.traceNorm_conjTranspose A

/-- The exponent-one Schatten value is the greatest real trace pairing `Complex.re ((U.val *
A).trace)` over unitary matrices `U`. -/
theorem schattenPower_one_dual (A : Matrix k k ℂ) :
    IsGreatest {x : ℝ | ∃ U : Matrix.unitaryGroup k ℂ, Complex.re ((U.val * A).trace) = x}
      (schattenPower 1 A) := by
  rw [schattenPower_one]
  exact Matrix.traceNorm_eq_max_re_tr_U A

/-- The Schatten power expression is zero for an empty input index type when `1 ≤ p`. -/
theorem schattenPower_zero_dim (p : ℝ) (A : Matrix m k ℂ) (hp : 1 ≤ p) (h : IsEmpty k) :
    schattenPower p A = 0 := by
  rw [schattenPower]
  letI := h
  have hsum : (∑ i : k, (Real.sqrt ((gram_isHermitian A).eigenvalues i)) ^ p) = 0 :=
    Finset.sum_eq_zero fun i _ => (IsEmpty.false i).elim
  rw [hsum]
  have hp' : 0 < p⁻¹ := inv_pos.mpr (by positivity)
  rw [Real.zero_rpow (ne_of_gt hp')]

/-- Expand the Schatten power expression as the reciprocal-exponent power of the sum of powers
of square roots of Gram eigenvalues. -/
theorem schattenPower_eq_sum_sqrt_gram (p : ℝ) (A : Matrix m k ℂ) :
    schattenPower p A =
      ((∑ i : k, (Real.sqrt ((gram_isHermitian A).eigenvalues i)) ^ p)) ^ (p⁻¹) := rfl

variable {D E F : ℕ}

/-- The diamond norm equals the amplified induced trace norm at the input dimension. -/
theorem diamondNorm_stabilizes (T : Operator D →ₗ[ℂ] Operator E) :
    diamondNorm T = Qatlib.Concepts.SchattenDiamond.DiamondNorm.diamondAtInput T :=
  diamond_input_dimension_stabilization D E T

/-- The diamond norm of a composition is at most the product of the diamond norms. -/
theorem diamondNorm_comp_le (T : Operator D →ₗ[ℂ] Operator E)
    (R : Operator E →ₗ[ℂ] Operator F) :
    diamondNorm (R.comp T) ≤ diamondNorm R * diamondNorm T :=
  (finiteDiamondNorm_algebra D E F T 0 R).2.1

/-- The diamond norm satisfies the triangle inequality. -/
theorem diamondNorm_add_le (T S : Operator D →ₗ[ℂ] Operator E) :
    diamondNorm (T + S) ≤ diamondNorm T + diamondNorm S :=
  (finiteDiamondNorm_algebra D E D T S 0).1

/-- The diamond error between two maps is one half of the diamond norm of their difference. -/
theorem diamondError_half_factor (T S : Operator D →ₗ[ℂ] Operator E) :
    diamondError T S = (1/2 : ℝ≥0∞) * diamondNorm (T - S) := rfl

/-- The diamond norm restricted to Hermitian inputs is at most the unrestricted diamond norm. -/
theorem diamondHermitianNorm_le_diamondNorm (T : Operator D →ₗ[ℂ] Operator E) :
    diamondHermitianNorm T ≤ diamondNorm T := by
  unfold diamondHermitianNorm diamondNorm
  apply iSup_le
  intro r
  apply iSup_le
  intro X
  by_cases hX : X.IsHermitian ∧ Matrix.traceNorm X ≤ 1
  · rw [if_pos hX]
    unfold Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm
    exact le_iSup_of_le r (le_iSup_of_le X (by simp [hX.2]))
  · rw [if_neg hX]
    exact bot_le

/-- The diamond norm can be expressed using all finite reference dimensions with the reference
factor placed on the left. -/
theorem diamondNorm_left_reference (T : Operator D →ₗ[ℂ] Operator E) :
    diamondNorm T =
      ⨆ r : ℕ, ⨆ X : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ,
        if Matrix.traceNorm X ≤ 1 then
          ENNReal.ofReal (Matrix.traceNorm (ChannelAmplification T r X)) else 0 := by
  unfold diamondNorm
  exact Qatlib.Concepts.SchattenDiamond.DiamondNorm.finiteDiamondNorm_left_reference D E T

/-- Swapping the input and reference indices intertwines the two conventions for channel
amplification. -/
theorem diamondNorm_amplification_swap (T : Operator D →ₗ[ℂ] Operator E) (r : ℕ)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    ChannelAmplification T r
        (Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) X) =
      Matrix.reindex (Equiv.prodComm _ _) (Equiv.prodComm _ _) (tensorLeft T X) :=
  diamond_amplification_swap T X

/-- The diamond norm is finite and is attained on a trace norm unit ball at reference dimension
equal to the input dimension. -/
theorem diamondNorm_attained (T : Operator D →ₗ[ℂ] Operator E) :
    diamondNorm T < ⊤ ∧
      ∃ X : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ,
        Matrix.traceNorm X ≤ 1 ∧
        diamondNorm T = ENNReal.ofReal (Matrix.traceNorm (tensorLeft T X)) := by
  obtain ⟨hlt, X, hX, hmax⟩ := diamond_finite_attained_maximum D E T
  refine ⟨hlt, X, hX, ?_⟩
  exact hmax

/-- The amplified output trace norm of `T` is at most that of `S` plus the diamond norm of `T -
S` times the input trace norm. -/
theorem channel_discrimination_diamond_bound (T S : Operator D →ₗ[ℂ] Operator E)
    (r : ℕ) (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    ENNReal.ofReal (Matrix.traceNorm (tensorLeft T X))
      ≤ ENNReal.ofReal (Matrix.traceNorm (tensorLeft S X))
        + diamondNorm (T - S) * ENNReal.ofReal (Matrix.traceNorm X) := by
  have hlin : tensorLeft T X = tensorLeft (T - S) X + tensorLeft S X := by
    rw [← diamond_tensorLeft_add]
    have hsub : (T - S) + S = T := by abel
    rw [hsub]
  have htri : Matrix.traceNorm (tensorLeft T X)
      ≤ Matrix.traceNorm (tensorLeft (T - S) X) + Matrix.traceNorm (tensorLeft S X) := by
    rw [hlin]
    exact Matrix.traceNorm_add_le _ _
  have hbound : ENNReal.ofReal (Matrix.traceNorm (tensorLeft (T - S) X))
      ≤ diamondNorm (T - S) * ENNReal.ofReal (Matrix.traceNorm X) :=
    finiteDiamondNorm_apply (T - S) r X
  have hnonneg : 0 ≤ Matrix.traceNorm (tensorLeft (T - S) X) := Matrix.traceNorm_nonneg _
  have hnonneg2 : 0 ≤ Matrix.traceNorm (tensorLeft S X) := Matrix.traceNorm_nonneg _
  calc
    ENNReal.ofReal (Matrix.traceNorm (tensorLeft T X))
        ≤ ENNReal.ofReal (Matrix.traceNorm (tensorLeft (T - S) X)
            + Matrix.traceNorm (tensorLeft S X)) :=
      ENNReal.ofReal_le_ofReal htri
    _ = ENNReal.ofReal (Matrix.traceNorm (tensorLeft (T - S) X))
        + ENNReal.ofReal (Matrix.traceNorm (tensorLeft S X)) :=
      ENNReal.ofReal_add hnonneg hnonneg2
    _ ≤ (diamondNorm (T - S) * ENNReal.ofReal (Matrix.traceNorm X))
        + ENNReal.ofReal (Matrix.traceNorm (tensorLeft S X)) :=
      add_le_add_left hbound _
    _ = ENNReal.ofReal (Matrix.traceNorm (tensorLeft S X))
        + diamondNorm (T - S) * ENNReal.ofReal (Matrix.traceNorm X) := add_comm _ _

end Qatlib.Concepts.SpectralSketch.SpectrumPerturb
