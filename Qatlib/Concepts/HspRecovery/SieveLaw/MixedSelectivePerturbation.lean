/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.ReferenceError.DensityToRaw.ChannelTraceContraction
import Qatlib.Concepts.ReferenceError.RefTraceError.FiniteReferenceTraceError
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ReferenceError.RefTraceError

namespace Qatlib.Concepts.HspRecovery.SieveLaw

open Matrix
open scoped Classical BigOperators ComplexOrder Matrix.Norms.L2Operator

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable def selectiveMap {O : Type} [Fintype O] {D E : ℕ}
    (J : Instrument O D E) (S : Finset O) : Operator D →ₗ[ℂ] Operator E :=
  ∑ o ∈ S, J.branch o

noncomputable def normalizedPositiveBranch {I : Type} [Fintype I]
    (σ : Matrix I I ℂ) : Matrix I I ℂ :=
  if 0 < (Matrix.trace σ).re then (((Matrix.trace σ).re)⁻¹ : ℂ) • σ else 0

theorem selectiveMap_cp {O : Type} [Fintype O] {D E : ℕ}
    (J : Instrument O D E) (S : Finset O) :
    CompletelyPositive (selectiveMap J S) :=
  CompletelyPositive.sum fun o _ => J.cp o

theorem selectiveMap_tni {O : Type} [Fintype O] {D E : ℕ}
    (J : Instrument O D E) (S : Finset O) :
    TraceNonIncreasing (selectiveMap J S) := by
  intro A hA
  have hsum : Matrix.trace ((selectiveMap J S) A)
      = ∑ o ∈ S, Matrix.trace (J.branch o A) := by
    simp only [selectiveMap, LinearMap.sum_apply, Matrix.trace_sum]
  calc (Matrix.trace ((selectiveMap J S) A)).re
      = ∑ o ∈ S, instrumentProb J A o := by
          rw [hsum, Complex.re_sum]
          rfl
    _ ≤ ∑ o : O, instrumentProb J A o :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          (fun o _ _ => instrumentProb_nonneg J hA o)
    _ = (Matrix.trace A).re := sum_instrumentProb J A

private theorem tensorLeft_finset_sum {O : Type} [Fintype O] {D E R : ℕ}
    (T : O → (Operator D →ₗ[ℂ] Operator E)) (S : Finset O)
    (ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ) :
    tensorLeft (∑ o ∈ S, T o) ρ = ∑ o ∈ S, tensorLeft (T o) ρ := by
  ext x y
  simp [tensorLeft, Matrix.sum_apply, LinearMap.sum_apply]

theorem selectiveMap_tensorLeft_tni {O : Type} [Fintype O] {D E R : ℕ}
    (J : Instrument O D E) (S : Finset O)
    {ρ : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ} (hρ : ρ.PosSemidef) :
    (Matrix.trace (tensorLeft (selectiveMap J S) ρ)).re ≤ (Matrix.trace ρ).re := by
  have hsum : Matrix.trace (tensorLeft (selectiveMap J S) ρ)
      = ∑ o ∈ S, Matrix.trace (tensorLeft (J.branch o) ρ) := by
    simp only [selectiveMap, tensorLeft_finset_sum, Matrix.trace_sum]
  have hnonneg : ∀ o : O, 0 ≤ (Matrix.trace (tensorLeft (J.branch o) ρ)).re :=
    fun o => (RCLike.nonneg_iff.mp (tensorLeft_posSemidef (J.cp o) hρ).trace_nonneg).1
  have htotal : ∑ o : O, (Matrix.trace (tensorLeft (J.branch o) ρ)).re
      = (Matrix.trace ρ).re := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, J.tensorLeft_total ρ]
  calc (Matrix.trace (tensorLeft (selectiveMap J S) ρ)).re
      = ∑ o ∈ S, (Matrix.trace (tensorLeft (J.branch o) ρ)).re := by
          rw [hsum, Complex.re_sum]
    _ ≤ ∑ o : O, (Matrix.trace (tensorLeft (J.branch o) ρ)).re :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          (fun o _ _ => hnonneg o)
    _ = (Matrix.trace ρ).re := htotal

theorem posSemidef_traceNorm_eq_re {I : Type} [Fintype I] {M : Matrix I I ℂ}
    (hM : M.PosSemidef) : Matrix.traceNorm M = (Matrix.trace M).re := by
  have hc : ((Matrix.traceNorm M : ℂ)) = Matrix.trace M := hM.traceNorm_eq_trace
  simpa using congrArg Complex.re hc

private theorem selective_posPart_posSemidef {n : Type} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.posPart hA).PosSemidef := by
  refine (Matrix.posSemidef_diagonal_iff.mpr ?_).mul_mul_conjTranspose_same _
  intro i
  exact RCLike.ofReal_nonneg.mpr (le_max_right (hA.eigenvalues i) 0)

private theorem selective_negPart_posSemidef {n : Type} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.negPart hA).PosSemidef := by
  refine (Matrix.posSemidef_diagonal_iff.mpr ?_).mul_mul_conjTranspose_same _
  intro i
  exact RCLike.ofReal_nonneg.mpr (le_max_right (-hA.eigenvalues i) 0)

private theorem selectiveMap_tensorLeft_posSemidef_norm
    {O : Type} [Fintype O] {D E R : ℕ} (J : Instrument O D E) (S : Finset O)
    {M : Matrix (Fin D × Fin R) (Fin D × Fin R) ℂ} (hM : M.PosSemidef) :
    Matrix.traceNorm (tensorLeft (selectiveMap J S) M) ≤ Matrix.traceNorm M := by
  rw [posSemidef_traceNorm_eq_re (tensorLeft_posSemidef (selectiveMap_cp J S) hM),
    posSemidef_traceNorm_eq_re hM]
  exact selectiveMap_tensorLeft_tni J S hM

theorem selectiveMap_reference_contraction {O : Type} [Fintype O] {D E : ℕ}
    (J : Instrument O D E) (S : Finset O) :
    ∀ (r : ℕ) (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ),
      X.IsHermitian → Matrix.traceNorm (tensorLeft (selectiveMap J S) X) ≤ Matrix.traceNorm X := by
  intro r X hX
  have hpos :
      (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.posPart hX).PosSemidef :=
      selective_posPart_posSemidef hX
  have hneg :
      (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.negPart hX).PosSemidef :=
      selective_negPart_posSemidef hX
  have hsplit : tensorLeft (selectiveMap J S) X
      = tensorLeft (selectiveMap J S) (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.posPart hX)
        - tensorLeft (selectiveMap J S) (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.negPart hX) := by
    rw [← tensorLeft_sub,
        Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.sub_posPart_negPart hX]
  have h1 := Matrix.traceNorm_add_le
    (tensorLeft (selectiveMap J S) (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.posPart hX))
    (-(tensorLeft (selectiveMap J S) (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.negPart hX)))
  rw [Matrix.traceNorm_neg, ← sub_eq_add_neg] at h1
  rw [hsplit]
  calc Matrix.traceNorm (tensorLeft (selectiveMap J S)
        (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.posPart hX)
        - tensorLeft (selectiveMap J S) (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.negPart hX))
      ≤ Matrix.traceNorm (tensorLeft (selectiveMap J S) (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.posPart hX))
        + Matrix.traceNorm (tensorLeft (selectiveMap J S) (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.negPart hX)) := h1
    _ ≤ (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.posPart hX).traceNorm
        + (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.negPart hX).traceNorm :=
          add_le_add (selectiveMap_tensorLeft_posSemidef_norm J S hpos)
            (selectiveMap_tensorLeft_posSemidef_norm J S hneg)
    _ = Matrix.traceNorm X := (Qatlib.Concepts.ReferenceError.DensityToRaw.HermitianSplit.traceNorm_sub_posPart_negPart hX).symm

theorem selective_instrument_cp_tni_reference_contraction :
    ∀ (O : Type) [Fintype O] (D E : ℕ) (J : Instrument O D E) (S : Finset O),
    CompletelyPositive (selectiveMap J S) ∧ TraceNonIncreasing (selectiveMap J S) ∧
    (∀ r : ℕ, ∀ X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ,
      X.IsHermitian → Matrix.traceNorm (tensorLeft (selectiveMap J S) X) ≤ Matrix.traceNorm X) := by
  intro O _ D E J S
  exact ⟨selectiveMap_cp J S, selectiveMap_tni J S, selectiveMap_reference_contraction J S⟩

theorem positive_selected_output_mass_and_normalization_stability :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (σ τ : Matrix I I ℂ) (η : ℝ),
    σ.PosSemidef → τ.PosSemidef → 0 ≤ η → Matrix.traceNorm (σ-τ) ≤ η →
    |(Matrix.trace σ).re - (Matrix.trace τ).re| ≤ η ∧
    ((Matrix.trace σ).re = 0 → normalizedPositiveBranch σ = 0) ∧
    (η < (Matrix.trace τ).re →
      0 < (Matrix.trace σ).re ∧
      Matrix.traceNorm (normalizedPositiveBranch σ-normalizedPositiveBranch τ) ≤
        2*η/(Matrix.trace τ).re) := by
  intro I _ _ σ τ η hσ hτ hη hdiff
  have hτre : 0 ≤ (Matrix.trace τ).re := (RCLike.nonneg_iff.mp hτ.trace_nonneg).1
  have hmass : |(Matrix.trace σ).re - (Matrix.trace τ).re| ≤ η := by
    have htr : (Matrix.trace σ).re - (Matrix.trace τ).re
        = (Matrix.trace (σ-τ)).re := by
      rw [Matrix.trace_sub, Complex.sub_re]
    rw [htr]
    exact ((Complex.abs_re_le_norm _).trans (Matrix.abs_trace_le_traceNorm _)).trans hdiff
  refine ⟨hmass, ?_, ?_⟩
  · intro hz
    have him : (Matrix.trace σ).im = 0 := (RCLike.nonneg_iff.mp hσ.trace_nonneg).2
    have hzero : Matrix.trace σ = 0 := Complex.ext hz him
    have hσ0 : σ = 0 := (Matrix.PosSemidef.trace_eq_zero_iff hσ).mp hzero
    subst hσ0
    simp [normalizedPositiveBranch]
  · intro hp
    have hs0 : 0 < (Matrix.trace σ).re := by
      have h2 := (abs_le.mp hmass).1
      linarith
    refine ⟨hs0, ?_⟩
    have hτ0 : 0 < (Matrix.trace τ).re := lt_of_le_of_lt hη hp
    have hns : normalizedPositiveBranch σ
        = (((Matrix.trace σ).re)⁻¹ : ℂ) • σ := by
      rw [normalizedPositiveBranch, if_pos hs0]
    have hnt : normalizedPositiveBranch τ
        = (((Matrix.trace τ).re)⁻¹ : ℂ) • τ := by
      rw [normalizedPositiveBranch, if_pos hτ0]
    have hcoe : (((((Matrix.trace σ).re)⁻¹ - ((Matrix.trace τ).re)⁻¹ : ℝ) : ℂ)) • σ
        = (((Matrix.trace σ).re)⁻¹ : ℂ) • σ - (((Matrix.trace τ).re)⁻¹ : ℂ) • σ := by
      rw [Complex.ofReal_sub, Complex.ofReal_inv, Complex.ofReal_inv, sub_smul]
    have hsplit : normalizedPositiveBranch σ - normalizedPositiveBranch τ
        = (((Matrix.trace τ).re)⁻¹ : ℂ) • (σ - τ)
          + ((((Matrix.trace σ).re)⁻¹ - ((Matrix.trace τ).re)⁻¹ : ℝ) : ℂ) • σ := by
      rw [hns, hnt, smul_sub, hcoe]
      abel
    have hnormσ : Matrix.traceNorm σ = (Matrix.trace σ).re := posSemidef_traceNorm_eq_re hσ
    have h1 : Matrix.traceNorm ((((Matrix.trace τ).re)⁻¹ : ℂ) • (σ - τ))
        ≤ η/(Matrix.trace τ).re := by
      rw [Matrix.traceNorm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hτ0]
      have hconv : ((Matrix.trace τ).re)⁻¹ * Matrix.traceNorm (σ - τ)
          = Matrix.traceNorm (σ - τ)/(Matrix.trace τ).re := by field_simp
      rw [hconv]
      exact div_le_div_of_nonneg_right hdiff (le_of_lt hτ0)
    have h2 : Matrix.traceNorm
        (((((Matrix.trace σ).re)⁻¹ - ((Matrix.trace τ).re)⁻¹ : ℝ) : ℂ) • σ)
        ≤ η/(Matrix.trace τ).re := by
      rw [Matrix.traceNorm_smul, Complex.norm_real, Real.norm_eq_abs, hnormσ]
      have hnz : (Matrix.trace σ).re*(Matrix.trace τ).re ≠ 0 :=
        mul_ne_zero (ne_of_gt hs0) (ne_of_gt hτ0)
      have hsp : ((Matrix.trace σ).re)⁻¹ - ((Matrix.trace τ).re)⁻¹
          = ((Matrix.trace τ).re - (Matrix.trace σ).re)
            /((Matrix.trace σ).re*(Matrix.trace τ).re) := by field_simp
      have habs : |(Matrix.trace τ).re - (Matrix.trace σ).re| ≤ η := by
        rw [abs_sub_comm]
        exact hmass
      have hconv2 : |(Matrix.trace τ).re - (Matrix.trace σ).re|
          /((Matrix.trace σ).re*(Matrix.trace τ).re)*(Matrix.trace σ).re
          = |(Matrix.trace τ).re - (Matrix.trace σ).re|/(Matrix.trace τ).re := by
        field_simp
      rw [hsp, abs_div, abs_of_pos (mul_pos hs0 hτ0), hconv2]
      exact div_le_div_of_nonneg_right habs (le_of_lt hτ0)
    rw [hsplit]
    exact (Matrix.traceNorm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

end Qatlib.Concepts.HspRecovery.SieveLaw
