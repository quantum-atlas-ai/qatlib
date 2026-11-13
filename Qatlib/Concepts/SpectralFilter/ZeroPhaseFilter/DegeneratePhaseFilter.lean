/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralFilter.PhaseReadout.CountedPhaseReflection
import Qatlib.Concepts.SketchArith.GramAction.PostMeasurePerturbation

/-!
# Filtering degenerate zero-phase subspaces

This module describes repeated phase detection on finite spectral combinations, allowing several
eigenvectors to share phase zero. The product-kernel formulas provide zero-event probability and
branch error estimates for the phase-estimation method of [Kitaev1995].

`spectralTargetState` retains the chosen zero-phase components. A phase gap outside the target
bounds leakage, and a positive target mass gives an error bound after normalization of the
selected branch.

## Main statements

* `degenerate_phase_actual_spectral_packet`: exact detection and zero-branch spectral
  expansions.
* `degenerate_phase_zero_event_and_full_branch_error`: target-mass bounds and unnormalized
  branch error.
* `degenerate_phase_conditional_target_state_error`: normalized branch error for positive target
  mass.

## References

* [Kitaev, 1995][Kitaev1995]
* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SketchArith.GramAction
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

namespace Qatlib.Concepts.SpectralFilter.ZeroPhaseFilter

open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

/-- The state produced by evaluating repeated phase detection on the zero-ancilla embedding of
the input. -/
noncomputable def degenerateDetectionState {I : Type} [Fintype I] [DecidableEq I]
    (W : Matrix I I ℂ) (M k : ℕ) (ψ : QState I) : QState (PhaseReflectionSpace I M k) :=
  ApplyGate (evaluate (parallelOracle (controlOracle W)) (phaseDetectionWord M k))
    (phaseReflectionEmbed M k ψ)

/-- Extract the data amplitudes of the detection state at all-zero phase labels and a false
control bit. -/
noncomputable def degenerateZeroBranch {I : Type} [Fintype I] [DecidableEq I]
    (W : Matrix I I ℂ) (M k : ℕ) (hM : 0 < M) (ψ : QState I) : QState I :=
  fun i => degenerateDetectionState W M k ψ (phaseZeroIndex M k hM, (false, i))

/-- The partial spectral sum retaining exactly the indices in the target set. -/
noncomputable def spectralTargetState {I J : Type} [Fintype J]
    (v : J → QState I) (c : J → ℂ) (T : Finset J) : QState I := ∑ j ∈ T, c j • v j

/-- The zero-ancilla embedding as a complex linear map. -/
noncomputable def degenerateEmbedLinear {I : Type} (M k : ℕ) :
    QState I →ₗ[ℂ] QState (PhaseReflectionSpace I M k) where
  toFun := phaseReflectionEmbed M k
  map_add' := phaseReflectionEmbed_add M k
  map_smul' := phaseReflectionEmbed_smul M k

/-- Matrix application as a complex linear map on data states. -/
noncomputable def degenerateApplyLinear {I : Type} [Fintype I]
    (U : Matrix I I ℂ) : QState I →ₗ[ℂ] QState I where
  toFun := ApplyGate U
  map_add' := Matrix.mulVec_add U
  map_smul' := Matrix.mulVec_smul U

/-- Expand repeated phase detection of a finite eigenvector combination into kernel packets, and
express its zero branch by multiplying each coefficient by the kth zero-label kernel
amplitude. -/
theorem degenerate_phase_actual_spectral_packet
    (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (W : Matrix I I ℂ) (M k : ℕ) (hM : 0 < M)
    (v : J → QState I) (c : J → ℂ) (φ : J → ℝ)
    (he : ∀ j, W *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (φ j : ℂ)) • v j) :
    degenerateDetectionState W M k (∑ j, c j • v j) =
        ∑ j, c j • phaseKernelPacket M k (φ j) (v j) ∧
      degenerateZeroBranch W M k hM (∑ j, c j • v j) =
        ∑ j, (c j * (qpeKernel M (φ j) (⟨0, hM⟩ : Fin M)) ^ k) • v j := by
  have hd : degenerateDetectionState W M k (∑ j, c j • v j) =
      ∑ j, c j • phaseKernelPacket M k (φ j) (v j) := by
    let L := (degenerateApplyLinear (evaluate (parallelOracle (controlOracle W))
      (phaseDetectionWord (I := I) M k))).comp (degenerateEmbedLinear M k)
    change L (∑ j, c j • v j) = _
    rw [map_sum]
    simp only [map_smul]
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (c j • ·) (phaseDetectionWord_eigenstate M k hM W (v j) (φ j) (he j))
  refine ⟨hd, ?_⟩
  funext i
  simp [degenerateZeroBranch, hd, phaseKernelPacket, phaseZeroIndex,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- For a spectral combination, collapse onto the all-zero phase event equals the zero-ancilla
embedding of the extracted zero branch. -/
theorem degenerate_detection_collapse_spectral
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (W : Matrix I I ℂ) (M k : ℕ) (hM : 0 < M)
    (v : J → QState I) (c : J → ℂ) (φ : J → ℝ)
    (he : ∀ j, W *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (φ j : ℂ)) • v j) :
    Collapse (degenerateDetectionState W M k (∑ j, c j • v j)) (phaseZeroEvent M k) =
      phaseReflectionEmbed M k (degenerateZeroBranch W M k hM (∑ j, c j • v j)) := by
  have hd := (degenerate_phase_actual_spectral_packet I J W M k hM v c φ he).1
  funext ⟨x, b, i⟩
  by_cases hx : ∀ j, (x j).val = 0
  · have hxe : x = phaseZeroIndex M k hM := by funext j; exact Fin.ext (hx j)
    subst x
    cases b <;> simp [collapse_apply, phaseZeroEvent, phaseReflectionEmbed,
      phaseZeroIndex, degenerateZeroBranch, hd, phaseKernelPacket]
  · cases b <;> simp [collapse_apply, phaseZeroEvent, phaseReflectionEmbed, hx]

/-- For a spectral combination, the all-zero phase-event probability equals the squared
Euclidean norm of the extracted zero branch. -/
theorem degenerate_detection_mass
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (W : Matrix I I ℂ) (M k : ℕ) (hM : 0 < M)
    (v : J → QState I) (c : J → ℂ) (φ : J → ℝ)
    (he : ∀ j, W *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (φ j : ℂ)) • v j) :
    MeasureProb (degenerateDetectionState W M k (∑ j, c j • v j)) (phaseZeroEvent M k) =
      ‖toEuclidean_fromVec (degenerateZeroBranch W M k hM (∑ j, c j • v j))‖ ^ 2 := by
  rw [← sum_normSq_collapse, ← norm_toEuclidean_fromVec_sq,
    degenerate_detection_collapse_spectral W M k hM v c φ he,
    phaseReflectionEmbed_norm M k hM]

/-- The squared norm of a finite combination of orthonormal states equals the sum of the squared
coefficient norms. -/
theorem degenerate_packet_norm_sq {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (v : J → QState I) (c : J → ℂ)
    (hv : ∀ j l, Inner (v j) (v l) = if j = l then 1 else 0) :
    ‖toEuclidean_fromVec (∑ j, c j • v j)‖ ^ 2 = ∑ j, ‖c j‖ ^ 2 := by
  rw [norm_toEuclidean_fromVec_sq]
  exact sum_norm_sq_orthonormal v c (fun j l => by by_cases h : j = l <;> simpa [h] using hv j l)

/-- The squared norm of the target spectral sum equals its total squared coefficient mass. -/
theorem spectralTargetState_norm_sq {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (v : J → QState I) (c : J → ℂ) (T : Finset J)
    (hv : ∀ j l, Inner (v j) (v l) = if j = l then 1 else 0) :
    ‖toEuclidean_fromVec (spectralTargetState v c T)‖ ^ 2 = ∑ j ∈ T, ‖c j‖ ^ 2 := by
  have ht : spectralTargetState v c T = ∑ j, (if j ∈ T then c j else 0) • v j := by
    simp [spectralTargetState, ite_smul, Finset.sum_ite_mem]
  rw [ht, degenerate_packet_norm_sq v _ hv]
  simp_rw [apply_ite norm, norm_zero, ite_pow]
  simp [Finset.sum_ite_mem]

/-- For a unit coefficient mass and a diagonal filter equal to one on the target and bounded by
`C` elsewhere, bound the filtered squared norm between `a` and `a+C^2*(1-a)` and its target
error by `C*sqrt(1-a)`. -/
theorem degenerate_diagonal_filter_bounds
    {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (v : J → QState I) (c α : J → ℂ) (T : Finset J) (C : ℝ)
    (hv : ∀ j l, Inner (v j) (v l) = if j = l then 1 else 0)
    (hc : (∑ j, ‖c j‖ ^ 2) = 1) (hC : 0 ≤ C)
    (hfix : ∀ j ∈ T, α j = 1) (hbound : ∀ j, j ∉ T → ‖α j‖ ≤ C) :
    let a := ∑ j ∈ T, ‖c j‖ ^ 2;
    let z := ∑ j, (c j * α j) • v j;
    a ≤ ‖toEuclidean_fromVec z‖ ^ 2 ∧
      ‖toEuclidean_fromVec z‖ ^ 2 ≤ a + C ^ 2 * (1 - a) ∧
      ‖toEuclidean_fromVec (z - spectralTargetState v c T)‖ ≤ C * Real.sqrt (1 - a) := by
  intro a z
  let d : J → ℂ := fun j => if j ∈ T then 0 else c j * α j
  have hz : z - spectralTargetState v c T = ∑ j, d j • v j := by
    have ht : spectralTargetState v c T = ∑ j, (if j ∈ T then c j else 0) • v j := by
      simp [spectralTargetState, ite_smul, Finset.sum_ite_mem]
    rw [ht, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ T
    · simp [d, hj, hfix j hj]
    · simp [d, hj]
  have ha : 0 ≤ a := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hac : a ≤ 1 := by
    rw [← hc]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
      (fun j _ _ => sq_nonneg _)
  have hsplit : (∑ j, ‖c j * α j‖ ^ 2) = a + ∑ j, ‖d j‖ ^ 2 := by
    have ht : a = ∑ j, if j ∈ T then ‖c j‖ ^ 2 else 0 := by
      simp [a, Finset.sum_ite_mem]
    rw [ht, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ T
    · simp [d, hj, hfix j hj]
    · simp [d, hj]
  have hbad : (∑ j, ‖d j‖ ^ 2) ≤ C ^ 2 * (1 - a) := by
    have hcomp : (∑ j, if j ∈ T then 0 else ‖c j‖ ^ 2) = 1 - a := by
      have ht : (∑ j, if j ∈ T then ‖c j‖ ^ 2 else 0) = a := by
        simp [a, Finset.sum_ite_mem]
      have hs : (∑ j, ‖c j‖ ^ 2) =
          (∑ j, if j ∈ T then ‖c j‖ ^ 2 else 0) +
          ∑ j, if j ∈ T then 0 else ‖c j‖ ^ 2 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> simp
      rw [hc, ht] at hs
      linarith
    rw [← hcomp, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j ∈ T
    · simp [d, hj]
    · simp only [d, if_neg hj, norm_mul, mul_pow]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hbound j hj) 2) (sq_nonneg ‖c j‖)
  have hnorm : ‖toEuclidean_fromVec z‖ ^ 2 = a + ∑ j, ‖d j‖ ^ 2 := by
    rw [degenerate_packet_norm_sq v _ hv, hsplit]
  refine ⟨by rw [hnorm]; exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => sq_nonneg _),
    by rw [hnorm]; linarith, ?_⟩
  have he : ‖toEuclidean_fromVec (z - spectralTargetState v c T)‖ ^ 2 ≤
      C ^ 2 * (1 - a) := by rw [hz, degenerate_packet_norm_sq v _ hv]; exact hbad
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1 - a)
  nlinarith [norm_nonneg (toEuclidean_fromVec (z - spectralTargetState v c T)),
    mul_nonneg hC (Real.sqrt_nonneg (1 - a))]

/-- For a normalized orthonormal spectral combination with zero target phases and gap `η`
elsewhere, the zero-event probability lies between `a` and `a+(1/(2*M*η))^(2*k)*(1-a)`. The
zero-branch error is at most `(1/(2*M*η))^k*sqrt(1-a)`. -/
theorem degenerate_phase_zero_event_and_full_branch_error
    (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (W : Matrix I I ℂ) (M k : ℕ) (hM : 2 ≤ M) (v : J → QState I) (c : J → ℂ)
    (φ : J → ℝ) (T : Finset J) (η : ℝ) (_hW : W ∈ Matrix.unitaryGroup I ℂ)
    (hη : 0 < η) (hv : ∀ j l, Inner (v j) (v l) = if j = l then 1 else 0)
    (hc : (∑ j, ‖c j‖ ^ 2) = 1)
    (he : ∀ j, W *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (φ j : ℂ)) • v j)
    (ht : ∀ j ∈ T, phaseDistance (φ j) 0 = 0)
    (hg : ∀ j, j ∉ T → η ≤ phaseDistance (φ j) 0) :
    let ψ := ∑ j, c j • v j;
    let a := ∑ j ∈ T, ‖c j‖ ^ 2;
    let p := MeasureProb (degenerateDetectionState W M k ψ) (phaseZeroEvent M k);
    a ≤ p ∧ p ≤ a + (1 / (2 * (M : ℝ) * η)) ^ (2 * k) * (1 - a) ∧
      ‖toEuclidean_fromVec (degenerateZeroBranch W M k (by omega) ψ -
        spectralTargetState v c T)‖ ≤
        (1 / (2 * (M : ℝ) * η)) ^ k * Real.sqrt (1 - a) := by
  (try dsimp only)
  rw [degenerate_detection_mass W M k (by omega) v c φ he,
    (degenerate_phase_actual_spectral_packet I J W M k (by omega) v c φ he).2]
  have hf : ∀ j ∈ T, (qpeKernel M (φ j) (⟨0, by omega⟩ : Fin M)) ^ k = 1 := by
    intro j hj
    simp [qpeKernel_zero_distance M (by omega) (φ j) (ht j hj), Ket]
  have hb : ∀ j, j ∉ T → ‖(qpeKernel M (φ j) (⟨0, by omega⟩ : Fin M)) ^ k‖ ≤
      (1 / (2 * (M : ℝ) * η)) ^ k := by
    intro j hj
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (phase_detection_zero_label_gap_bound M (by omega) (φ j) η hη (hg j hj)) k
  have h := degenerate_diagonal_filter_bounds v c
    (fun j => (qpeKernel M (φ j) (⟨0, by omega⟩ : Fin M)) ^ k) T
    ((1 / (2 * (M : ℝ) * η)) ^ k) hv hc (by positivity) hf hb
  simpa only [← pow_mul, Nat.mul_comm k 2] using h

/-- The Euclidean norm of a postmeasurement state is at most one. -/
theorem degenerate_postMeasure_norm_le_one {I : Type} [Fintype I] [DecidableEq I]
    (ψ : QState I) (S : Finset I) : ‖toEuclidean_fromVec (PostMeasure ψ S)‖ ≤ 1 := by
  rw [toEuclidean_postMeasure_eq_normalize]
  by_cases h : toEuclidean_fromVec (Collapse ψ S) = 0
  · simp [h]
  · rw [NormedSpace.norm_normalize h]

/-- With positive target mass `a` and the stated zero-phase gap, the normalized zero branch
differs from the normalized target by at most `2*(1/(2*M*η))^k*sqrt(1-a)/sqrt(a)`. -/
theorem degenerate_phase_conditional_target_state_error
    (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (W : Matrix I I ℂ) (M k : ℕ) (hM : 2 ≤ M) (v : J → QState I) (c : J → ℂ)
    (φ : J → ℝ) (T : Finset J) (η : ℝ) (hW : W ∈ Matrix.unitaryGroup I ℂ)
    (hη : 0 < η) (hv : ∀ j l, Inner (v j) (v l) = if j = l then 1 else 0)
    (hc : (∑ j, ‖c j‖ ^ 2) = 1)
    (he : ∀ j, W *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (φ j : ℂ)) • v j)
    (ht : ∀ j ∈ T, phaseDistance (φ j) 0 = 0)
    (hg : ∀ j, j ∉ T → η ≤ phaseDistance (φ j) 0) :
    let a := ∑ j ∈ T, ‖c j‖ ^ 2;
    0 < a → ‖toEuclidean_fromVec
      (PostMeasure (degenerateZeroBranch W M k (by omega) (∑ j, c j • v j)) Finset.univ -
        PostMeasure (spectralTargetState v c T) Finset.univ)‖ ≤
      2 * (1 / (2 * (M : ℝ) * η)) ^ k * Real.sqrt (1 - a) / Real.sqrt a := by
  intro a ha
  let z := degenerateZeroBranch W M k (by omega) (∑ j, c j • v j)
  let t := spectralTargetState v c T
  let ε := (1 / (2 * (M : ℝ) * η)) ^ k * Real.sqrt (1 - a)
  have hclose : ‖toEuclidean_fromVec (z - t)‖ ≤ ε :=
    (degenerate_phase_zero_event_and_full_branch_error I J W M k hM v c φ T η
      hW hη hv hc he ht hg).2.2
  have hmass : MeasureProb t Finset.univ = a := by
    change (∑ i, ‖t i‖ ^ 2) = a
    rw [← norm_toEuclidean_fromVec_sq, spectralTargetState_norm_sq v c T hv]
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  change ‖toEuclidean_fromVec (PostMeasure z Finset.univ - PostMeasure t Finset.univ)‖ ≤ _
  by_cases hsmall : ε < Real.sqrt a
  · have hr := (postMeasure_error_of_gap t z Finset.univ hclose (hmass ▸ hsmall)).2
    rw [hmass] at hr
    simpa only [ε, mul_assoc] using hr
  · have hn : ‖toEuclidean_fromVec (PostMeasure z Finset.univ - PostMeasure t Finset.univ)‖ ≤ 2 := by
      change ‖toEuclidean_fromVec (PostMeasure z Finset.univ) -
        toEuclidean_fromVec (PostMeasure t Finset.univ)‖ ≤ 2
      exact (norm_sub_le _ _).trans (by linarith [degenerate_postMeasure_norm_le_one z Finset.univ,
        degenerate_postMeasure_norm_le_one t Finset.univ])
    apply hn.trans
    apply (le_div_iff₀ hs).mpr
    have hb : 2 * Real.sqrt a ≤ 2 * ε := by linarith
    simpa only [ε, mul_assoc] using hb

end Qatlib.Concepts.SpectralFilter.ZeroPhaseFilter
