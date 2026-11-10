/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixWeights.WeightsCore
import Qatlib.Concepts.SdpDuality.ConeSeparation.MatrixOptimizationInterfacesDefs
import Qatlib.Concepts.QuditTeleport.TeleportCore.InstrumentConditioning
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MatrixWeights.WeightsCore
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.QuditTeleport.TeleportCore

set_option autoImplicit false

namespace Qatlib.Concepts.SdpDuality.ConeSeparation

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder
set_option warningAsError false

noncomputable local instance optimizationMatrixCStar {J : Type} [Fintype J] [DecidableEq J] :
    CStarAlgebra (Matrix J J ℂ) where

theorem payoff_error {D : ℕ} (M ρ σ : Operator D) (hM : ‖M‖ ≤ 1) :
    |(Matrix.trace (M * ρ)).re - (Matrix.trace (M * σ)).re| ≤
      (ρ - σ).traceNorm := by
  calc
    _ = |(Matrix.trace (M * (ρ - σ))).re| := by
      rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    _ ≤ ‖Matrix.trace (M * (ρ - σ))‖ := Complex.abs_re_le_norm _
    _ ≤ (M * (ρ - σ)).traceNorm := Matrix.abs_trace_le_traceNorm _
    _ ≤ ‖M‖ * (ρ - σ).traceNorm := Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
    _ ≤ 1 * (ρ - σ).traceNorm :=
      mul_le_mul_of_nonneg_right hM (Matrix.traceNorm_nonneg _)
    _ = _ := one_mul _

theorem recorded_history_regret
    (D T : ℕ) (M ρ : ℕ → Operator D) (z ξ ζ : ℕ → ℝ)
    (η : ℝ) (σ : Operator D)
    (hD : 0 < D) (hη : 0 < η) (hη1 : η ≤ 1)
    (hM : ∀ t, (M t).IsHermitian ∧ ‖M t‖ ≤ 1)
    (hσ : IsDensityOperator σ)
    (hstate : ∀ t ∈ Finset.range T, (ρ t - mmwState D M η t).traceNorm ≤ ξ t)
    (hrecord : ∀ t ∈ Finset.range T,
      |z t - (Matrix.trace (M t * ρ t)).re| ≤ ζ t) :
    (∑ t ∈ Finset.range T, z t) -
        (∑ t ∈ Finset.range T, (Matrix.trace (M t * σ)).re) ≤
      η * T + Real.log D / η + (∑ t ∈ Finset.range T, (ξ t + ζ t)) := by
  have hround (t : ℕ) (ht : t ∈ Finset.range T) :
      z t ≤ (Matrix.trace (M t * mmwState D M η t)).re + (ξ t + ζ t) := by
    have he := (payoff_error (M t) (ρ t) (mmwState D M η t) (hM t).2).trans
      (hstate t ht)
    have ho := (abs_le.mp (hrecord t ht)).2
    have hs := (abs_le.mp he).2
    linarith
  have hsum := Finset.sum_le_sum hround
  rw [Finset.sum_add_distrib] at hsum
  have hreg := matrix_mw_noncommuting_regret D T M η σ hD hη hη1 hM hσ
  have hdiv : η * (Real.log D / η) = Real.log D := by
    field_simp
  apply (mul_le_mul_iff_right₀ hη).mp
  nlinarith

theorem povm_payoff_mean {O : Type*} [Fintype O] [DecidableEq O] {D : ℕ}
    (Λ : POVM O (Fin D)) (ρ : Operator D) (hρ : IsDensityOperator ρ) (f : O → ℝ) :
    (Qatlib.Concepts.SdpDuality.ConeSeparation.povmLaw Λ ρ hρ).expect f =
      (Matrix.trace (payoffObservable Λ f * ρ)).re := by
  simp only [FinDist.expect, Qatlib.Concepts.SdpDuality.ConeSeparation.povmLaw_prob, payoffObservable,
    Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul,
    Complex.re_sum, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro o _
  exact mul_comm _ _

theorem payoffObservable_hermitian {O : Type*} [Fintype O] {D : ℕ}
    (Λ : POVM O (Fin D)) (f : O → ℝ) : (payoffObservable Λ f).IsHermitian := by
  rw [Matrix.IsHermitian, payoffObservable, Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro o _
  rw [Matrix.conjTranspose_smul, (Λ.mats o).H.eq]
  congr 1
  exact Complex.conj_ofReal _

set_option backward.isDefEq.respectTransparency false in

theorem payoffObservable_psd_unit {O : Type*} [Fintype O] {D : ℕ}
    (Λ : POVM O (Fin D)) (f : O → ℝ) (hf : ∀ o, 0 ≤ f o ∧ f o ≤ 1) :
    (payoffObservable Λ f).PosSemidef ∧ ‖payoffObservable Λ f‖ ≤ 1 := by
  have hpositive (g : O → ℝ) (hg : ∀ o, 0 ≤ g o) :
      (payoffObservable Λ g).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro o _
    exact (HermitianMat.zero_le_iff.mp (Λ.nonneg o)).smul
      (by simpa only [Complex.nonneg_iff, Complex.ofReal_re, Complex.ofReal_im,
        and_true] using! hg o)
  have hX := hpositive f (fun o => (hf o).1)
  have hsum : (∑ o, (Λ.mats o).mat) = (1 : Operator D) := by
    simpa using! congrArg HermitianMat.mat Λ.normalized
  have hcomplement : 1 - payoffObservable Λ f = payoffObservable Λ (fun o => 1 - f o) := by
    rw [← hsum]
    simp only [payoffObservable, Complex.ofReal_sub, Complex.ofReal_one, sub_smul,
      one_smul, Finset.sum_sub_distrib]
  have hY : (1 - payoffObservable Λ f).PosSemidef := by
    rw [hcomplement]
    exact hpositive _ (fun o => sub_nonneg.mpr (hf o).2)
  exact ⟨hX, (CStarAlgebra.norm_le_one_iff_of_nonneg _ hX.nonneg).mpr hY⟩

theorem feedforward_payoff_conditional_mean {H O : Type*} [Fintype H] [Fintype O]
    [DecidableEq O] {D E : ℕ} (I : Instrument H D E) (Λ : H → POVM O (Fin E))
    (ρ : Operator D) (hρ : IsDensityOperator ρ) (f : H → O → ℝ) (h : H)
    (hp : 0 < instrumentProb I ρ h) :
    (∑ o, (instrumentProb (I.feedForward (fun h => Instrument.ofPOVM (Λ h))) ρ ⟨h,o⟩ /
      instrumentProb I ρ h) * f h o) =
        (Matrix.trace (payoffObservable (Λ h) (f h) * I.conditionalState ρ h hp)).re := by
  have hr (o : O) :
      instrumentProb (I.feedForward (fun h => Instrument.ofPOVM (Λ h))) ρ ⟨h,o⟩ /
          instrumentProb I ρ h =
        instrumentProb (Instrument.ofPOVM (Λ h)) (I.conditionalState ρ h hp) o := by
    rw [(instrumentProb_feedForward_conditional_laws I (fun h => Instrument.ofPOVM (Λ h))
      ρ hρ.1 h o).1 hp]
    field_simp
  simp_rw [hr]
  have hm := povm_payoff_mean (Λ h) (I.conditionalState ρ h hp)
    (I.isDensityOperator_conditionalState hρ h hp) (f h)
  simpa only [FinDist.expect, Qatlib.Concepts.SdpDuality.ConeSeparation.povmLaw_prob,
      instrumentProb_ofPOVM] using! hm

theorem feedforward_payoff_zero {H O : Type*} [Fintype H] [Fintype O]
    [DecidableEq O] {D E : ℕ} (I : Instrument H D E) (Λ : H → POVM O (Fin E))
    (ρ : Operator D) (hρ : ρ.PosSemidef) (f : H → O → ℝ) (h : H)
    (hp : instrumentProb I ρ h = 0) :
    (∑ o, instrumentProb (I.feedForward (fun h => Instrument.ofPOVM (Λ h))) ρ ⟨h,o⟩ * f h o) = 0 := by
  apply Finset.sum_eq_zero
  intro o _
  rw [(instrumentProb_feedForward_conditional_laws I (fun h => Instrument.ofPOVM (Λ h))
    ρ hρ h o).2 hp, zero_mul]

end Qatlib.Concepts.SdpDuality.ConeSeparation
