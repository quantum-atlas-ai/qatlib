/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw.RationalPreparedLCU
import Qatlib.Concepts.MonteCarloMean.PayoffEncoding
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.MonteCarloMean.PayoffEncoding
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation

namespace Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open scoped Classical BigOperators Matrix.Norms.L2Operator
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem weight_unitary_event_error {H : Type} [Fintype H] [DecidableEq H]
    (P Q : Matrix H H ℂ) (hP : P ∈ Matrix.unitaryGroup H ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup H ℂ) (j : H) (S : Finset H) :
    |MeasureProb (P *ᵥ Ket j) S-MeasureProb (Q *ᵥ Ket j) S| ≤ 2*‖P-Q‖ := by
  have h := measureProb_sub_le_two_mul_l2 (P *ᵥ Ket j) (Q *ᵥ Ket j) S
    (normalized_applyGate hP (normalized_ket j))
    (normalized_applyGate hQ (normalized_ket j))
  rw [← Matrix.sub_mulVec] at h
  have hv := l2_norm_mulVec_fromVec_le (P-Q) (Ket j)
  rw [(normalized_iff_norm_toEuclidean_fromVec _).mp (normalized_ket j), mul_one] at hv
  exact h.trans (mul_le_mul_of_nonneg_left hv (by norm_num))

theorem weight_target_born {n : ℕ} (w : Option (Fin n) → ℚ)
    (hw : ∀ a, 0 ≤ w a) (hZ : 0 < rationalWeightMass w) (a : Option (Fin n)) :
    BornProb (rationalWeightTarget w) a = ((w a/rationalWeightMass w : ℚ) : ℝ) := by
  unfold BornProb rationalWeightTarget
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sq_sqrt (by exact_mod_cast div_nonneg (hw a) hZ.le)

theorem rational_weight_mean_bias {n : ℕ} (w f : Option (Fin n) → ℚ)
    (hw : ∀ a, 0 ≤ w a) (hZ : 0 < rationalWeightMass w)
    (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) (k : ℕ) :
    |(∑ a, BornProb (rationalWeightPrepare w k *ᵥ Ket none) a * (f a : ℝ)) -
      ∑ a, ((w a/rationalWeightMass w : ℚ) : ℝ)*(f a : ℝ)| ≤ 64*(n : ℝ)/2^k := by
  obtain ⟨_, hP, he⟩ := rational_weight_numerical_word_unitary_and_error n k w hw
  obtain ⟨hQ, htarget, _⟩ := rational_weight_ideal_preparation_exact n w hw hZ
  let R := payoffRotation (fun a => (f a : ℝ))
  have hfr : ∀ a, (f a : ℝ) ∈ Set.Icc 0 1 := fun a =>
    ⟨by exact_mod_cast (hf a).1, by exact_mod_cast (hf a).2⟩
  have hR : R ∈ Matrix.unitaryGroup _ ℂ := payoffRotation_mem_unitaryGroup _ hfr
  have hB := (payoff_actual_rotation_and_mean (rationalWeightPrepare w k) none
    (fun a => (f a : ℝ)) hP hfr)
  have hC := (payoff_actual_rotation_and_mean (idealWeightPrepare w) none
    (fun a => (f a : ℝ)) hQ hfr)
  have h := weight_unitary_event_error _ _ hB.1 hC.1 (none,false)
    (Finset.univ.filter (fun a : Option (Fin n) × Bool => a.2=true))
  simp only [payoffPreparation, ApplyGate] at hB hC h
  rw [hB.2, hC.2, htarget] at h
  simp only [weight_target_born w hw hZ] at h
  apply h.trans
  have hd : ‖R*TensorGate (rationalWeightPrepare w k) (1 : Matrix Bool Bool ℂ) -
      R*TensorGate (idealWeightPrepare w) (1 : Matrix Bool Bool ℂ)‖ ≤ 32*(n : ℝ)/2^k := by
    rw [← Matrix.mul_sub, tensorGate_sub_left]
    calc
      _ ≤ ‖R‖*‖TensorGate (rationalWeightPrepare w k-idealWeightPrepare w) (1 : Matrix Bool Bool ℂ)‖ := norm_mul_le _ _
      _ ≤ 1*(32*(n : ℝ)/2^k) := mul_le_mul (l2_norm_unitary_le_one hR)
        (by rw [l2_norm_tensorGate, l2_norm_one_eq, mul_one]; exact he)
        (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  exact (mul_le_mul_of_nonneg_left hd (by norm_num)).trans_eq (by ring)

theorem rational_weight_actual_ae_original_mean : ∀ (n k M : ℕ)
    (w f : Option (Fin n) → ℚ), (∀ a, 0 ≤ w a) → 0 < rationalWeightMass w →
    (∀ a, 0 ≤ f a ∧ f a ≤ 1) → 2 ≤ M →
    let B :=
        rationalPayoffRotation f k * TensorGate (rationalWeightPrepare w k)
        (1 : Matrix Bool Bool ℂ);
    let S := Finset.univ.filter (fun a : Option (Fin n) × Bool => a.2=true);
    ∃ hB : B ∈ Matrix.unitaryGroup (Option (Fin n) × Bool) ℂ,
      (let μ := ∑ a, ((w a/rationalWeightMass w : ℚ) : ℝ)*(f a : ℝ);
       ∀ hM : 2 ≤ M,
       ∑ z ∈ Finset.univ.filter (fun z : Fin M => |aeEstimate M z-μ| ≤
         Real.pi/(M : ℝ)+Real.pi^2/(M : ℝ)^2+64*(n+1 : ℝ)/2^k),
         (aeLaw M B (none,false) S hB hM).prob z ≥ 8/Real.pi^2) := by
  intro n k M w f hw hZ hf hM
  (try dsimp only)
  obtain ⟨_, hP, _⟩ := rational_weight_numerical_word_unitary_and_error n k w hw
  obtain ⟨hB, _, hgood⟩ := rational_payoff_actual_ae_mean_and_precision
    (Option (Fin n)) (rationalWeightPrepare w k) none f k M hM hP hf
  refine ⟨hB, ?_⟩
  intro hM'
  apply hgood.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    have hb := rational_weight_mean_bias w f hw hZ hf k
    have ht := abs_sub_le (aeEstimate M z)
      (∑ a, BornProb (rationalWeightPrepare w k *ᵥ Ket none) a*(f a : ℝ))
      (∑ a, ((w a/rationalWeightMass w : ℚ) : ℝ)*(f a : ℝ))
    have he : 64/(2 : ℝ)^k+64*(n : ℝ)/2^k=64*(n+1 : ℝ)/2^k := by push_cast; ring
    linarith
  · intro z _ _
    exact (aeLaw M _ (none,false) _ hB hM').nonneg z

end Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
