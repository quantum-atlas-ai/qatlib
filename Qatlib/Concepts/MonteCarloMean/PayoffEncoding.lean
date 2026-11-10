/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.PayoffRotation.RationalPayoffRotation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability

open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation

namespace Qatlib.Concepts.MonteCarloMean.PayoffEncoding
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

theorem rational_payoff_weighted_bias
    {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I)
    (f : I → ℚ) (k : ℕ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) :
    |(∑ i, BornProb (A *ᵥ Ket j) i * (rationalPayoffValue (f i) k : ℝ)) -
      ∑ i, BornProb (A *ᵥ Ket j) i * (f i : ℝ)| ≤ 64 / 2 ^ k := by
  have hn : (∑ i, BornProb (A *ᵥ Ket j) i) = 1 :=
    normalized_applyGate hA (normalized_ket j)
  rw [← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  calc
    _ ≤ ∑ i, |BornProb (A *ᵥ Ket j) i *
        ((rationalPayoffValue (f i) k : ℝ) - (f i : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, BornProb (A *ᵥ Ket j) i * (64 / 2 ^ k) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (bornProb_nonneg _ _)]
      exact mul_le_mul_of_nonneg_left (rationalPayoffValue_error (f i) k (hf i).1 (hf i).2)
        (bornProb_nonneg _ _)
    _ = _ := by rw [← Finset.sum_mul, hn, one_mul]

theorem rational_payoff_preparation_mass
    {I : Type} [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I)
    (f : I → ℚ) (k : ℕ) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) :
    let B := rationalPayoffRotation f k * TensorGate A (1 : Matrix Bool Bool ℂ);
    B ∈ Matrix.unitaryGroup (I × Bool) ℂ ∧
      MeasureProb (B *ᵥ Ket (j, false)) (Finset.univ.filter (fun p : I × Bool => p.2 = true)) =
        ∑ i, BornProb (A *ᵥ Ket j) i * (rationalPayoffValue (f i) k : ℝ) ∧
      |MeasureProb (B *ᵥ Ket (j, false)) (Finset.univ.filter (fun p : I × Bool => p.2 = true)) -
        ∑ i, BornProb (A *ᵥ Ket j) i * (f i : ℝ)| ≤ 64 / 2 ^ k := by
  (try dsimp only)
  have hg : ∀ i, (rationalPayoffValue (f i) k : ℝ) ∈ Set.Icc 0 1 := by
    intro i
    have h := (rational_payoff_unitary_value_and_operator_error I f k hf).2.1 i
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2.1⟩
  have hb : rationalPayoffRotation f k * TensorGate A (1 : Matrix Bool Bool ℂ) =
      payoffPreparation A (fun i => (rationalPayoffValue (f i) k : ℝ)) := by
    rw [rationalPayoffRotation_eq_payoffRotation f k hf]
    rfl
  rw [hb]
  have h := payoff_actual_rotation_and_mean A j (fun i => (rationalPayoffValue (f i) k : ℝ)) hA hg
  simp only [ApplyGate] at h
  refine ⟨h.1, h.2, ?_⟩
  rw [h.2]
  exact rational_payoff_weighted_bias A j f k hA hf

theorem rational_payoff_actual_ae_mean_and_precision
    (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (j : I)
    (f : I → ℚ) (k M : ℕ) (hM : 2 ≤ M) (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1) :
    let B := rationalPayoffRotation f k * TensorGate A (1 : Matrix Bool Bool ℂ);
    ∃ hB : B ∈ Matrix.unitaryGroup (I × Bool) ℂ,
      MeasureProb (B *ᵥ Ket (j, false)) (Finset.univ.filter (fun p : I × Bool => p.2 = true)) =
        ∑ i, BornProb (A *ᵥ Ket j) i * (rationalPayoffValue (f i) k : ℝ) ∧
      (let μ := ∑ i, BornProb (A *ᵥ Ket j) i * (f i : ℝ);
        ∑ z ∈ Finset.univ.filter (fun z : Fin M => |aeEstimate M z - μ| ≤
          Real.pi / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2 + 64 / 2 ^ k),
          (aeLaw M B (j, false) (Finset.univ.filter (fun p : I × Bool => p.2 = true)) hB hM).prob z
          ≥ 8 / Real.pi ^ 2) := by
  intro B
  obtain ⟨hB, hmass, hbias⟩ := rational_payoff_preparation_mass A j f k hA hf
  refine ⟨hB, hmass, ?_⟩
  intro μ
  let S := Finset.univ.filter (fun p : I × Bool => p.2 = true)
  let a := MeasureProb (B *ᵥ Ket (j, false)) S
  let p := aeLaw M B (j, false) S hB hM
  have ha0 : 0 ≤ a := measureProb_nonneg _ _
  have ha1 : a ≤ 1 := measureProb_le_one (normalized_applyGate hB (normalized_ket _)) _
  have hs : Real.sqrt (a * (1 - a)) ≤ 1 / 2 := by
    have hsq := Real.sq_sqrt (mul_nonneg ha0 (by linarith : 0 ≤ 1 - a))
    nlinarith [sq_nonneg (a - 1 / 2), Real.sqrt_nonneg (a * (1 - a))]
  have hMr : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hwin : 2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) ≤ Real.pi / (M : ℝ) := by
    apply (div_le_div_iff_of_pos_right hMr).mpr
    nlinarith [Real.pi_pos]
  have hgood := (prepared_ae_bhmt_error_and_endpoints M hM B (j, false) S hB).1
  change 8 / Real.pi ^ 2 ≤ ∑ z ∈ Finset.univ.filter (fun z : Fin M => |aeEstimate M z - a| ≤
    2 * Real.pi * Real.sqrt (a * (1 - a)) / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2), p.prob z at hgood
  apply hgood.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    have ht := abs_sub_le (aeEstimate M z) a μ
    have hb : |a - μ| ≤ 64 / 2 ^ k := hbias
    linarith
  · intro z _ _
    exact p.nonneg z

theorem rational_payoff_numeric_table_and_ae_access_consumer (k M : ℕ) (hM : 2 ≤ M) :
    let f : Bool → ℚ := fun b => if b then 3 / 4 else 1 / 4;
    let B := rationalPayoffRotation f k * TensorGate Hadamard (1 : Matrix Bool Bool ℂ);
    |MeasureProb (B *ᵥ Ket (false, false))
      (Finset.univ.filter (fun p : Bool × Bool => p.2 = true)) - 1 / 2| ≤ 64 / 2 ^ k ∧
      QueryCount (countedAECircuit M B (false, false)) = M - 1 ∧
      GateCount (countedAECircuit M B (false, false)) = 5 * (M - 1) + 3 ∧
      aeForwardAccesses (aeAccessWord (I := Bool × Bool) M) = M ∧
      aeBackwardAccesses (aeAccessWord (I := Bool × Bool) M) = M - 1 := by
  intro f B
  have hf : ∀ i, 0 ≤ f i ∧ f i ≤ 1 := by intro i; cases i <;> norm_num [f]
  have hmean : (∑ i, BornProb (Hadamard *ᵥ Ket false) i * (f i : ℝ)) = 1 / 2 := by
    rw [show Hadamard *ᵥ Ket false = Plus from applyGate_hadamard_ket_false]
    norm_num [Fintype.sum_bool, BornProb, Plus, hadamard_apply_false, f, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2), inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hb := (rational_payoff_preparation_mass Hadamard false f k hadamard_unitary hf).2.2
  rw [hmean] at hb
  have hc := prepared_ae_access_ledger M (by omega) B (false, false)
  have hs := prepared_ae_separate_access_counts (I := Bool × Bool) M (by omega)
  exact ⟨hb, hc.1, hc.2.1, hs.1, hs.2.1⟩

end Qatlib.Concepts.MonteCarloMean.PayoffEncoding
