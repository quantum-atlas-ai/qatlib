/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FiniteStats.BornEstimator.EffectNormalize
import Qatlib.Foundations.FiniteStats.BornEstimator.MeasurementScore

/-!
# Measurement-score identities and Hilbert--Schmidt bounds

Extends the public finite measurement score with weight identities, positivity, and
observable budgets, including the zero-dimensional case.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.FiniteStats.BornEstimator

open Qatlib.Foundations.FiniteStats.BornEstimator
open scoped Classical BigOperators RealInnerProductSpace
variable {d V Ω : Type*} [Fintype d] [DecidableEq d] [Nonempty d] [Fintype V] [Fintype Ω]

/-! The score is a genuine nonnegative finite statistic whenever the source
weights are nonnegative.  This keeps the zero-effect convention explicit:
the denominator may vanish, but the corresponding real division is still
nonnegative because both numerator and denominator are nonnegative. -/

/-- The actual measurement score cannot be negative. -/
theorem measurementScore_nonneg (S : V → HermitianMat d ℂ) (w : V → ℝ)
    (hw : ∀ i, 0 ≤ w i) (P : POVM Ω d) : 0 ≤ measurementScore S w P := by
  unfold measurementScore
  apply Finset.sum_nonneg
  intro s hs
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hw i) (sq_nonneg _)
  · apply mul_nonneg
    · positivity
    · exact HermitianMat.trace_nonneg (P.nonneg s)

/-- Vanishing source weights erase the actual measurement score exactly. -/
theorem measurementScore_zero_weights (S : V → HermitianMat d ℂ)
    (w : V → ℝ) (hw : ∀ i, w i = 0) (P : POVM Ω d) :
    measurementScore S w P = 0 := by
  unfold measurementScore
  simp_rw [hw]
  simp

/-- The actual score is homogeneous in the source weights, including when a
zero effect makes a denominator vanish. -/
theorem measurementScore_scale_weights (S : V → HermitianMat d ℂ)
    (w : V → ℝ) (c : ℝ) (P : POVM Ω d) :
    measurementScore S (fun i => c * w i) P = c * measurementScore S w P := by
  unfold measurementScore
  calc
    (∑ s, (∑ i, (c * w i) * ⟪P.mats s, S i⟫ ^ 2) /
        ((Fintype.card d : ℝ) * (P.mats s).trace)) =
      ∑ s, c * ((∑ i, w i * ⟪P.mats s, S i⟫ ^ 2) /
        ((Fintype.card d : ℝ) * (P.mats s).trace)) := by
      apply Finset.sum_congr rfl
      intro s hs
      have hsum :
          (∑ i, c * w i * ⟪P.mats s, S i⟫ ^ 2) =
            c * ∑ i, w i * ⟪P.mats s, S i⟫ ^ 2 := by
        simpa [mul_assoc] using
          (Finset.mul_sum Finset.univ (fun i => w i * ⟪P.mats s, S i⟫ ^ 2) c).symm
      rw [hsum]
      ring
    _ = c * ∑ s, (∑ i, w i * ⟪P.mats s, S i⟫ ^ 2) /
        ((Fintype.card d : ℝ) * (P.mats s).trace) := by
      rw [Finset.mul_sum]

/-- The actual score is additive in the source weights. -/
theorem measurementScore_add_weights (S : V → HermitianMat d ℂ)
    (w₁ w₂ : V → ℝ) (P : POVM Ω d) :
    measurementScore S (fun i => w₁ i + w₂ i) P =
      measurementScore S w₁ P + measurementScore S w₂ P := by
  unfold measurementScore
  calc
    (∑ s, (∑ i, (w₁ i + w₂ i) * ⟪P.mats s, S i⟫ ^ 2) /
        ((Fintype.card d : ℝ) * (P.mats s).trace)) =
      ∑ s, ((∑ i, w₁ i * ⟪P.mats s, S i⟫ ^ 2) /
        ((Fintype.card d : ℝ) * (P.mats s).trace) +
        (∑ i, w₂ i * ⟪P.mats s, S i⟫ ^ 2) /
        ((Fintype.card d : ℝ) * (P.mats s).trace)) := by
      apply Finset.sum_congr rfl
      intro s hs
      have hsum :
          (∑ i, (w₁ i + w₂ i) * ⟪P.mats s, S i⟫ ^ 2) =
            (∑ i, w₁ i * ⟪P.mats s, S i⟫ ^ 2) +
              ∑ i, w₂ i * ⟪P.mats s, S i⟫ ^ 2 := by
        simp_rw [add_mul]
        rw [Finset.sum_add_distrib]
      rw [hsum]
      ring
    _ = (∑ s, (∑ i, w₁ i * ⟪P.mats s, S i⟫ ^ 2) /
        ((Fintype.card d : ℝ) * (P.mats s).trace)) +
        ∑ s, (∑ i, w₂ i * ⟪P.mats s, S i⟫ ^ 2) /
        ((Fintype.card d : ℝ) * (P.mats s).trace) := by
      rw [Finset.sum_add_distrib]

/-- The actual score respects signed differences of source weights. -/
theorem measurementScore_sub_weights (S : V → HermitianMat d ℂ)
    (w₁ w₂ : V → ℝ) (P : POVM Ω d) :
    measurementScore S (fun i => w₁ i - w₂ i) P =
      measurementScore S w₁ P - measurementScore S w₂ P := by
  calc
    measurementScore S (fun i => w₁ i - w₂ i) P =
        measurementScore S (fun i => w₁ i + (-w₂ i)) P := by
          simp [sub_eq_add_neg]
    _ = measurementScore S w₁ P + measurementScore S (fun i => -w₂ i) P :=
      measurementScore_add_weights S w₁ (fun i => -w₂ i) P
    _ = measurementScore S w₁ P + (-1) * measurementScore S w₂ P := by
      have hfun : (fun i => -w₂ i) = (fun i => (-1 : ℝ) * w₂ i) := by
        funext i
        ring
      rw [hfun, measurementScore_scale_weights S w₂ (-1) P]
    _ = measurementScore S w₁ P - measurementScore S w₂ P := by ring

omit [Nonempty d] in
/-- Every actual POVM score is bounded by the observable Hilbert--Schmidt
budget, without choosing an optimizer or an admissible-state set. -/
theorem measurementScore_le_observable_budget (S : V → HermitianMat d ℂ)
    (w : V → ℝ) (hw : ∀ i, 0 ≤ w i) (P : POVM Ω d) :
    measurementScore S w P ≤ ∑ i, w i * ‖S i‖ ^ 2 := by
  classical
  by_cases hd : Nonempty d
  · letI := hd
    have hscore := measurementScore_le_stateValue S w hw (Set.univ : Set (MState d)) P
      (fun s hne => Set.mem_univ _)
    have hsup : stateScoreValue S w (Set.univ : Set (MState d)) ≤
        ∑ i, w i * ‖S i‖ ^ 2 := by
      unfold stateScoreValue
      apply csSup_le
      · exact Set.image_nonempty.mpr Set.univ_nonempty
      · intro y hy
        rcases hy with ⟨ρ, hρ, rfl⟩
        exact quadraticScore_le S w hw ρ
    exact hscore.trans hsup
  · letI : IsEmpty d := not_nonempty_iff.mp hd
    simp only [measurementScore, Fintype.card_of_isEmpty, Nat.cast_zero, zero_mul,
      div_zero, Finset.sum_const_zero]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))

/-- If every observable has Hilbert--Schmidt norm at most `B`, the score is
bounded by the squared norm budget times the total source weight. -/
theorem measurementScore_le_weight_mass_mul_norm (S : V → HermitianMat d ℂ)
    (w : V → ℝ) (hw : ∀ i, 0 ≤ w i) (B : ℝ) (hB : 0 ≤ B)
    (hS : ∀ i, ‖S i‖ ≤ B) (P : POVM Ω d) :
    measurementScore S w P ≤ B ^ 2 * ∑ i, w i := by
  have hbudget := measurementScore_le_observable_budget S w hw P
  have hsum :
      (∑ i, w i * ‖S i‖ ^ 2) ≤ ∑ i, w i * B ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg (S i)) hB).2 (hS i)) (hw i)
  calc
    measurementScore S w P ≤ ∑ i, w i * ‖S i‖ ^ 2 := hbudget
    _ ≤ ∑ i, w i * B ^ 2 := hsum
    _ = B ^ 2 * ∑ i, w i := by
      calc
        (∑ i, w i * B ^ 2) = ∑ i, B ^ 2 * w i := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = B ^ 2 * ∑ i, w i := by rw [Finset.mul_sum]

/-- A scalar total-weight budget turns the norm bound into a direct score
budget. -/
theorem measurementScore_le_budget (S : V → HermitianMat d ℂ)
    (w : V → ℝ) (hw : ∀ i, 0 ≤ w i) (B W : ℝ) (hB : 0 ≤ B)
    (hS : ∀ i, ‖S i‖ ≤ B) (hW : (∑ i, w i) ≤ W) (P : POVM Ω d) :
    measurementScore S w P ≤ B ^ 2 * W := by
  calc
    measurementScore S w P ≤ B ^ 2 * ∑ i, w i :=
      measurementScore_le_weight_mass_mul_norm S w hw B hB hS P
    _ ≤ B ^ 2 * W := mul_le_mul_of_nonneg_left hW (sq_nonneg B)

/-- Pack the native nonnegativity and scalar budget into the interval consumed
by finite-statistics confidence layers. -/
theorem measurementScore_mem_Icc_budget (S : V → HermitianMat d ℂ)
    (w : V → ℝ) (hw : ∀ i, 0 ≤ w i) (B W : ℝ) (hB : 0 ≤ B)
    (hS : ∀ i, ‖S i‖ ≤ B) (hW : (∑ i, w i) ≤ W) (P : POVM Ω d) :
    measurementScore S w P ∈ Set.Icc 0 (B ^ 2 * W) := by
  exact ⟨measurementScore_nonneg S w hw P,
    measurementScore_le_budget S w hw B W hB hS hW P⟩

/-- A nonnegative source with zero total weight contributes no score. -/
theorem measurementScore_zero_of_weight_mass_zero (S : V → HermitianMat d ℂ)
    (w : V → ℝ) (hw : ∀ i, 0 ≤ w i) (hzero : (∑ i, w i) = 0)
    (P : POVM Ω d) : measurementScore S w P = 0 := by
  apply measurementScore_zero_weights S w (P := P)
  intro i
  have hall : ∀ j ∈ (Finset.univ : Finset V), w j = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => hw j)).mp hzero
  exact hall i (Finset.mem_univ i)

/-- The actual score is monotone under pointwise increases of nonnegative
source weights. -/
theorem measurementScore_mono_weights (S : V → HermitianMat d ℂ)
    (w₁ w₂ : V → ℝ) (h12 : ∀ i, w₁ i ≤ w₂ i) (P : POVM Ω d) :
    measurementScore S w₁ P ≤ measurementScore S w₂ P := by
  have hdiff : ∀ i, 0 ≤ w₂ i - w₁ i := fun i => sub_nonneg.mpr (h12 i)
  have hnon := measurementScore_nonneg S (fun i => w₂ i - w₁ i) hdiff P
  have hsub := measurementScore_sub_weights S w₂ w₁ P
  linarith

/-- Pointwise equal source weights are interchangeable in the actual score. -/
theorem measurementScore_congr_weights (S : V → HermitianMat d ℂ)
    (w₁ w₂ : V → ℝ) (h12 : ∀ i, w₁ i = w₂ i) (P : POVM Ω d) :
    measurementScore S w₁ P = measurementScore S w₂ P := by
  congr 2
  funext i
  exact h12 i

/-- Vanishing observables erase the actual score for every source weight. -/
theorem measurementScore_zero_observables (S : V → HermitianMat d ℂ)
    (w : V → ℝ) (hS : ∀ i, S i = 0) (P : POVM Ω d) :
    measurementScore S w P = 0 := by
  unfold measurementScore
  simp_rw [hS]
  simp

end Qatlib.Foundations.FiniteStats.BornEstimator
