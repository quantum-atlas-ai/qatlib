/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QComplexity97.MachineDefs.QtmPrecision

open Qatlib.Foundations.PureStateMath

noncomputable def stateNorm {I : Type*} [Fintype I] (ψ : QState I) : ℝ :=
  ‖(EuclideanSpace.equiv I ℂ).symm ψ‖

theorem stateNorm_eq_sqrt {I : Type*} [Fintype I] (ψ : QState I) :
    stateNorm ψ = Real.sqrt (∑ i, ‖ψ i‖ ^ 2) := by
  rw [stateNorm, EuclideanSpace.norm_eq]
  simp

theorem stateNorm_sq {I : Type*} [Fintype I] (ψ : QState I) :
    stateNorm ψ ^ 2 = ∑ i, ‖ψ i‖ ^ 2 := by
  rw [stateNorm, EuclideanSpace.norm_sq_eq]
  simp

theorem stateNorm_nonneg {I : Type*} [Fintype I] (ψ : QState I) :
    0 ≤ stateNorm ψ := norm_nonneg _

@[simp] theorem stateNorm_zero {I : Type*} [Fintype I] :
    stateNorm (0 : QState I) = 0 := by
  rw [stateNorm, show (EuclideanSpace.equiv I ℂ).symm (0 : QState I) = 0 from by simp,
    norm_zero]

theorem stateNorm_neg {I : Type*} [Fintype I] (ψ : QState I) :
    stateNorm (-ψ) = stateNorm ψ := by
  rw [stateNorm, show (EuclideanSpace.equiv I ℂ).symm (-ψ) =
      -(EuclideanSpace.equiv I ℂ).symm ψ from by simp, stateNorm, norm_neg]

theorem stateNorm_add_le {I : Type*} [Fintype I] (ψ φ : QState I) :
    stateNorm (ψ + φ) ≤ stateNorm ψ + stateNorm φ := by
  rw [stateNorm, show (EuclideanSpace.equiv I ℂ).symm (ψ + φ) =
      (EuclideanSpace.equiv I ℂ).symm ψ + (EuclideanSpace.equiv I ℂ).symm φ from by simp,
    stateNorm, stateNorm]
  exact norm_add_le _ _

theorem stateNorm_sub_le {I : Type*} [Fintype I] (ψ φ : QState I) :
    stateNorm (ψ - φ) ≤ stateNorm ψ + stateNorm φ := by
  have h := stateNorm_add_le ψ (-φ)
  rw [stateNorm_neg] at h
  simpa [sub_eq_add_neg] using h

theorem normalized_iff_stateNorm_eq_one {I : Type*} [Fintype I] (ψ : QState I) :
    Normalized ψ ↔ stateNorm ψ = 1 := by
  rw [stateNorm_eq_sqrt, Normalized, Real.sqrt_eq_one]

theorem deviation_accumulation {I : Type*} [Fintype I]
    (U : QState I →ₗ[ℂ] QState I) (hU : ∀ ψ, stateNorm (U ψ) = stateNorm ψ)
    (φ φt : ℕ → QState I) (ε : ℝ) (T : ℕ)
    (h0 : φt 0 = φ 0)
    (hstep : ∀ i, i < T → φ (i + 1) = U (φt i))
    (hdev : ∀ i, 0 < i → i ≤ T → stateNorm (φ i - φt i) ≤ ε) :
    stateNorm (φt T - U^[T] (φ 0)) ≤ T * ε := by
  induction T with
  | zero => simp [h0]
  | succ T ih =>
    have hstepT : φ (T + 1) = U (φt T) := hstep T (Nat.lt_succ_self T)
    have hidx : φt (T + 1) - U^[T + 1] (φ 0) =
        U (φt T - U^[T] (φ 0)) - (φ (T + 1) - φt (T + 1)) := by
      rw [Function.iterate_succ_apply', hstepT, map_sub]
      abel
    have ih' : stateNorm (φt T - U^[T] (φ 0)) ≤ (T : ℝ) * ε :=
      ih (fun i hi => hstep i (Nat.lt_trans hi (Nat.lt_succ_self T)))
        (fun i hi0 hiT => hdev i hi0 (Nat.le_trans hiT (Nat.le_succ T)))
    have hdevT : stateNorm (φ (T + 1) - φt (T + 1)) ≤ ε :=
      hdev (T + 1) (Nat.succ_pos T) (Nat.le_refl _)
    calc stateNorm (φt (T + 1) - U^[T + 1] (φ 0))
        = stateNorm (U (φt T - U^[T] (φ 0)) - (φ (T + 1) - φt (T + 1))) := by rw [hidx]
      _ ≤ stateNorm (U (φt T - U^[T] (φ 0))) + stateNorm (φ (T + 1) - φt (T + 1)) :=
          stateNorm_sub_le _ _
      _ ≤ (T : ℝ) * ε + ε := by
          rw [hU _]
          linarith
      _ = ((T + 1 : ℕ) : ℝ) * ε := by push_cast; ring

theorem sum_mul_le_sqrt_mul_sqrt {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    ∑ i ∈ s, f i * g i ≤ Real.sqrt (∑ i ∈ s, f i ^ 2) * Real.sqrt (∑ i ∈ s, g i ^ 2) := by
  have hF : 0 ≤ ∑ i ∈ s, f i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  calc ∑ i ∈ s, f i * g i ≤ Real.sqrt ((∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2) :=
        Real.le_sqrt_of_sq_le (Finset.sum_mul_sq_le_sq_mul_sq s f g)
    _ = Real.sqrt (∑ i ∈ s, f i ^ 2) * Real.sqrt (∑ i ∈ s, g i ^ 2) := Real.sqrt_mul hF _

theorem born_gap_pointwise {I : Type*} (ψ φ : QState I) (i : I) :
    |BornProb ψ i - BornProb φ i| ≤ ‖ψ i - φ i‖ * (‖ψ i‖ + ‖φ i‖) := by
  have h1 : BornProb ψ i - BornProb φ i = (‖ψ i‖ - ‖φ i‖) * (‖ψ i‖ + ‖φ i‖) := by
    unfold BornProb
    ring
  rw [h1, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖ψ i‖ + ‖φ i‖)]
  have h2 : |‖ψ i‖ - ‖φ i‖| ≤ ‖ψ i - φ i‖ := abs_norm_sub_norm_le _ _
  nlinarith [norm_nonneg (ψ i), norm_nonneg (φ i), h2,
    abs_nonneg (‖ψ i‖ - ‖φ i‖), norm_nonneg (ψ i - φ i)]

theorem born_gap_sum_le {I : Type*} [Fintype I] (ψ φ : QState I) :
    ∑ i, |BornProb ψ i - BornProb φ i| ≤ (stateNorm ψ + stateNorm φ) * stateNorm (ψ - φ) := by
  have hstep : ∑ i, |BornProb ψ i - BornProb φ i| ≤
      ∑ i, (‖ψ i - φ i‖ * ‖ψ i‖ + ‖ψ i - φ i‖ * ‖φ i‖) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have h := born_gap_pointwise ψ φ i
    have : ‖ψ i - φ i‖ * (‖ψ i‖ + ‖φ i‖) =
        ‖ψ i - φ i‖ * ‖ψ i‖ + ‖ψ i - φ i‖ * ‖φ i‖ := by ring
    linarith
  have hA : ∑ i, ‖ψ i - φ i‖ * ‖ψ i‖ ≤
      Real.sqrt (∑ i, ‖ψ i - φ i‖ ^ 2) * Real.sqrt (∑ i, ‖ψ i‖ ^ 2) :=
    sum_mul_le_sqrt_mul_sqrt _ _ _
  have hB : ∑ i, ‖ψ i - φ i‖ * ‖φ i‖ ≤
      Real.sqrt (∑ i, ‖ψ i - φ i‖ ^ 2) * Real.sqrt (∑ i, ‖φ i‖ ^ 2) :=
    sum_mul_le_sqrt_mul_sqrt _ _ _
  have hsplit : ∑ i, (‖ψ i - φ i‖ * ‖ψ i‖ + ‖ψ i - φ i‖ * ‖φ i‖) =
      ∑ i, ‖ψ i - φ i‖ * ‖ψ i‖ + ∑ i, ‖ψ i - φ i‖ * ‖φ i‖ := Finset.sum_add_distrib
  have hd : Real.sqrt (∑ i, ‖ψ i - φ i‖ ^ 2) = stateNorm (ψ - φ) := by
    rw [stateNorm_eq_sqrt]
    rfl
  have ha : Real.sqrt (∑ i, ‖ψ i‖ ^ 2) = stateNorm ψ := (stateNorm_eq_sqrt ψ).symm
  have hb : Real.sqrt (∑ i, ‖φ i‖ ^ 2) = stateNorm φ := (stateNorm_eq_sqrt φ).symm
  rw [hsplit] at hstep
  rw [hd, ha] at hA
  rw [hd, hb] at hB
  nlinarith [stateNorm_nonneg (ψ - φ)]

theorem born_gap_sum_le_of_normalized {I : Type*} [Fintype I] (ψ φ : QState I)
    {ε : ℝ} (hψ : Normalized ψ) (hφ : Normalized φ) (h : stateNorm (ψ - φ) ≤ ε) :
    ∑ i, |BornProb ψ i - BornProb φ i| ≤ 2 * ε := by
  have h1 := born_gap_sum_le ψ φ
  have h2 : stateNorm ψ = 1 := (normalized_iff_stateNorm_eq_one ψ).1 hψ
  have h3 : stateNorm φ = 1 := (normalized_iff_stateNorm_eq_one φ).1 hφ
  rw [h2, h3] at h1
  nlinarith [stateNorm_nonneg (ψ - φ)]

noncomputable def totalVariation {I : Type*} [Fintype I] (p q : I → ℝ) : ℝ :=
  (1 / 2) * ∑ i, |p i - q i|

theorem totalVariation_born_le {I : Type*} [Fintype I] (ψ φ : QState I)
    {ε : ℝ} (hψ : Normalized ψ) (hφ : Normalized φ) (h : stateNorm (ψ - φ) ≤ ε) :
    totalVariation (BornProb ψ) (BornProb φ) ≤ ε := by
  have h1 := born_gap_sum_le_of_normalized ψ φ hψ hφ h
  rw [totalVariation]
  nlinarith

theorem observation_totalVariation_le {I : Type*} [Fintype I]
    (U : QState I →ₗ[ℂ] QState I) (hU : ∀ ψ, stateNorm (U ψ) = stateNorm ψ)
    (φ φt : ℕ → QState I) (ε : ℝ) (T : ℕ)
    (h0 : φt 0 = φ 0)
    (hstep : ∀ i, i < T → φ (i + 1) = U (φt i))
    (hdev : ∀ i, 0 < i → i ≤ T → stateNorm (φ i - φt i) ≤ ε)
    (hφt : Normalized (φt T)) (hφ : Normalized (U^[T] (φ 0))) :
    totalVariation (BornProb (φt T)) (BornProb (U^[T] (φ 0))) ≤ T * ε :=
  totalVariation_born_le _ _ hφt hφ
    (deviation_accumulation U hU φ φt ε T h0 hstep hdev)

end Qatlib.Papers.QComplexity97.MachineDefs.QtmPrecision
