/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Mathlib.Tactic.Ring

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.Trainability23.VarianceScaling

open scoped BigOperators

noncomputable def ensembleMean {Θ : Type*} [Fintype Θ] (P : FinDist Θ) (L : Θ → ℝ) : ℝ :=
  ∑ θ, P.prob θ * L θ

noncomputable def ensembleVariance {Θ : Type*} [Fintype Θ] (P : FinDist Θ) (L : Θ → ℝ) : ℝ :=
  ∑ θ, P.prob θ * (L θ - ensembleMean P L) ^ 2

theorem ensembleMean_const {Θ : Type*} [Fintype Θ] (P : FinDist Θ) (c : ℝ) :
    ensembleMean P (fun _ => c) = c := by
  unfold ensembleMean
  rw [← Finset.sum_mul, P.sum_one, one_mul]

theorem ensembleVariance_const {Θ : Type*} [Fintype Θ] (P : FinDist Θ) (c : ℝ) :
    ensembleVariance P (fun _ => c) = 0 := by
  unfold ensembleVariance
  rw [ensembleMean_const]
  simp

theorem ensembleMean_add_const {Θ : Type*} [Fintype Θ] (P : FinDist Θ) (L : Θ → ℝ) (c : ℝ) :
    ensembleMean P (fun θ => L θ + c) = ensembleMean P L + c := by
  have h : ∀ θ : Θ, P.prob θ * (L θ + c) = P.prob θ * L θ + P.prob θ * c := fun θ => by ring
  unfold ensembleMean
  rw [Finset.sum_congr rfl fun θ _ => h θ, Finset.sum_add_distrib, ← Finset.sum_mul, P.sum_one,
    one_mul]

theorem ensembleVariance_add_const {Θ : Type*} [Fintype Θ] (P : FinDist Θ) (L : Θ → ℝ) (c : ℝ) :
    ensembleVariance P (fun θ => L θ + c) = ensembleVariance P L := by
  unfold ensembleVariance
  rw [ensembleMean_add_const]
  exact Finset.sum_congr rfl fun θ _ => by ring

theorem ensembleVariance_nonneg {Θ : Type*} [Fintype Θ] (P : FinDist Θ) (L : Θ → ℝ) :
    0 ≤ ensembleVariance P L :=
  Finset.sum_nonneg fun θ _ => mul_nonneg (P.nonneg θ) (sq_nonneg _)

theorem ensembleVariance_eq_zero_iff {Θ : Type*} [Fintype Θ] (P : FinDist Θ) (L : Θ → ℝ) :
    ensembleVariance P L = 0 ↔ ∀ θ, P.prob θ ≠ 0 → L θ = ensembleMean P L := by
  constructor
  · intro h
    have hnn : ∀ θ ∈ (Finset.univ : Finset Θ),
        0 ≤ P.prob θ * (L θ - ensembleMean P L) ^ 2 :=
      fun θ _ => mul_nonneg (P.nonneg θ) (sq_nonneg _)
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h
    intro θ hθ
    have h0 := hall θ (Finset.mem_univ θ)
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 hθ
    · exact sub_eq_zero.mp (sq_eq_zero_iff.mp h1)
  · intro h
    refine Finset.sum_eq_zero fun θ _ => ?_
    by_cases hθ : P.prob θ = 0
    · rw [hθ, zero_mul]
    · rw [h θ hθ]
      ring

theorem ensembleVariance_eq_meanSq_sub_sq {Θ : Type*} [Fintype Θ] (P : FinDist Θ) (L : Θ → ℝ) :
    ensembleVariance P L = (∑ θ, P.prob θ * (L θ) ^ 2) - (ensembleMean P L) ^ 2 := by
  have h : ∀ θ : Θ, P.prob θ * (L θ - ensembleMean P L) ^ 2
      = P.prob θ * (L θ) ^ 2 - 2 * ensembleMean P L * (P.prob θ * L θ)
        + (ensembleMean P L) ^ 2 * P.prob θ := fun θ => by ring
  unfold ensembleVariance
  rw [Finset.sum_congr rfl fun θ _ => h θ, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [show (∑ θ : Θ, P.prob θ * L θ) = ensembleMean P L from rfl, P.sum_one, mul_one]
  ring

end Qatlib.Papers.Trainability23.VarianceScaling
