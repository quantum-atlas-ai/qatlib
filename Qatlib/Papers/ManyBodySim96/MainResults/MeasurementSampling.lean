/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Sampling accuracy with simulation error

For finite-distribution observables taking values in `[0, 1]`, this module bounds the variance
by `1 / 4` and derives a Chebyshev estimate for repeated independent samples. `sampleCount`
selects a sufficient number of samples, and `measurement_accuracy_with_simulation` adds a
supplied bias bound to the sampling tolerance.

The mathematical setting is that of [Wiesner1996].

## Main statements

* `repeated_measurement_accuracy`: For an observable valued in `[0, 1]`, the selected
  independent sample average differs from its expectation by more than `δ` with probability at
  most `η`.
* `measurement_accuracy_with_simulation`: If the expectation is within `eobs` of a target `μ`,
  the selected sample average differs from `μ` by more than `eobs + δ` with probability at most
  `η`.

## References

* [Wiesner, 1996][Wiesner1996]
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.ManyBodySim96.MainResults

variable {X : Type} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in

/-- The expectation of a function valued in `[0, 1]` also lies in `[0, 1]`. -/
theorem expect_mem_unit (p : FinDist X) (f : X → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    0 ≤ p.expect f ∧ p.expect f ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun x _ => mul_nonneg (p.nonneg x) (hf0 x)
  · calc p.expect f ≤ ∑ x, p.prob x * 1 := by
          apply Finset.sum_le_sum
          intro x _
          exact mul_le_mul_of_nonneg_left (hf1 x) (p.nonneg x)
      _ = 1 := by simp [p.sum_one]

/-- A function valued in `[0, 1]` has variance at most `1 / 4` under a finite probability
distribution. -/
theorem variance_le_quarter (p : FinDist X) (f : X → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    p.variance f ≤ 1 / 4 := by
  obtain ⟨hμ0, hμ1⟩ := expect_mem_unit p f hf0 hf1
  rw [FinDist.variance_eq_expect_sq_sub]
  have hsq : p.expect (fun x => (f x) ^ 2) ≤ p.expect f := by
    unfold FinDist.expect
    apply Finset.sum_le_sum
    intro x _
    have hx : (f x) ^ 2 ≤ f x := by nlinarith [hf0 x, hf1 x]
    exact mul_le_mul_of_nonneg_left hx (p.nonneg x)
  nlinarith [sq_nonneg (p.expect f - 1 / 2)]

/-- For positive sample size and tolerance, the probability that the empirical average differs
from its expectation by more than `δ` is at most `1 / (4 * L * δ ^ 2)`. -/
theorem avg_tail_quarter {L : ℕ} (p : FinDist X) (f : X → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hL : 0 < L) (δ : ℝ) (hδ : 0 < δ) :
    p.probEvent (L := L) (fun ω : Fin L → X => δ < |FinDist.avg f ω - p.expect f|) ≤
      1 / (4 * (L : ℝ) * δ ^ 2) := by
  have hcheb := FinDist.chebyshev_avg p f hL δ hδ
  have hquarter := variance_le_quarter p f hf0 hf1
  have hden : (0 : ℝ) ≤ (L : ℝ) * δ ^ 2 := by positivity
  calc p.probEvent (L := L) (fun ω : Fin L → X => δ < |FinDist.avg f ω - p.expect f|)
      ≤ p.variance f / ((L : ℝ) * δ ^ 2) := hcheb
    _ ≤ (1 / 4) / ((L : ℝ) * δ ^ 2) := div_le_div_of_nonneg_right hquarter hden
    _ = 1 / (4 * (L : ℝ) * δ ^ 2) := by ring

/-- Selects `max 1 (ceil(1 / (4 * δ ^ 2 * η)))` samples for tolerance `δ` and failure bound `η`. -/
def sampleCount (δ η : ℝ) : ℕ :=
  max 1 (Nat.ceil (1 / (4 * δ ^ 2 * η)))

/-- The selected sample count is always positive. -/
theorem sampleCount_pos (δ η : ℝ) : 0 < sampleCount δ η := by
  unfold sampleCount
  omega

/-- Positive tolerance and failure bound make the selected sample count's Chebyshev bound at
most `η`. -/
theorem sampleCount_tail (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) :
    1 / (4 * (sampleCount δ η : ℝ) * δ ^ 2) ≤ η := by
  have hLpos : (0 : ℝ) < (sampleCount δ η : ℝ) := by
    exact_mod_cast sampleCount_pos δ η
  have hpos : (0 : ℝ) < 4 * δ ^ 2 * η := by positivity
  have hceil : 1 / (4 * δ ^ 2 * η) ≤ (Nat.ceil (1 / (4 * δ ^ 2 * η)) : ℝ) :=
    Nat.le_ceil _
  have hle : (1 : ℝ) / (4 * δ ^ 2 * η) ≤ (sampleCount δ η : ℝ) :=
    hceil.trans (by exact_mod_cast le_max_right 1 _)
  have hmul : 1 ≤ (sampleCount δ η : ℝ) * (4 * δ ^ 2 * η) := by
    have := (div_le_iff₀ hpos).mp hle
    simpa [mul_comm] using this
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (sampleCount δ η : ℝ) * δ ^ 2)]
  nlinarith [hmul]

/-- For an observable valued in `[0, 1]`, the selected independent sample average differs from
its expectation by more than `δ` with probability at most `η`. -/
theorem repeated_measurement_accuracy (p : FinDist X) (f : X → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) :
    p.probEvent (L := sampleCount δ η)
        (fun ω => δ < |FinDist.avg f ω - p.expect f|) ≤ η := by
  refine (avg_tail_quarter p f hf0 hf1 (sampleCount_pos δ η) δ hδ).trans
    (sampleCount_tail δ η hδ hη)

omit [DecidableEq X] in

/-- Pointwise implication between sample events gives the corresponding inequality between their
probabilities. -/
theorem probEvent_le_of_imp {L : ℕ} (p : FinDist X) {E F : (Fin L → X) → Prop}
    [DecidablePred E] [DecidablePred F] (h : ∀ ω, E ω → F ω) :
    p.probEvent (L := L) E ≤ p.probEvent (L := L) F := by
  unfold FinDist.probEvent
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact h ω hω
  · intro ω _ _
    exact Finset.prod_nonneg fun i _ => p.nonneg (ω i)

/-- If the expectation is within `eobs` of a target `μ`, the selected sample average differs
from `μ` by more than `eobs + δ` with probability at most `η`. [Wiesner1996] -/
theorem measurement_accuracy_with_simulation (p : FinDist X) (f : X → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (μ eobs δ η : ℝ) (hμ : |p.expect f - μ| ≤ eobs)
    (hδ : 0 < δ) (hη : 0 < η) :
    p.probEvent (L := sampleCount δ η)
        (fun ω => eobs + δ < |FinDist.avg f ω - μ|) ≤ η := by
  have himp : ∀ ω : Fin (sampleCount δ η) → X,
      eobs + δ < |FinDist.avg f ω - μ| →
      δ < |FinDist.avg f ω - p.expect f| := by
    intro ω hω
    have htri : |FinDist.avg f ω - μ| - |p.expect f - μ| ≤
        |FinDist.avg f ω - p.expect f| := by
      have h1 := abs_sub_abs_le_abs_sub (FinDist.avg f ω - μ) (p.expect f - μ)
      have h2 : (FinDist.avg f ω - μ) - (p.expect f - μ) =
          FinDist.avg f ω - p.expect f := by ring
      rwa [h2] at h1
    have h2 : |p.expect f - μ| ≤ eobs := by simpa [abs_sub_comm] using hμ
    linarith
  exact (probEvent_le_of_imp p himp).trans
    (repeated_measurement_accuracy p f hf0 hf1 δ η hδ hη)

end Qatlib.Papers.ManyBodySim96.MainResults
