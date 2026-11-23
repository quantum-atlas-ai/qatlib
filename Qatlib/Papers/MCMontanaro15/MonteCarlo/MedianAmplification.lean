/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.AmplitudeCore.PayoffMedian.QuantumPayoffEstimation

@[expose] public section

/-!
# Explicit median-amplification failure bound

Theorem 3 of [Montanaro2015] repeats the amplitude-estimation circuit `2 * r + 1` times and reads
the sorted median. The locked library proves the per-`r` failure bound
`2^(2 * r + 1) * (1 - 8 / π^2)^(r + 1)` (`quantum_mean_sorted_median_amplification`); this
module restates it in the form the paper uses, where `δ ∈ (0, 1)` is a free parameter and the
median count is required to satisfy that explicit inequality.

## Main statements

* `mean_median_failure_le_delta`: the median failure event of the amplitude-estimation law has
  probability at most `δ` whenever `2^(2 * r + 1) * (1 - 8 / π^2)^(r + 1) ≤ δ`.
* `exists_median_count_for_delta`: for every `δ ∈ (0, 1)` there is a positive median count whose
  failure probability is at most `δ`; the count is chosen from the geometric decay of the
  amplification budget.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Papers.MCMontanaro15.MonteCarlo

open Matrix
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open scoped BigOperators

variable {I : Type} [Fintype I] [DecidableEq I]

/-- For a bounded payoff, a grid size of at least two, and a median count whose amplification
budget is at most `δ`, the sorted median of `2 * r + 1` amplitude estimates deviates from the
payoff mean by more than the amplitude-estimation window with probability at most `δ`. This is
[Montanaro2015], Theorem 3 with the confidence parameter `δ` left free. -/
theorem mean_median_failure_le_delta (M r : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ) (j : I)
    (f : I → ℝ) (hA : A ∈ Matrix.unitaryGroup I ℂ) (hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1)
    (δ : ℝ) (_hδ0 : 0 < δ) (_hδ1 : δ < 1)
    (hδ : (2 : ℝ) ^ (2 * r + 1) * (1 - 8 / Real.pi ^ 2) ^ (r + 1) ≤ δ) :
    let μ := ∑ i, BornProb (ApplyGate A (Ket j)) i * f i
    (meanLaw M A j f hA hf hM).probEvent
        (fun ω => 2 * Real.pi * Real.sqrt (μ * (1 - μ)) / (M : ℝ) + Real.pi ^ 2 / (M : ℝ) ^ 2
          < |meanMedian r M ω - μ|)
      ≤ δ := by
  intro μ
  exact (quantum_mean_sorted_median_amplification M r hM A j f hA hf).trans hδ

/-- The locked median-amplification budget is bounded by the geometric sequence
`(2 / 5) * (4 / 5)^r`. The estimate `1 - 8 / π^2 ≤ 1 / 5` follows from `π^2 < 10`. -/
private theorem median_budget_le_geometric (r : ℕ) :
    (2 : ℝ) ^ (2 * r + 1) * (1 - 8 / Real.pi ^ 2) ^ (r + 1)
      ≤ (2 / 5) * (4 / 5 : ℝ) ^ r := by
  have hpi2 : Real.pi ^ 2 < 10 := by
    have h1 : Real.pi * Real.pi < 3.1416 * Real.pi :=
      mul_lt_mul_of_pos_right Real.pi_lt_d4 Real.pi_pos
    have h2 : (3.1416 : ℝ) * Real.pi < 3.1416 * 3.1416 :=
      mul_lt_mul_of_pos_left Real.pi_lt_d4 (by norm_num)
    nlinarith [h1, h2]
  have hpi2pos : 0 < Real.pi ^ 2 := by positivity
  have hbase_nonneg : 0 ≤ 1 - 8 / Real.pi ^ 2 := by
    rw [sub_nonneg, div_le_one hpi2pos]
    nlinarith [Real.pi_gt_three]
  have hbase : 1 - 8 / Real.pi ^ 2 ≤ 1 / 5 := by
    have h8 : (4 / 5 : ℝ) ≤ 8 / Real.pi ^ 2 := by
      rw [le_div_iff₀ hpi2pos]
      nlinarith
    linarith
  have hpow2 : (2 : ℝ) ^ (2 * r + 1) = 2 * (4 : ℝ) ^ r := by
    rw [pow_succ, pow_mul]
    norm_num
    rw [mul_comm]
  calc (2 : ℝ) ^ (2 * r + 1) * (1 - 8 / Real.pi ^ 2) ^ (r + 1)
      ≤ (2 * (4 : ℝ) ^ r) * (1 / 5 : ℝ) ^ (r + 1) := by
        rw [hpow2]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase_nonneg hbase (r + 1))
          (by positivity)
    _ = (2 / 5) * (4 / 5 : ℝ) ^ r := by
        calc (2 * 4 ^ r) * (1 / 5 : ℝ) ^ (r + 1)
            = (2 * 4 ^ r) * ((1 / 5) ^ r * (1 / 5)) := by rw [pow_succ]
          _ = (2 / 5) * (4 ^ r * (1 / 5) ^ r) := by ring
          _ = (2 / 5) * ((4 * (1 / 5 : ℝ)) ^ r) := by rw [← mul_pow]
          _ = (2 / 5) * (4 / 5 : ℝ) ^ r := by norm_num

/-- For every confidence `δ ∈ (0, 1)` there is a uniform positive median index `r`, using
`2 * r + 1` fresh estimates, for which the amplitude-estimation median fails with probability
at most `δ`. This is the confidence component of [Montanaro2015], Theorem 3. -/
theorem exists_median_count_for_delta (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ r : ℕ, 1 ≤ r ∧
      ∀ {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
        (M : ℕ) (hM : 2 ≤ M) (A : Matrix J J ℂ) (j : J) (f : J → ℝ)
        (hA : A ∈ Matrix.unitaryGroup J ℂ) (hf : ∀ i, f i ∈ Set.Icc (0 : ℝ) 1),
      (meanLaw M A j f hA hf hM).probEvent
          (fun ω => 2 * Real.pi * Real.sqrt ((∑ i, BornProb (ApplyGate A (Ket j)) i * f i)
              * (1 - ∑ i, BornProb (ApplyGate A (Ket j)) i * f i)) / (M : ℝ)
            + Real.pi ^ 2 / (M : ℝ) ^ 2
            < |meanMedian r M ω - ∑ i, BornProb (ApplyGate A (Ket j)) i * f i|)
        ≤ δ := by
  obtain ⟨r, hr, hgeom⟩ :
      ∃ r : ℕ, 1 ≤ r ∧ (2 / 5) * (4 / 5 : ℝ) ^ r ≤ δ := by
    obtain ⟨n, hn⟩ :=
      exists_pow_lt_of_lt_one (show 0 < δ / (2 / 5) by positivity)
        (by norm_num : (4 / 5 : ℝ) < 1)
    refine ⟨max 1 n, le_max_left _ _, ?_⟩
    have hmono : (4 / 5 : ℝ) ^ max 1 n ≤ (4 / 5 : ℝ) ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_right _ _)
    have hstep : (2 / 5) * (4 / 5 : ℝ) ^ max 1 n ≤ (2 / 5) * (4 / 5 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_left hmono (by norm_num)
    have hscale : (2 / 5) * (4 / 5 : ℝ) ^ n < δ := by
      have := mul_lt_mul_of_pos_left hn (by norm_num : (0 : ℝ) < 2 / 5)
      field_simp at this ⊢
      linarith
    linarith
  refine ⟨r, hr, ?_⟩
  intro J _ _ _ M hM A j f hA hf
  have hmain := mean_median_failure_le_delta M r hM A j f hA hf δ hδ0 hδ1
    (le_trans (median_budget_le_geometric r) hgeom)
  dsimp only at hmain
  exact hmain

end Qatlib.Papers.MCMontanaro15.MonteCarlo
