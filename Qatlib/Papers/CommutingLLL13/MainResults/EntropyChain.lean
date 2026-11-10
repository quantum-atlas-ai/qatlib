/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutingLLL13.MainResults.BinomialBound
import QuantumInfo.ClassicalInfo.Entropy
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open scoped BigOperators

noncomputable section

namespace Qatlib.Papers.CommutingLLL13.MainResults.EntropyChain

variable {O : Type} [Fintype O]

noncomputable def failProb (p : ProbDistribution O) (f : O → ℕ) (T : ℕ) : ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s => f s = T), (p s : ℝ)

noncomputable def failWeight (p : ProbDistribution O) (f : O → ℕ) : ℝ :=
  ∑ s, (p s : ℝ) * (f s : ℝ)

theorem failProb_mul_le_weight (p : ProbDistribution O) (f : O → ℕ) (T : ℕ) :
    (T : ℝ) * failProb p f T ≤ failWeight p f := by
  unfold failProb failWeight
  have hsubset : ∑ s ∈ Finset.univ.filter (fun s => f s = T), (p s : ℝ) * (f s : ℝ)
      ≤ ∑ s, (p s : ℝ) * (f s : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro s _ _
    exact mul_nonneg (p s).zero_le_coe (Nat.cast_nonneg _)
  have heq : ∑ s ∈ Finset.univ.filter (fun s => f s = T), (p s : ℝ) * (f s : ℝ)
      = (T : ℝ) * ∑ s ∈ Finset.univ.filter (fun s => f s = T), (p s : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mem_filter] at hs
    rw [hs.2]; ring
  rw [← heq]
  exact hsubset

theorem kappa_mul_weight_le
    (n N m : ℕ) (k r g logT H Ssum Q : ℝ)
    (hr : 0 < r) (hg : 0 < g)
    (hclaim : (n + N : ℝ) ≤ H + Ssum)
    (hS : Ssum ≤ (N + n : ℝ) - (k - Real.log r) * Q)
    (hH : H ≤ logT + (m : ℝ) + Real.log (g * Real.exp 1) * Q) :
    (k - Real.log (g * r * Real.exp 1)) * Q ≤ logT + (m : ℝ) := by
  have hlog : Real.log (g * r * Real.exp 1) = Real.log r + Real.log (g * Real.exp 1) := by
    rw [show g * r * Real.exp 1 = r * (g * Real.exp 1) by ring]
    exact Real.log_mul hr.ne' (by positivity)
  have hbox : k - Real.log r - Real.log (g * Real.exp 1)
      = k - Real.log (g * r * Real.exp 1) := by
    rw [hlog]; ring
  have h1 : (n + N : ℝ)
      ≤ logT + (m : ℝ) + (N + n : ℝ)
        - (k - Real.log r - Real.log (g * Real.exp 1)) * Q := by
    have h := add_le_add hH hS
    linarith
  rw [hbox] at h1
  linarith

theorem eq5_failure_bound
    (p : ProbDistribution O) (f : O → ℕ) (T : ℕ) (hT : 0 < T)
    (n N m : ℕ) (k r g : ℝ) (hr : 0 < r) (hg : 0 < g)
    (H Ssum : ℝ)
    (hclaim : (n + N : ℝ) ≤ H + Ssum)
    (hS : Ssum ≤ (N + n : ℝ) - (k - Real.log r) * failWeight p f)
    (hH : H ≤ Real.log T + (m : ℝ) + Real.log (g * Real.exp 1) * failWeight p f)
    (hκ : 0 < k - Real.log (g * r * Real.exp 1)) :
    failProb p f T
      ≤ (Real.log T + (m : ℝ)) / ((T : ℝ) * (k - Real.log (g * r * Real.exp 1))) := by
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hk := kappa_mul_weight_le n N m k r g (Real.log T) H Ssum
    (failWeight p f) hr hg hclaim hS hH
  have hw := failProb_mul_le_weight p f T

  have hpT : (T : ℝ) * failProb p f T * (k - Real.log (g * r * Real.exp 1))
      ≤ Real.log T + (m : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hw (le_of_lt hκ)
    have hmul2 := mul_le_mul_of_nonneg_right hk (le_of_lt hTpos)
    nlinarith [hmul, hmul2]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (T : ℝ) * (k - Real.log (g * r * Real.exp 1)))]
  have hgoal : failProb p f T * ((T : ℝ) * (k - Real.log (g * r * Real.exp 1)))
      = (T : ℝ) * failProb p f T * (k - Real.log (g * r * Real.exp 1)) := by ring
  rw [hgoal]
  exact hpT

end Qatlib.Papers.CommutingLLL13.MainResults.EntropyChain
