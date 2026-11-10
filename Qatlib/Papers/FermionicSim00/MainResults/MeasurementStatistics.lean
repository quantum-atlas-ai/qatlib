/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Qatlib.Papers.FermionicSim00.MainResults

theorem variance_sum_le_card {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {m : ℕ} (X : Fin m → Ω → ℝ)
    (hX : ∀ j, AEMeasurable (X j) μ)
    (hb : ∀ j, ∀ᵐ ω ∂μ, X j ω ∈ Set.Icc (-1 : ℝ) 1)
    (hindep : ∀ i j : Fin m, i ≠ j → IndepFun (X i) (X j) μ) :
    variance (fun ω => ∑ j, X j ω) μ ≤ (m : ℝ) := by
  have hmem : ∀ j, MemLp (X j) 2 μ := fun j =>
    memLp_of_bounded (hb j) (hX j).aestronglyMeasurable 2
  have hvar : variance (fun ω => ∑ j, X j ω) μ = ∑ j, variance (X j) μ := by
    have h := IndepFun.variance_sum (s := (Finset.univ : Finset (Fin m)))
      (fun i _ => hmem i) (fun i _ j _ hij => hindep i j hij)
    convert h using 2
    ext ω
    simp [Finset.sum_apply]
  calc variance (fun ω => ∑ j, X j ω) μ = ∑ j, variance (X j) μ := hvar
    _ ≤ ∑ _j : Fin m, (1 : ℝ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h := variance_le_sq_of_bounded (a := -1) (b := 1) (hb j) (hX j)
        simpa using h
    _ = (m : ℝ) := by simp

theorem std_of_sample_count {m : ℕ} (hm : 0 < m) (ε : ℝ) (hε : 0 < ε) :
    Real.sqrt ((m : ℝ) / (Nat.ceil ((m : ℝ) / ε ^ 2) : ℝ)) ≤ ε := by
  have hε2 : 0 < ε ^ 2 := by positivity
  have hq : 0 < (m : ℝ) / ε ^ 2 := by
    refine div_pos ?_ hε2
    exact_mod_cast hm
  set K : ℝ := (Nat.ceil ((m : ℝ) / ε ^ 2) : ℝ) with hKdef
  have hKpos : 0 < K := lt_of_lt_of_le hq (Nat.le_ceil _)
  have hceil : (m : ℝ) / ε ^ 2 ≤ K := Nat.le_ceil _
  have hmK : (m : ℝ) ≤ K * ε ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hceil hε2.le
    have hdiv : (m : ℝ) / ε ^ 2 * ε ^ 2 = (m : ℝ) := by
      field_simp
    rwa [hdiv] at h
  have hle : (m : ℝ) / K ≤ ε ^ 2 := by
    rw [div_le_iff₀ hKpos]
    linarith
  calc Real.sqrt ((m : ℝ) / K) ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt hle
    _ = ε := Real.sqrt_sq hε.le

theorem sample_count_le (m : ℕ) (ε : ℝ) :
    (Nat.ceil ((m : ℝ) / ε ^ 2) : ℝ) ≤ (m : ℝ) / ε ^ 2 + 1 := by
  have hq : (0 : ℝ) ≤ (m : ℝ) / ε ^ 2 := by positivity
  have h := Nat.ceil_lt_add_one hq
  linarith

theorem statistical_noise_bound (mA mB : ℕ) (ε : ℝ) (hε : 0 < ε) (hm : 0 < mA * mB) :
    Real.sqrt (((mA * mB : ℕ) : ℝ)
        / (Nat.ceil (((mA * mB : ℕ) : ℝ) / ε ^ 2) : ℝ)) ≤ ε ∧
    (Nat.ceil (((mA * mB : ℕ) : ℝ) / ε ^ 2) : ℝ) ≤ ((mA * mB : ℕ) : ℝ) / ε ^ 2 + 1 := by
  refine ⟨std_of_sample_count hm ε hε, sample_count_le (mA * mB) ε⟩

end Qatlib.Papers.FermionicSim00.MainResults
