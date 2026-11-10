/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TuraevViro10.MainResults.WrtBridge
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TuraevViro10.MainResults.ApproximationGuarantee

open Qatlib.Papers.TuraevViro10.MainResults.WrtBridge
open Qatlib.Papers.TuraevViro10.MainResults.WrtBridge.TuraevViroModel
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

theorem tvEstimate_error_le {P ι : Type*} [Fintype P] (M : TuraevViroModel P ι)
    {g : ℕ} (hg : 1 ≤ g) (x : ι) (est ε : ℝ)
    (h : |est - M.normalizedTvInvariant g x| ≤ ε) :
    |M.D ^ (2 * (g - 1)) * est - M.tvInvariant g x| ≤ M.D ^ (2 * (g - 1)) * ε := by
  have htv : M.tvInvariant g x = M.D ^ (2 * (g - 1)) * M.normalizedTvInvariant g x := by
    rw [tvInvariant_eq_D_pow_mul_normSq, normalizedTvInvariant_eq_normSq M hg x]
  have hpos : 0 < M.D ^ (2 * (g - 1)) := pow_pos M.D_pos _
  rw [htv, ← mul_sub, abs_mul, abs_of_pos hpos]
  exact mul_le_mul_of_nonneg_left h (le_of_lt hpos)

theorem probEvent_mono {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (law : FinDist Ω)
    {k : ℕ} {E F : (Fin k → Ω) → Prop} [DecidablePred E] [DecidablePred F]
    (h : ∀ ω, E ω → F ω) : law.probEvent E ≤ law.probEvent F := by
  unfold FinDist.probEvent
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact h ω hω
  · intro ω _ _
    exact Finset.prod_nonneg (fun i _ => law.nonneg (ω i))

theorem tvEstimate_failure_le {P ι Ω : Type*} [Fintype P] [Fintype Ω] [DecidableEq Ω]
    (M : TuraevViroModel P ι) {g : ℕ} (hg : 1 ≤ g) (x : ι) {k : ℕ}
    (law : FinDist Ω) (est : (Fin k → Ω) → ℝ) (ε δ : ℝ)
    (h : 1 - δ ≤ law.probEvent (fun ω => |est ω - M.normalizedTvInvariant g x| ≤ ε)) :
    1 - δ ≤ law.probEvent
      (fun ω => |M.D ^ (2 * (g - 1)) * est ω - M.tvInvariant g x| ≤
        M.D ^ (2 * (g - 1)) * ε) := by
  refine h.trans (probEvent_mono law ?_)
  intro ω hω
  exact tvEstimate_error_le M hg x (est ω) ε hω

theorem amplitudePrecision_of_tvPrecision {P ι : Type*} [Fintype P]
    (M : TuraevViroModel P ι) {g : ℕ} (hg : 1 ≤ g) (x : ι) (est ε' : ℝ) :
    |M.D ^ (2 * (g - 1)) * est - M.tvInvariant g x| ≤ ε' ↔
      |est - M.normalizedTvInvariant g x| ≤ ε' / M.D ^ (2 * (g - 1)) := by
  have hpos : 0 < M.D ^ (2 * (g - 1)) := pow_pos M.D_pos _
  have htv : M.tvInvariant g x = M.D ^ (2 * (g - 1)) * M.normalizedTvInvariant g x := by
    rw [tvInvariant_eq_D_pow_mul_normSq, normalizedTvInvariant_eq_normSq M hg x]
  rw [htv, ← mul_sub, abs_mul, abs_of_pos hpos]
  constructor
  · intro h
    rw [le_div_iff₀ hpos, mul_comm]
    exact h
  · intro h
    rw [le_div_iff₀ hpos, mul_comm] at h
    exact h

theorem approximation_algorithm_guarantee {P ι Ω : Type*} [Fintype P] [Fintype Ω]
    [DecidableEq Ω] (M : TuraevViroModel P ι) {g : ℕ} (hg : 1 ≤ g) (x : ι)
    {k : ℕ} (law : FinDist Ω) (est : (Fin k → Ω) → ℝ) (ε δ : ℝ)
    (h : 1 - δ ≤ law.probEvent (fun ω => |est ω - M.normalizedTvInvariant g x| ≤ ε)) :
    1 - δ ≤ law.probEvent
        (fun ω => |M.D ^ (2 * (g - 1)) * est ω - M.tvInvariant g x| ≤
          M.D ^ (2 * (g - 1)) * ε) ∧
      (1 - δ ≤ law.probEvent
        (fun ω => |est ω - M.normalizedTvInvariant g x| ≤ ε)) :=
  ⟨tvEstimate_failure_le M hg x law est ε δ h, h⟩

end Qatlib.Papers.TuraevViro10.MainResults.ApproximationGuarantee
