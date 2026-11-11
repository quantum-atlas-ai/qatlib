/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyDecision.FreshPolicies.Data.AsymptoticRatio
import Qatlib.Concepts.CopyDecision.CollectiveRisk.Data.GeneralCollectiveOptimum
import Qatlib.Concepts.CopyDecision.FreshPolicies.Data.SequentialOptimum

/-! Original OQ #145 fixed-copy trine comparison. This extension is separately
attributed to its source research; Jeong et al. do not claim this arbitrary-POVM
asymptotic ratio. All native/relaxed/collective model distinctions are retained. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.SeqQsdJeong26.TrineExample
open Qatlib.Concepts.CopyDecision.CollectiveRisk.Data Qatlib.Concepts.CopyDecision.FreshPolicies.Data Qatlib.Concepts.CopyDecision.QubitMeasure.Data Qatlib.Foundations.DecisionRisk.HarmonicError Qatlib.Foundations.DecisionRisk.RiskPartition
open Filter Topology

/-- The stated copy-decision construction satisfies `generalCollectiveOptimum_uniform_pos` with the complete displayed premises. -/
theorem generalCollectiveOptimum_uniform_pos (N : ℕ) :
    0 < generalCollectiveOptimum N (fun _ => (1/3:ℝ)) := by
  rw [generalCollectiveOptimum_eq_finite _ _ (by intro i; norm_num)]
  exact lt_of_lt_of_le (by positivity) (collectiveOptimum_uniform_lower N)

/-- Full arbitrary-outcome collective decoding has the same sharp coefficient. -/
theorem generalCollectiveOptimum_uniform_asymptotic :
    Tendsto (fun N => generalCollectiveOptimum N (fun _ => 1/3)/(1/4:ℝ)^N)
      atTop (𝓝 (1/2)) := by
  have he (N : ℕ) := generalCollectiveOptimum_eq_finite N (fun _ => (1/3:ℝ)) (by intro i; norm_num)
  simpa only [he] using collectiveOptimum_uniform_asymptotic

/-- Same-copy ratio for native full-kernel controllers against arbitrary joint
observations and measurable randomized terminal guesses. -/
theorem trine_causal_general_error_ratio :
    Tendsto (fun N => causalPolicyOptimum N (fun _ => 1/3)/generalCollectiveOptimum N (fun _ => 1/3))
      atTop (𝓝 2) := by
  have he (N : ℕ) := generalCollectiveOptimum_eq_finite N (fun _ => (1/3:ℝ)) (by intro i; norm_num)
  simpa only [he] using trine_optimal_error_ratio

/-- Even the larger class of measurable-error mixtures cannot improve the
native infimum. Thus allowing independent external program randomization or
bounded early stopping (via the same-risk padding bridge) preserves ratio two. -/
theorem trine_mixture_general_error_ratio :
    Tendsto (fun N => mixtureOptimum N/generalCollectiveOptimum N (fun _ => 1/3)) atTop (𝓝 2) := by
  simpa only [mixtureOptimum_eq_causal] using trine_causal_general_error_ratio

/-- The stated copy-decision construction satisfies `trine_error_ratio_eventually_gt_one` with the complete displayed premises. -/
theorem trine_error_ratio_eventually_gt_one :
    ∀ᶠ N : ℕ in atTop, (3/2:ℝ) < mixtureOptimum N/generalCollectiveOptimum N (fun _ => 1/3) :=
  trine_mixture_general_error_ratio.eventually (Ioi_mem_nhds (by norm_num : (3/2:ℝ) < 2))

/-- Any physical presentation actually embedded between finite adaptive trees
and the proved mixture enlargement has this SAME infimum. The hypotheses are
class maps, never an assumed error inequality or asymptotic endpoint. -/
theorem sequentialRiskSet_optimum {N : ℕ} (S : Set ℝ)
    (hfinite : finitePOVMRisks N (fun _ => 1/3) ⊆ S) (hmixture : S ⊆ mixtureRisks N) :
    sInf S=causalPolicyOptimum N (fun _ => 1/3) := by
  have hS := (finitePOVMRisks_nonempty N (fun _ => (1/3:ℝ))).mono hfinite
  have hb := (mixtureRisks_bddBelow N).mono hmixture
  apply le_antisymm
  · rw [causalPolicyOptimum_eq_finite _ _ (by intro i; norm_num)]
    exact csInf_le_csInf hb (finitePOVMRisks_nonempty N _) hfinite
  · rw [← mixtureOptimum_eq_causal]
    exact csInf_le_csInf (mixtureRisks_bddBelow N) hS hmixture

end Qatlib.Papers.SeqQsdJeong26.TrineExample
