/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyDecision.CollectiveRisk.Data.CollectiveOptimum
import Qatlib.Concepts.CopyDecision.FreshPolicies.Data.AntiTrineUpper
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Asymptotic Ratio

Fresh Policies constructions for Copy Decision.
Proves `adaptiveUpper_scaled`, `causalPolicyOptimum_scaled_bounds`, `causalPolicyOptimum_uniform_asymptotic`.
-/


set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.CopyDecision.FreshPolicies.Data
open Qatlib.Concepts.CopyDecision.CollectiveRisk.Data Qatlib.Concepts.CopyDecision.QubitMeasure.Data Qatlib.Foundations.DecisionRisk.HarmonicError Qatlib.Foundations.DecisionRisk.RiskPartition
open Filter Topology

/-- The stated copy-decision construction satisfies `adaptiveUpper_scaled` with the complete displayed premises. -/
lemma adaptiveUpper_scaled (n : ℕ) :
    ((1-Real.sqrt (1-(1/4:ℝ)^n))/2)/(1/4:ℝ)^(n+1)=
      2/(1+Real.sqrt (1-(1/4:ℝ)^n)) := by
  have hx : 0 < (1/4:ℝ)^n := by positivity
  have hx1 : (1/4:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hs := Real.sq_sqrt (sub_nonneg.2 hx1)
  have hd : 1+Real.sqrt (1-(1/4:ℝ)^n) ≠ 0 := by positivity
  rw [pow_succ]
  field_simp
  nlinarith only [hs]

/-- The stated copy-decision construction satisfies `causalPolicyOptimum_scaled_bounds` with the complete displayed premises. -/
theorem causalPolicyOptimum_scaled_bounds (n : ℕ) :
    1/(1+(1/2:ℝ)^n) ≤ causalPolicyOptimum (n+1) (fun _ => 1/3)/(1/4:ℝ)^(n+1) ∧
    causalPolicyOptimum (n+1) (fun _ => 1/3)/(1/4:ℝ)^(n+1) ≤
      2/(1+Real.sqrt (1-(1/4:ℝ)^n)) := by
  have hx : 0 < (1/4:ℝ)^(n+1) := by positivity
  constructor
  · apply (le_div_iff₀ hx).2
    convert causalPolicyOptimum_uniform_lower n using 1
    ring
  · rw [← adaptiveUpper_scaled]
    exact div_le_div_of_nonneg_right (causalPolicyOptimum_uniform_upper n) hx.le

/-- Optimal sequential error has leading coefficient one at scale 4^(-N). -/
theorem causalPolicyOptimum_uniform_asymptotic :
    Tendsto (fun N => causalPolicyOptimum N (fun _ => 1/3)/(1/4:ℝ)^N)
      atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have ht4 : Tendsto (fun n : ℕ => (1/4:ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h1 : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h2 : Tendsto (fun _ : ℕ => (2:ℝ)) atTop (𝓝 2) := tendsto_const_nhds
  have hl : Tendsto (fun n : ℕ => 1/(1+(1/2:ℝ)^n)) atTop (𝓝 1) := by
    convert h1.div (h1.add ht) (by norm_num) using 1
    norm_num
  have hs : Tendsto (fun n : ℕ => Real.sqrt (1-(1/4:ℝ)^n)) atTop (𝓝 1) := by
    convert (tendsto_const_nhds.sub ht4).sqrt using 1
    norm_num
  have hu : Tendsto (fun n : ℕ => 2/(1+Real.sqrt (1-(1/4:ℝ)^n))) atTop (𝓝 1) := by
    convert h2.div (h1.add hs) (by norm_num) using 1
    norm_num
  apply (tendsto_add_atTop_iff_nat 1).1
  exact hl.squeeze hu (fun n => (causalPolicyOptimum_scaled_bounds n).1)
    (fun n => (causalPolicyOptimum_scaled_bounds n).2)

/-- The stated copy-decision construction satisfies `trineSignedOverlap_sq` with the complete displayed premises. -/
lemma trineSignedOverlap_sq (N : ℕ) : (trineSignedOverlap N)^2=(1/4:ℝ)^N := by
  unfold trineSignedOverlap
  rw [← pow_mul, Nat.mul_comm N 2, pow_mul]
  norm_num

/-- The stated copy-decision construction satisfies `collectiveOptimum_scaled_bounds` with the complete displayed premises. -/
theorem collectiveOptimum_scaled_bounds (n : ℕ) :
    1/(2*(1+(1/2:ℝ)^(n+2))) ≤ collectiveOptimum (n+2) (fun _ => 1/3)/(1/4:ℝ)^(n+2) ∧
    collectiveOptimum (n+2) (fun _ => 1/3)/(1/4:ℝ)^(n+2) ≤
      2/(Real.sqrt (1+2*trineSignedOverlap (n+2))+Real.sqrt (1-trineSignedOverlap (n+2)))^2 := by
  have hx : 0 < (1/4:ℝ)^(n+2) := by positivity
  constructor
  · apply (le_div_iff₀ hx).2
    convert collectiveOptimum_uniform_lower (n+2) using 1
    ring
  · have h := div_le_div_of_nonneg_right (collectiveOptimum_uniform_upper n) hx.le
    rw [trineSignedOverlap_sq] at h
    convert h using 1
    have hd : (Real.sqrt (1+2*trineSignedOverlap (n+2))+
        Real.sqrt (1-trineSignedOverlap (n+2))) ≠ 0 := by
      have hm := (trineSignedOverlap_valid n).1
      have hp := (trineSignedOverlap_valid n).2
      positivity
    field_simp

/-- Collective optimum is squeezed by actual full-space POVMs, with leading
coefficient one half; finite-N exact PGM optimality is not assumed. -/
theorem collectiveOptimum_uniform_asymptotic :
    Tendsto (fun N => collectiveOptimum N (fun _ => 1/3)/(1/4:ℝ)^N)
      atTop (𝓝 (1/2)) := by
  have ht : Tendsto (fun n : ℕ => (1/2:ℝ)^(n+2)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_add_atTop_nat 2)
  have hsign : Tendsto (fun n : ℕ => trineSignedOverlap (n+2)) atTop (𝓝 0) := by
    exact (tendsto_pow_atTop_nhds_zero_iff.2 (by norm_num : |(-1/2:ℝ)| < 1)).comp
      (tendsto_add_atTop_nat 2)
  have h1 : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h2 : Tendsto (fun _ : ℕ => (2:ℝ)) atTop (𝓝 2) := tendsto_const_nhds
  have hl : Tendsto (fun n : ℕ => 1/(2*(1+(1/2:ℝ)^(n+2)))) atTop (𝓝 (1/2)) := by
    convert h1.div (h2.mul (h1.add ht)) (by norm_num) using 1
    norm_num
  have hv : Tendsto (fun n : ℕ => Real.sqrt (1+2*trineSignedOverlap (n+2))) atTop (𝓝 1) := by
    simpa using (h1.add (h2.mul hsign)).sqrt
  have hu : Tendsto (fun n : ℕ => Real.sqrt (1-trineSignedOverlap (n+2))) atTop (𝓝 1) := by
    simpa using (h1.sub hsign).sqrt
  have hupper : Tendsto (fun n : ℕ =>
      2/(Real.sqrt (1+2*trineSignedOverlap (n+2))+Real.sqrt (1-trineSignedOverlap (n+2)))^2)
      atTop (𝓝 (1/2)) := by
    convert h2.div ((hv.add hu).pow 2) (by norm_num) using 1
    norm_num
  apply (tendsto_add_atTop_iff_nat 2).1
  exact hl.squeeze hupper (fun n => (collectiveOptimum_scaled_bounds n).1)
    (fun n => (collectiveOptimum_scaled_bounds n).2)

/-- Same-copy optimal sequential/collective error ratio tends to two. -/
theorem trine_optimal_error_ratio :
    Tendsto (fun N => causalPolicyOptimum N (fun _ => 1/3)/collectiveOptimum N (fun _ => 1/3))
      atTop (𝓝 2) := by
  have h := causalPolicyOptimum_uniform_asymptotic.div
    collectiveOptimum_uniform_asymptotic (by norm_num : (1/2:ℝ) ≠ 0)
  have h' := h.congr (fun N => div_div_div_cancel_right₀
    (by positivity : (1/4:ℝ)^N ≠ 0) _ _)
  simpa using h'

end Qatlib.Concepts.CopyDecision.FreshPolicies.Data
