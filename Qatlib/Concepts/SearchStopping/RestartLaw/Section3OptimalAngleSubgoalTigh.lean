/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.RestartLaw.Section3OptimalAngleSubgoalStat
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.BigOperators
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.ModuleTopology
set_option warningAsError false

namespace Qatlib.Concepts.SearchStopping.RestartLaw

open Finset Filter

private theorem angleTerms_antitone (x : ℝ) (hx : 0 ≤ x) (hu : x ≤ 5 / 4) (d : ℕ) :
    Antitone (fun n : ℕ => x ^ (2 * n + d) / ((2 * n + d).factorial : ℝ)) := by
  apply antitone_nat_of_succ_le
  intro n
  let m := 2 * n + d
  have he : 2 * (n + 1) + d = m + 2 := by dsimp [m]; omega
  have hf : ((m + 2).factorial : ℝ) =
      ((m : ℝ) + 2) * ((m : ℝ) + 1) * (m.factorial : ℝ) := by
    rw [show m + 2 = (m + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  have hsq : x ^ 2 ≤ 2 := by nlinarith
  have hm : (2 : ℝ) ≤ ((m : ℝ) + 2) * ((m : ℝ) + 1) := by
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith [sq_nonneg (m : ℝ)]
  have hfp : (0 : ℝ) < (m.factorial : ℝ) := by positivity
  have hfp2 : (0 : ℝ) < ((m + 2).factorial : ℝ) := by positivity
  change x ^ (2 * (n + 1) + d) / _ ≤ x ^ m / _
  rw [he, pow_add, div_le_div_iff₀ hfp2 hfp]
  calc
    x ^ m * x ^ 2 * (m.factorial : ℝ) ≤
        x ^ m * (((m : ℝ) + 2) * ((m : ℝ) + 1)) * (m.factorial : ℝ) := by
      gcongr
      exact hsq.trans hm
    _ = x ^ m * ((m + 2).factorial : ℝ) := by rw [hf]; ring

private theorem angleSin_bounds (x : ℝ) (hx : 0 ≤ x) (hu : x ≤ 5 / 4) (k : ℕ) :
    (∑ i ∈ range (2 * k), (-1 : ℝ) ^ i * x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ))
      ≤ Real.sin x ∧ Real.sin x ≤
    ∑ i ∈ range (2 * k + 1), (-1 : ℝ) ^ i * x ^ (2 * i + 1) / ((2 * i + 1).factorial : ℝ) := by
  have ht := (Real.hasSum_sin x).tendsto_sum_nat
  have ha := angleTerms_antitone x hx hu 1
  simpa only [mul_div_assoc] using
    And.intro (ha.alternating_series_le_tendsto (by simpa only [mul_div_assoc] using ht) k)
      (ha.tendsto_le_alternating_series (by simpa only [mul_div_assoc] using ht) k)

private theorem angleCos_bounds (x : ℝ) (hx : 0 ≤ x) (hu : x ≤ 5 / 4) (k : ℕ) :
    (∑ i ∈ range (2 * k), (-1 : ℝ) ^ i * x ^ (2 * i) / ((2 * i).factorial : ℝ))
      ≤ Real.cos x ∧ Real.cos x ≤
    ∑ i ∈ range (2 * k + 1), (-1 : ℝ) ^ i * x ^ (2 * i) / ((2 * i).factorial : ℝ) := by
  have ht := (Real.hasSum_cos x).tendsto_sum_nat
  have ha := angleTerms_antitone x hx hu 0
  simpa only [Nat.add_zero, mul_div_assoc] using
    And.intro (ha.alternating_series_le_tendsto (by simpa only [mul_div_assoc] using! ht) k)
      (ha.tendsto_le_alternating_series (by simpa only [mul_div_assoc] using! ht) k)

private theorem angleEndpoint_lower :
    Real.sin ((233112 / 100000 : ℝ) / 2) -
      (233112 / 100000 : ℝ) * Real.cos ((233112 / 100000 : ℝ) / 2) < 0 := by
  have hs := angleSin_bounds ((233112 / 100000 : ℝ) / 2) (by norm_num) (by norm_num) 3
  have hc := angleCos_bounds ((233112 / 100000 : ℝ) / 2) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at hs hc
  linarith only [hs.2, hc.1]

private theorem angleEndpoint_upper :
    0 < Real.sin ((233113 / 100000 : ℝ) / 2) -
      (233113 / 100000 : ℝ) * Real.cos ((233113 / 100000 : ℝ) / 2) := by
  have hs := angleSin_bounds ((233113 / 100000 : ℝ) / 2) (by norm_num) (by norm_num) 3
  have hc := angleCos_bounds ((233113 / 100000 : ℝ) / 2) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at hs hc
  linarith only [hs.1, hc.2]

theorem section3OptimalAngleSubgoal : Section3OptimalAngleSubgoal := by
  let g : ℝ → ℝ := fun z => Real.sin (z / 2) - z * Real.cos (z / 2)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hcos (z : ℝ) (hz : z ∈ Set.Icc (233112 / 100000 : ℝ) (233113 / 100000)) :
      0 < Real.cos (z / 2) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_gt_d2, hz.1, hz.2]
  have hmono : StrictMonoOn g (Set.Icc (233112 / 100000 : ℝ) (233113 / 100000)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hg.continuousOn
    intro z hz
    have hzi : z ∈ Set.Icc (233112 / 100000 : ℝ) (233113 / 100000) :=
      interior_subset hz
    have hder : HasDerivAt g ((z * Real.sin (z / 2) - Real.cos (z / 2)) / 2) z := by
      convert! ((Real.hasDerivAt_sin (z / 2)).comp z ((hasDerivAt_id z).div_const 2)).sub
        ((hasDerivAt_id z).mul
          ((Real.hasDerivAt_cos (z / 2)).comp z ((hasDerivAt_id z).div_const 2))) using 1
      (try dsimp [g])
      ring
    rw [hder.deriv]
    have hs1 : (3 / 4 : ℝ) < Real.sin 1 := by
      have h := Real.sin_gt_sub_cube (by norm_num : (0 : ℝ) < 1)
      linarith
    have hsin : Real.sin 1 ≤ Real.sin (z / 2) := by
      apply Real.strictMonoOn_sin.monotoneOn
      · constructor <;> linarith [Real.pi_gt_d2]
      · constructor <;> linarith [Real.pi_gt_d2, hzi.1, hzi.2]
      · linarith [hzi.1]
    have hprod : 0 ≤ (z - 2) * (Real.sin (z / 2) - 3 / 4) :=
      mul_nonneg (by linarith [hzi.1]) (by linarith)
    nlinarith [Real.cos_le_one (z / 2), hzi.1]
  obtain ⟨z, hz, hgz⟩ := intermediate_value_Ioo
    (by norm_num : (233112 / 100000 : ℝ) ≤ 233113 / 100000)
    hg.continuousOn (show (0 : ℝ) ∈ Set.Ioo (g (233112 / 100000)) (g (233113 / 100000)) from
      ⟨angleEndpoint_lower, angleEndpoint_upper⟩)
  have hzi : z ∈ Set.Icc (233112 / 100000 : ℝ) (233113 / 100000) := ⟨hz.1.le, hz.2.le⟩
  have htan : Real.tan (z / 2) = z := by
    rw [Real.tan_eq_sin_div_cos, div_eq_iff (ne_of_gt (hcos z hzi))]
    dsimp [g] at hgz
    linarith
  refine ⟨z, ⟨htan, hz⟩, ?_⟩
  intro y hy
  have hyi : y ∈ Set.Icc (233112 / 100000 : ℝ) (233113 / 100000) :=
    ⟨hy.2.1.le, hy.2.2.le⟩
  have hgy : g y = 0 := by
    have h := (div_eq_iff (ne_of_gt (hcos y hyi))).mp
      (by simpa [Real.tan_eq_sin_div_cos] using hy.1)
    dsimp [g]
    linarith
  exact hmono.injOn hyi hzi (hgy.trans hgz.symm)

end Qatlib.Concepts.SearchStopping.RestartLaw
