/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MatProdVerify04.MainResults.TrialAmplification
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Geometric bounds for repeated hits

`escape_le_exp` bounds repeated failure by an exponential, and `geometric_hit_bound` gives a
linear lower bound on the complementary hit probability when the total trial mass is at most
one. `hit_mass_product` transports this estimate to independent Boolean trials. The paper
context is [BuhrmanSpalek2006].

## Main statements

* `escape_le_exp`: exponential upper bound on failure.
* `hit_mass_product`: lower bound on at least one successful trial.

## References

* [Buhrman and Špalek, 2006][BuhrmanSpalek2006]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MatProdVerify04.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- For `x ≤ 1`, bounds `(1 - x) ^ t` by `exp (-t * x)`. See [BuhrmanSpalek2006]. -/
theorem escape_le_exp {x : ℝ} (hx1 : x ≤ 1) (t : ℕ) :
    (1 - x) ^ t ≤ Real.exp (-((t : ℝ) * x)) := by
  have hbase : 0 ≤ 1 - x := by linarith
  have hexp : 1 - x ≤ Real.exp (-x) := by
    have := Real.add_one_le_exp (-x)
    linarith
  have hstep : (1 - x) ^ t ≤ (Real.exp (-x)) ^ t := pow_le_pow_left₀ hbase hexp t
  have hmul : (Real.exp (-x)) ^ t = Real.exp (-((t : ℝ) * x)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  exact hstep.trans hmul.le

/-- For `0 ≤ x ≤ 1` and `t * x ≤ 1`, the probability expression `1 - (1 - x) ^ t` is at least `t
* x / 2`. See [BuhrmanSpalek2006]. -/
theorem geometric_hit_bound {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (t : ℕ)
    (htx : (t : ℝ) * x ≤ 1) :
    (t : ℝ) * x / 2 ≤ 1 - (1 - x) ^ t := by
  have hu0 : 0 ≤ (t : ℝ) * x := mul_nonneg (Nat.cast_nonneg t) hx0
  have hesc := escape_le_exp hx1 t

  have hexp_le : Real.exp (-((t : ℝ) * x)) ≤ (1 + (t : ℝ) * x)⁻¹ := by
    have hden : 0 < 1 + (t : ℝ) * x := by linarith
    have hle : 1 + (t : ℝ) * x ≤ Real.exp ((t : ℝ) * x) := by
      have := Real.add_one_le_exp ((t : ℝ) * x)
      linarith
    have h1 : (Real.exp ((t : ℝ) * x))⁻¹ ≤ (1 + (t : ℝ) * x)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hden hle
    have h2 : Real.exp (-((t : ℝ) * x)) = (Real.exp ((t : ℝ) * x))⁻¹ := Real.exp_neg _
    rw [h2]
    exact h1

  have hfrac : (t : ℝ) * x / 2 ≤ 1 - (1 + (t : ℝ) * x)⁻¹ := by
    have hpos : 0 < 1 + (t : ℝ) * x := by linarith
    have hgoal : 1 - (1 + (t : ℝ) * x)⁻¹ = (t : ℝ) * x / (1 + (t : ℝ) * x) := by
      have hu : 1 + (t : ℝ) * x ≠ 0 := ne_of_gt hpos
      field_simp [hu]
      ring
    rw [hgoal]
    have hden2 : (t : ℝ) * x / 2 ≤ (t : ℝ) * x / (1 + (t : ℝ) * x) :=
      div_le_div_of_nonneg_left hu0 hpos (by linarith)
    linarith
  linarith

/-- If each Boolean trial succeeds with probability at least `x`, where `0 ≤ x ≤ 1` and `t * x ≤
1`, then `t` independent trials contain a success with probability at least `t * x / 2`. See
[BuhrmanSpalek2006]. -/
theorem hit_mass_product (trial : FinDist Bool) (t : ℕ) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (htx : (t : ℝ) * x ≤ 1) (hsucc : x ≤ trial.prob true) :
    (t : ℝ) * x / 2 ≤ trial.probEvent (L := t) (fun ω => ∃ i, ω i = true) := by
  classical
  have hfalse : trial.prob false = 1 - trial.prob true := by
    have hsum : trial.prob true + trial.prob false = 1 := by
      have := trial.sum_one
      rwa [Fintype.sum_bool] at this
    linarith
  have hfail : trial.probEvent (L := t) (fun ω => ∀ i, ω i = false)
      = (trial.prob false) ^ t := probEvent_allFail trial
  have hcompl : trial.probEvent (L := t) (fun ω => ∃ i, ω i = true)
      = 1 - trial.probEvent (L := t) (fun ω => ∀ i, ω i = false) := by
    have h := probEvent_add_compl trial (L := t) (fun ω : Fin t → Bool => ∃ i, ω i = true)
    have hcongr : trial.probEvent (L := t) (fun ω => ¬ ∃ i, ω i = true)
        = trial.probEvent (L := t) (fun ω => ∀ i, ω i = false) :=
      probEvent_congr trial (fun ω => by simp [not_exists])
    rw [hcongr] at h
    linarith
  have hbase : 0 ≤ trial.prob false := trial.nonneg false
  have hbase_le : trial.prob false ≤ 1 - x := by
    rw [hfalse]
    linarith
  have hpow : (trial.prob false) ^ t ≤ (1 - x) ^ t :=
    pow_le_pow_left₀ hbase hbase_le t
  have hgeo := geometric_hit_bound hx0 hx1 t htx
  rw [hcompl, hfail]
  linarith

end Qatlib.Papers.MatProdVerify04.MainResults
