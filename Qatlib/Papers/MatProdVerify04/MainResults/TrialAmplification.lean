/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Amplification by sixteen independent trials

`lemma2_amplification` proves the numerical estimate underlying amplification by sixteen trials.
Complement identities and the product formula for total failure yield
`lemma2_sixteen_trial_mass` for finite Boolean trial distributions. The paper context is
[BuhrmanSpalek2006].

## Main statements

* `probEvent_allFail`: product formula for all trials failing.
* `lemma2_sixteen_trial_mass`: lower bound on success in sixteen trials.

## References

* [Buhrman and Špalek, 2006][BuhrmanSpalek2006]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.MatProdVerify04.MainResults

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- For `1 / 8 ≤ p ≤ 1 / 2`, the amplified success expression `1 - (1 - p / 8) ^ 16` is at least
`p`. See [BuhrmanSpalek2006]. -/
theorem lemma2_amplification {p : ℝ} (hp8 : (1 : ℝ) / 8 ≤ p) (hp2 : p ≤ 1 / 2) :
    p ≤ 1 - (1 - p / 8) ^ 16 := by
  have hp0 : 0 ≤ p := by linarith
  have hbase : 0 ≤ 1 - p / 8 := by linarith
  have hexp1 : 1 - p / 8 ≤ Real.exp (-(p / 8)) := by
    have := Real.add_one_le_exp (-(p / 8))
    linarith
  have hpow : (1 - p / 8) ^ 16 ≤ Real.exp (-(2 * p)) := by
    have hstep : (1 - p / 8) ^ 16 ≤ (Real.exp (-(p / 8))) ^ 16 :=
      pow_le_pow_left₀ hbase hexp1 16
    have hmul : (Real.exp (-(p / 8))) ^ 16 = Real.exp (-(2 * p)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    exact hstep.trans hmul.le
  have hexp2 : Real.exp (-(2 * p)) ≤ (1 + 2 * p)⁻¹ := by
    have hden : 0 < 1 + 2 * p := by linarith
    have hle : 1 + 2 * p ≤ Real.exp (2 * p) := by
      have := Real.add_one_le_exp (2 * p)
      linarith
    have h1 : (Real.exp (2 * p))⁻¹ ≤ (1 + 2 * p)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hden hle
    have h2 : Real.exp (-(2 * p)) = (Real.exp (2 * p))⁻¹ := Real.exp_neg _
    rw [h2]
    exact h1
  have hfrac : p ≤ 1 - (1 + 2 * p)⁻¹ := by
    have hpos : 0 < 1 + 2 * p := by linarith
    have hgoal : 1 - (1 + 2 * p)⁻¹ = 2 * p / (1 + 2 * p) := by
      field_simp
      ring
    rw [hgoal]
    have hkey : p * (1 + 2 * p) ≤ 2 * p := by nlinarith
    calc p = p * (1 + 2 * p) / (1 + 2 * p) := by field_simp
      _ ≤ 2 * p / (1 + 2 * p) := div_le_div_of_nonneg_right hkey (le_of_lt hpos)
  linarith

/-- The probabilities of an event and its complement under independent Boolean trials sum to
one. -/
theorem probEvent_add_compl (trial : FinDist Bool) {L : ℕ}
    (E : (Fin L → Bool) → Prop) [DecidablePred E] :
    trial.probEvent (L := L) E + trial.probEvent (L := L) (fun ω => ¬ E ω) = 1 := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := E) (f := fun ω : Fin L → Bool => trial.probOf ω)
  have hone := FinDist.sum_probOf trial L
  unfold FinDist.probEvent
  exact hsplit.trans hone

/-- Pointwise equivalent events have equal probabilities under a finite product distribution. -/
theorem probEvent_congr {X : Type*} [Fintype X] {L : ℕ} (p : FinDist X)
    {E E' : (Fin L → X) → Prop} [DecidablePred E] [DecidablePred E']
    (h : ∀ ω, E ω ↔ E' ω) : p.probEvent E = p.probEvent E' := by
  classical
  unfold FinDist.probEvent
  rw [Finset.filter_congr (fun ω _ => h ω)]

/-- The probability that all `L` independent Boolean trials fail equals the single trial failure
probability raised to `L`. -/
theorem probEvent_allFail (trial : FinDist Bool) {L : ℕ} :
    trial.probEvent (L := L) (fun ω => ∀ i, ω i = false) = (trial.prob false) ^ L := by
  classical
  rw [FinDist.probEvent]
  have hfilter : Finset.univ.filter (fun ω : Fin L → Bool => ∀ i, ω i = false)
      = {fun _ => false} := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, funext_iff]
  rw [hfilter]
  simp [FinDist.probOf]

/-- If a Boolean trial succeeds with probability at least `p / 8`, where `1 / 8 ≤ p ≤ 1 / 2`,
then sixteen independent trials contain a success with probability at least `p`. See
[BuhrmanSpalek2006]. -/
theorem lemma2_sixteen_trial_mass (trial : FinDist Bool) {p : ℝ}
    (hp8 : (1 : ℝ) / 8 ≤ p) (hp2 : p ≤ 1 / 2) (hsucc : p / 8 ≤ trial.prob true) :
    p ≤ trial.probEvent (L := 16) (fun ω => ∃ i, ω i = true) := by
  classical
  have hfalse : trial.prob false = 1 - trial.prob true := by
    have hsum : trial.prob true + trial.prob false = 1 := by
      have := trial.sum_one
      rwa [Fintype.sum_bool] at this
    linarith
  have hfail : trial.probEvent (L := 16) (fun ω => ∀ i, ω i = false)
      = (trial.prob false) ^ 16 := probEvent_allFail trial
  have hcompl : trial.probEvent (L := 16) (fun ω => ∃ i, ω i = true)
      = 1 - trial.probEvent (L := 16) (fun ω => ∀ i, ω i = false) := by
    have h := probEvent_add_compl trial (fun ω : Fin 16 → Bool => ∃ i, ω i = true)
    have hcongr : trial.probEvent (L := 16) (fun ω => ¬ ∃ i, ω i = true)
        = trial.probEvent (L := 16) (fun ω => ∀ i, ω i = false) :=
      probEvent_congr trial (fun ω => by simp [not_exists])
    rw [hcongr] at h
    linarith
  have hbase : 0 ≤ trial.prob false := trial.nonneg false
  have hbase_le : trial.prob false ≤ 1 - p / 8 := by
    rw [hfalse]
    linarith
  have hpow : (trial.prob false) ^ 16 ≤ (1 - p / 8) ^ 16 :=
    pow_le_pow_left₀ hbase hbase_le 16
  have hnum := lemma2_amplification hp8 hp2
  rw [hcompl, hfail]
  linarith

end Qatlib.Papers.MatProdVerify04.MainResults
