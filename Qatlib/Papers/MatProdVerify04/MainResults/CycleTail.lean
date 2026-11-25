/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MatProdVerify04.MainResults.TrialAmplification
public import Qatlib.Papers.MatProdVerify04.MainResults.AlgorithmTime

@[expose] public section

/-!
# Failure and time estimates after the threshold in Product Verification

In Theorem 6 of [Buhrman and Špalek][BuhrmanSpalek2006], each cycle past the
threshold repeats Verify Once sixteen times. The single-cycle success bound
controls the conditional failure recurrence. Nine cycles suffice for the
stated error, and the growth factor `15/14` yields a convergent time tail.
-/

set_option autoImplicit false

open scoped BigOperators
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Papers.MatProdVerify04.MainResults

namespace Qatlib.Papers.MatProdVerify04.MainResults

/-- With Verify Once success mass at least `1/64`, a cycle of sixteen independent
trials fails with mass at most `7/8`. -/
theorem sixteen_trial_failure_le (trial : FinDist Bool) (htrial : (1 : ℝ) / 64 ≤ trial.prob true) :
    trial.probEvent (L := 16) (fun ω => ∀ i, ω i = false) ≤ 7 / 8 := by
  let E : (Fin 16 → Bool) → Prop := fun ω => ∃ i, ω i = true
  have hsuccess : (1 : ℝ) / 8 ≤ trial.probEvent E :=
    lemma2_sixteen_trial_mass trial (p := 1 / 8) le_rfl (by norm_num) (by
      norm_num at htrial ⊢
      exact htrial)
  have hsum := probEvent_add_compl trial E
  have hcompl : trial.probEvent (fun ω => ¬ E ω) =
      trial.probEvent (L := 16) (fun ω => ∀ i, ω i = false) :=
    probEvent_congr trial (fun ω => by simp [E])
  rw [hcompl] at hsum
  linarith

/-- Nine consecutive cycles with conditional failure ratio at most `γ ≤ 7/8`
leave less than one-third total failure mass after a cutoff. -/
theorem nine_cycles_failure_lt_third (failure : ℕ → ℝ) (cutoff : ℕ) {γ : ℝ}
    (hγ : 0 ≤ γ) (hγmax : γ ≤ 7 / 8) (hbase : failure cutoff ≤ 1)
    (hstep : ∀ j < 9, failure (cutoff + j + 1) ≤ γ * failure (cutoff + j)) :
    failure (cutoff + 9) < 1 / 3 := by
  have hpow (j : ℕ) (hj : j ≤ 9) : failure (cutoff + j) ≤ γ ^ j := by
    induction j with
    | zero => simpa using hbase
    | succ j ih =>
      have hj' : j < 9 := Nat.lt_of_succ_le hj
      calc
        _ ≤ γ * failure (cutoff + j) := hstep j hj'
        _ ≤ γ * γ ^ j := mul_le_mul_of_nonneg_left (ih hj'.le) hγ
        _ = _ := by rw [pow_succ, mul_comm]
  exact (hpow 9 le_rfl).trans_lt
    ((pow_le_pow_left₀ hγ hγmax 9).trans_lt (by norm_num))

/-- At growth factor `15/14`, the geometric contribution to the
expected-time tail is bounded by sixteen times its first coefficient. -/
theorem cycle_time_tail_le {a γ : ℝ} (ha : 0 ≤ a) (hγ : 0 ≤ γ)
    (hγmax : γ ≤ 7 / 8) (N : ℕ) :
    (∑ i ∈ Finset.range N, a * ((15 : ℝ) / 14 * γ) ^ i) ≤ 16 * a := by
  have hr0 : 0 ≤ (15 : ℝ) / 14 * γ := by positivity
  have hr : (15 : ℝ) / 14 * γ ≤ 15 / 16 := by linarith
  have hd : (1 : ℝ) / 16 ≤ 1 - (15 : ℝ) / 14 * γ := by linarith
  calc
    _ ≤ a / (1 - (15 : ℝ) / 14 * γ) :=
      geom_partial_sum_le ha hr0 (hr.trans_lt (by norm_num)) N
    _ ≤ a / (1 / 16 : ℝ) := div_le_div_of_nonneg_left ha (by norm_num) hd
    _ = _ := by ring

end Qatlib.Papers.MatProdVerify04.MainResults
