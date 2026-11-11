/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.GeometricRetry
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Qatlib.Papers.AdiabaticQLS23.MainResults.FilterCost
import Mathlib.Tactic

/-!
# Paid clocks for geometric QLS retries

Connects a Bernoulli failure model to the paid branch clock for repeated QLS attempts in
[CostaEtAl2025]. The theorem `actualPaidClock` proves zero nontermination mass, finite expected
paid time, and the exact expression `G + B * q / (1 - q)`.

The budget lemmas compare this clock with the exact filtering and adiabatic costs, then with
`paperTotalCost` under explicit bounds on branch costs and the failure probability.

## Main statements

* `actualPaidClock`: Evaluates the expected paid time and proves finiteness.
* `actualReceipt`: Gives the probability of success at paid time `n * B + G`.
* `paid_clock_le_paper_cost`: Bounds the paid clock by the paper cost under the domination
  condition.
* `paid_clock_le_corrected_cost`: Uses an upper bound `δ` on the failure probability as the cost
  parameter.

## References

* [Costa et al., 2025][CostaEtAl2025]
-/

set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Papers.AdiabaticQLS23.MainResults
noncomputable section
open scoped ENNReal
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.FairRandomBits.GeometricRetry

/-- The Bernoulli distribution with success outcome `true` of mass `1 - q` and failure outcome
`false` of mass `q`. -/
def failureCoin (q : ℝ) (h0 : 0 ≤ q) (_h1 : q < 1) : PMF Bool :=
  PMF.bernoulli ((1-q).toNNReal) (Real.toNNReal_le_one.mpr (by linarith))

/-- The success mass of `failureCoin q h0 h1` is `ENNReal.ofReal (1 - q)`. -/
@[simp] theorem failureCoin_true (q : ℝ) (h0 : 0 ≤ q) (h1 : q < 1) :
    failureCoin q h0 h1 true = ENNReal.ofReal (1-q) := by
  simp [failureCoin, PMF.bernoulli_apply, ENNReal.ofReal]

/-- The failure mass of `failureCoin q h0 h1` is `ENNReal.ofReal q`. -/
@[simp] theorem failureCoin_false (q : ℝ) (h0 : 0 ≤ q) (h1 : q < 1) :
    failureCoin q h0 h1 false = ENNReal.ofReal q := by
  simp only [failureCoin, PMF.bernoulli_apply, Bool.cond_false]
  change 1 - ENNReal.ofReal (1-q) = ENNReal.ofReal q
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by linarith : 0 ≤ 1-q)]
  congr 1
  ring

/-- For `0 ≤ q < 1` and positive branch costs `G` and `B`, the retry clock has zero
nontermination mass, finite expected paid time, and real expectation `G + B * q / (1 - q)`.
See [CostaEtAl2025]. -/
theorem actualPaidClock (q : ℝ) (h0 : 0 ≤ q) (h1 : q < 1)
    (G B : ℕ) (hG : 0 < G) (hB : 0 < B) :
    generalNeverMass (branchClockNext (branchRetryNext (failureCoin q h0 h1) G B))
      (branchClockEmbed (Sum.inr ())) = 0 ∧
    (generalUnboundedTime (branchClockNext (branchRetryNext (failureCoin q h0 h1) G B))
      (branchClockEmbed (Sum.inr ()))) ≠ ∞ ∧
    (generalUnboundedTime (branchClockNext (branchRetryNext (failureCoin q h0 h1) G B))
      (branchClockEmbed (Sum.inr ()))).toReal = (G:ℝ)+(B:ℝ)*q/(1-q) := by
  have hp : 0 < failureCoin q h0 h1 true := by
    rw [failureCoin_true]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  have h := branch_cost_geometric_retry_expected_paid_cost (failureCoin q h0 h1) G B hG hB hp
  have ht : (B:ℝ≥0∞)*failureCoin q h0 h1 false/failureCoin q h0 h1 true ≠ ∞ :=
    ENNReal.div_ne_top (ENNReal.mul_ne_top (by simp) ((failureCoin q h0 h1).apply_ne_top false)) hp.ne'
  refine ⟨h.1, ?_, ?_⟩
  · rw [h.2]
    exact ENNReal.add_ne_top.mpr ⟨by simp, ht⟩
  rw [h.2, ENNReal.toReal_add (by simp) ht]
  simp only [ENNReal.toReal_natCast, ENNReal.toReal_div, ENNReal.toReal_mul,
    failureCoin_false, failureCoin_true, ENNReal.toReal_ofReal h0,
    ENNReal.toReal_ofReal (by linarith : 0 ≤ 1-q)]

/-- For `0 ≤ q < 1` and positive branch costs, the joint mass of success at paid time `n * B +
G` has real value `q ^ n * (1 - q)`. See [CostaEtAl2025]. -/
theorem actualReceipt (q : ℝ) (h0 : 0 ≤ q) (h1 : q < 1)
    (G B : ℕ) (hG : 0 < G) (hB : 0 < B) (n : ℕ) :
    (branchHaltJoint (branchRetryNext (failureCoin q h0 h1) G B)
      (Sum.inr ()) true (n*B+G)).toReal = q^n*(1-q) := by
  rw [branch_cost_geometric_retry_exact_receipt (failureCoin q h0 h1) G B hG hB n]
  simp [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal, h0,
    show 0 ≤ 1-q by linarith]

/-- If `G ≤ A + F` and `B ≤ A + F / 2`, the expected paid time is bounded by `F + (F / 2) *
expectedFailures q + A * expectedAttempts q`. -/
theorem paid_cost_le_exact_budget (q : ℝ) (h0 : 0 ≤ q) (h1 : q < 1)
    (G B : ℕ) (hG : 0 < G) (hB : 0 < B) (A F : ℝ)
    (hg : (G:ℝ) ≤ A+F) (hb : (B:ℝ) ≤ A+F/2) :
    (generalUnboundedTime (branchClockNext (branchRetryNext (failureCoin q h0 h1) G B))
      (branchClockEmbed (Sum.inr ()))).toReal ≤
        F + (F/2)*expectedFailures q + A*expectedAttempts q := by
  rw [(actualPaidClock q h0 h1 G B hG hB).2.2,
    expectedFailures_eq h0 h1, expectedAttempts_eq h0 h1]
  have hratio : 0 ≤ q/(1-q) := div_nonneg h0 (by linarith)
  calc
    (G:ℝ)+(B:ℝ)*q/(1-q) = (G:ℝ)+(B:ℝ)*(q/(1-q)) := by ring
    _ ≤ (A+F)+(A+F/2)*(q/(1-q)) :=
      add_le_add hg (mul_le_mul_of_nonneg_right hb hratio)
    _ = F + (F/2)*(q/(1-q)) + A*(1/(1-q)) := by
      field_simp [ne_of_gt (show (0:ℝ) < 1-q by linarith)]
      ring

/-- Under the stated branch-cost and positivity bounds, `q ≤ δ < 1`, `r < 1`, and `δ ≤ 2 * r - r
^ 2`, the expected paid time is at most `paperTotalCost α κ Δ εf r`. See [CostaEtAl2025]. -/
theorem paid_clock_le_paper_cost (q : ℝ) (h0 : 0 ≤ q) (h1 : q < 1)
    (G B : ℕ) (hG : 0 < G) (hB : 0 < B)
    (α κ Δ εf δ r : ℝ) (hα : 0 ≤ α) (hκ : 0 ≤ κ) (hΔ : 0 < Δ)
    (hε0 : 0 < εf) (hε2 : εf ≤ 2) (hqd : q ≤ δ) (hδ : δ < 1)
    (hr : r < 1) (hdom : δ ≤ 2*r-r^2)
    (hg : (G:ℝ) ≤ α*κ/Δ + κ*Real.log (2/εf))
    (hb : (B:ℝ) ≤ α*κ/Δ + (κ*Real.log (2/εf))/2) :
    (generalUnboundedTime (branchClockNext (branchRetryNext (failureCoin q h0 h1) G B))
      (branchClockEmbed (Sum.inr ()))).toReal ≤ paperTotalCost α κ Δ εf r := by
  have hp := paid_cost_le_exact_budget q h0 h1 G B hG hB
    (α*κ/Δ) (κ*Real.log (2/εf)) hg hb
  have he : κ*Real.log (2/εf) + (κ*Real.log (2/εf)/2)*expectedFailures q
      + (α*κ/Δ)*expectedAttempts q = exactTotalCost α κ Δ εf q := by
    unfold exactTotalCost exactFilterCost exactAdiabaticRepeatCost
    ring
  rw [he] at hp
  exact hp.trans (actual_cost_le_paper_cost hα hκ hΔ hε0 hε2 h0 hqd hδ hr hdom)

/-- Under the stated branch-cost and positivity bounds and `q ≤ δ < 1`, the expected paid time
is at most `paperTotalCost α κ Δ εf δ`. See [CostaEtAl2025]. -/
theorem paid_clock_le_corrected_cost (q : ℝ) (h0 : 0 ≤ q) (h1 : q < 1)
    (G B : ℕ) (hG : 0 < G) (hB : 0 < B)
    (α κ Δ εf δ : ℝ) (hα : 0 ≤ α) (hκ : 0 ≤ κ) (hΔ : 0 < Δ)
    (hε0 : 0 < εf) (hε2 : εf ≤ 2) (hqd : q ≤ δ) (hδ : δ < 1)
    (hg : (G:ℝ) ≤ α*κ/Δ + κ*Real.log (2/εf))
    (hb : (B:ℝ) ≤ α*κ/Δ + (κ*Real.log (2/εf))/2) :
    (generalUnboundedTime (branchClockNext (branchRetryNext (failureCoin q h0 h1) G B))
      (branchClockEmbed (Sum.inr ()))).toReal ≤ paperTotalCost α κ Δ εf δ := by
  have hd0 : 0 ≤ δ := h0.trans hqd
  have hdom : δ ≤ 2*δ-δ^2 := by nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hδ.le)]
  exact paid_clock_le_paper_cost q h0 h1 G B hG hB α κ Δ εf δ δ
    hα hκ hΔ hε0 hε2 hqd hδ hδ hdom hg hb

end
end Qatlib.Papers.AdiabaticQLS23.MainResults
