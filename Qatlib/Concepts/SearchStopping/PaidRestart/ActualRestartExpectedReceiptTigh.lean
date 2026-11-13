/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.PaidRestart.ActualRestartExpectedReceiptStat
import Qatlib.Concepts.SearchStopping.PaidRestart.ActualRestartFirstSuccessTigh
import Qatlib.Concepts.SearchStopping.RestartLaw.Section3RestartExpectedSubgoalTigh

/-!
# Expected receipts for verified Grover restarts

Proves `actualRestartExpectedReceipt` using the first-success law and geometric-series
expectations. The supporting lemmas bound Grover success probabilities, sum the marked Born
masses, and evaluate a fixed-price retry expectation. For the quantum-search analysis, see
[BoyerEtAl1998].

## Main statements

* `bbhtGeometric_ennreal_expectation`: For `0 < p ≤ 1` and `0 ≤ c`, the extended nonnegative sum
  of `(r + 1) * c` weighted by the geometric first-success law is `ENNReal.ofReal (c / p)`.
* `actualRestartExpectedReceipt`: Establishes the nontermination dichotomy and expected
  paid-time and iteration formulas in `ActualRestartExpectedReceipt`.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution

set_option autoImplicit false
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Concepts.FairRandomBits.GeometricRetry
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.SearchStopping.RestartLaw

namespace Qatlib.Concepts.SearchStopping.PaidRestart
open Qatlib.Concepts.SearchStopping.KnownCount Matrix
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped Classical BigOperators ENNReal

/-- On a nonempty finite search space, the probability of measuring a marked address in a Grover
state lies between zero and one. -/
theorem bbhtGroverSuccess_bounds {I : Type} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (j : ℕ) :
    0 ≤ MeasureProb (GroverState A j) A ∧ MeasureProb (GroverState A j) A ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun i _ => bornProb_nonneg _ i), ?_⟩
  exact measureProb_le_one ((isUnitaryCircuit_groverCircuit hN j).normalized_run
    (setOracle_unitary A) (normalized_uniform hN)) A

/-- The sum of the extended nonnegative Born masses over marked addresses equals the extended
nonnegative marked-set measurement probability. -/
theorem bbhtMarkedBorn_mass_sum {I : Type} [Fintype I] [DecidableEq I]
    (A : Finset I) (j : ℕ) :
    (∑ i : I, if i ∈ A then ENNReal.ofReal (BornProb (GroverState A j) i) else 0) =
      ENNReal.ofReal (MeasureProb (GroverState A j) A) := by
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  exact (ENNReal.ofReal_sum_of_nonneg (fun i _ => bornProb_nonneg _ i)).symm

/-- For `0 < p ≤ 1` and `0 ≤ c`, the extended nonnegative sum of `(r + 1) * c` weighted by the
geometric first-success law is `ENNReal.ofReal (c / p)`. -/
theorem bbhtGeometric_ennreal_expectation (p c : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hc : 0 ≤ c) :
    (∑' r : ℕ, ENNReal.ofReal ((((r+1 : ℕ) : ℝ)*c*((1-p)^r*p)))) =
      ENNReal.ofReal (c/p) := by
  have hr : ‖1-p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hp1)]
    linarith
  have hh : HasSum (fun r : ℕ => ((r+1 : ℕ) : ℝ)*(1-p)^r) (1/p^2) := by
    simpa using hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hr
  have hs : Summable (fun r : ℕ => ((r+1 : ℕ) : ℝ)*c*((1-p)^r*p)) := by
    have he : (fun r : ℕ => ((r+1 : ℕ) : ℝ)*c*((1-p)^r*p)) =
        fun r : ℕ => (((r+1 : ℕ) : ℝ)*(1-p)^r)*(c*p) := by funext r; ring
    rw [he]
    exact (hh.mul_right (c*p)).summable
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun r => by positivity) hs]
  rw [geometric_restart_expectation p c hp hp1]

/-- For a Boolean distribution with positive success mass, the one-step price plus the
failure-to-success correction equals the price divided by the success mass. -/
theorem bbhtFixedPrice_expectation_formula (coin : PMF Bool) (price : ℕ)
    (hp : 0 < coin true) :
    (price : ℝ≥0∞)+(price : ℝ≥0∞)*coin false/coin true =
      (price : ℝ≥0∞)/coin true := by
  have hs : coin false+coin true = 1 := by simpa only [tsum_bool] using coin.tsum_coe
  have ht : coin true+coin false = 1 := (add_comm _ _).trans hs
  have hself : coin true/coin true = 1 := ENNReal.div_self hp.ne' (coin.apply_ne_top true)
  calc
    _ = (price : ℝ≥0∞)*(1+coin false/coin true) := by simp only [div_eq_mul_inv]; ring
    _ = (price : ℝ≥0∞)*((coin true+coin false)/coin true) := by rw [ENNReal.add_div,hself]
    _ = _ := by rw [ht,one_div]; rfl

/-- Establishes the nontermination dichotomy and expected paid-time and iteration formulas in
`ActualRestartExpectedReceipt`. See [BoyerEtAl1998]. -/
theorem actualRestartExpectedReceipt : ActualRestartExpectedReceipt := by
  intro I _ _ hN T' v hT hv hprep A j hC price hprice
  (try dsimp only)
  let p := MeasureProb (GroverState A j) A
  let next := bbhtActualRestartNextPrice T' v j A hC hv price
  let a := fun i : I => if i ∈ A then ENNReal.ofReal (BornProb (GroverState A j) i) else 0
  let q := ENNReal.ofReal (1-p)
  have hl := actualRestartAttemptLaw I hN T' v hT hv hprep A j hC price
  have hb := bbhtGroverSuccess_bounds hN A j
  change 0 ≤ p ∧ p ≤ 1 at hb
  have hsum : (∑ i : I, a i) = ENNReal.ofReal p := bbhtMarkedBorn_mass_sum A j
  have hpos := unitRestart_positive next price hl.2.2 hprice
  refine ⟨?_,?_⟩
  · intro hpzero
    change p = 0 at hpzero
    have hz (i : I) : a i = 0 := by
      have hle : a i ≤ ∑ x : I, a x := Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i)
      rw [hsum,hpzero,ENNReal.ofReal_zero] at hle
      exact le_antisymm hle zero_le
    have hj (i : I) (k : ℕ) : branchHaltJoint next (Sum.inr ()) i k = 0 :=
      unitRestart_zero_address next price a q hl.1 hl.2.1 hl.2.2 i (hz i) k k
    have hn := (branch_cost_output_pending_never_conservation Unit I next hpos (Sum.inr ())).1
    simp only [hj,tsum_zero,zero_add] at hn
    refine ⟨hn,?_⟩
    have he := (general_unbounded_actual_expected_time (BranchClock Unit I) I
      (branchClockNext next) (branchClockEmbed (Sum.inr ()))).1
    simp_rw [branchClock_bridge next hpos] at he
    simpa only [hj,mul_zero,tsum_zero,hn,mul_one,zero_add] using he
  · intro hp
    change 0 < p at hp
    let coin : PMF Bool := PMF.ofFintype
      (fun b => if b then ENNReal.ofReal p else q) (by
        simp only [Fintype.sum_bool,Bool.false_eq_true,if_false,if_true]
        dsimp [q]
        rw [← ENNReal.ofReal_add hb.1 (by linarith [hb.2])]
        convert ENNReal.ofReal_one using 1
        congr 1
        ring)
    have hc : coin true = ∑ i : I, a i := hsum.symm
    have hf : coin false = q := rfl
    have hrel := unitRestart_never_time_eq next price a q hl.1 hl.2.1 hl.2.2 coin hc hf hprice
    have hct : coin true = ENNReal.ofReal p := rfl
    have hcp : 0 < coin true := by rw [hct]; exact ENNReal.ofReal_pos.mpr hp
    have hpaid := branch_cost_geometric_retry_expected_paid_cost coin price price hprice hprice hcp
    have hcost : (price : ℝ≥0∞)+(price : ℝ≥0∞)*coin false/coin true =
        ENNReal.ofReal ((price : ℝ)/p) := by
      rw [bbhtFixedPrice_expectation_formula coin price hcp, hct,
        ENNReal.ofReal_div_of_pos hp, ENNReal.ofReal_natCast]
    refine ⟨hrel.1.trans hpaid.1, hrel.2.trans (hpaid.2.trans hcost), ?_⟩
    have hex := (actualRestartFirstSuccess I hN T' v hT hv hprep A j hC price hprice).1
    calc
      _ = ∑' r : ℕ, ENNReal.ofReal ((((r+1 : ℕ) : ℝ)*(j : ℝ)*((1-p)^r*p))) := by
        apply tsum_congr
        intro r
        simp only [hex,← Finset.mul_sum,bbhtMarkedBorn_mass_sum]
        change (((r+1)*j : ℕ) : ℝ≥0∞)*(ENNReal.ofReal (1-p)^r*ENNReal.ofReal p) = _
        have hq0 : 0 ≤ 1-p := by linarith [hb.2]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow hq0,
          ← ENNReal.ofReal_mul (pow_nonneg hq0 r),
          ← ENNReal.ofReal_mul (Nat.cast_nonneg ((r+1)*j))]
        congr 1
        push_cast
        ring
      _ = _ := bbhtGeometric_ennreal_expectation p (j : ℝ) hp hb.2 (by positivity)

end Qatlib.Concepts.SearchStopping.PaidRestart
