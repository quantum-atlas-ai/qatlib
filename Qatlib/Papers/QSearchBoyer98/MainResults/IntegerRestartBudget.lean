/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QSearchBoyer98.MainResults.RestartAsymptotics
public import Qatlib.Concepts.SearchStopping.PaidRestart.ActualRestartExpectedReceipt
public import Qatlib.Concepts.SearchStopping.PaidRestart.ActualRestartSearchWord
public import Mathlib.Tactic

@[expose] public section

/-!
# Integer restart budgets with a uniform paid-cost constant

Section 3 of [BoyerEtAl1998] optimizes the number of Grover iterations per restart.  The
continuous stationary profile is transported to finite angles in
`Qatlib.Papers.QSearchBoyer98.MainResults.exists_stationary_root_close`. Rounding the stationary
root divided by `4 θ` down to an integer gives a restart budget whose expected paid cost until
success is bounded by an absolute constant below `π / 4` times `1 / θ`, uniformly in the search
instance. This bound allows a supplied unitary preparation and does not prove global integer
optimality or a gate synthesis cost.

The first theorem is a statement about the actual Grover marked probability
`MeasureProb (GroverState A j) A`; the second instantiates the same budget in the paid restart
process of `Qatlib.Concepts.SearchStopping.PaidRestart`, where one verification query is added to
the `j` search queries.

## Main statements

* `integer_restart_paid_uniform`: There is a constant `C < π / 4` such that, on every nonempty
  finite search domain, every nonempty marked set and every sufficiently small angle `θ`, the
  integer restart budget `⌊ z / (4 θ) ⌋` taken from a stationary root `z` has marked success at
  strictly above `78 / 100` and expected paid query cost at most `C / θ`.
* `actual_integer_restart_receipt`: The same integer budget, implemented by the actual bit-oracle
  search word followed by one verification query, terminates almost surely and has expected paid
  time `(j + 1) / p`.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.SearchStopping.RestartLaw
open Qatlib.Concepts.SearchStopping.PaidRestart
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution
open Matrix
open scoped Classical BigOperators ENNReal

namespace Qatlib.Papers.QSearchBoyer98.MainResults

/-- The squared sine is globally `2`-Lipschitz. -/
private theorem abs_sin_sq_sub_le (x y : ℝ) :
    |Real.sin x ^ 2 - Real.sin y ^ 2| ≤ 2 * |x - y| := by
  have hfac : Real.sin x ^ 2 - Real.sin y ^ 2 =
      (Real.sin x - Real.sin y) * (Real.sin x + Real.sin y) := by ring
  rw [hfac, abs_mul]
  have h1 : |Real.sin x - Real.sin y| ≤ |x - y| := Real.abs_sin_sub_sin_le x y
  have h2 : |Real.sin x + Real.sin y| ≤ 2 := by
    calc
      |Real.sin x + Real.sin y| ≤ |Real.sin x| + |Real.sin y| := abs_add_le _ _
      _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one x) (Real.abs_sin_le_one y)
      _ = 2 := by norm_num
  calc
    |Real.sin x - Real.sin y| * |Real.sin x + Real.sin y| ≤ |x - y| * 2 := by
      gcongr
    _ = 2 * |x - y| := by ring

/-- The integer budget `⌊ z / (4 θ) ⌋` gives marked success above `78 / 100` on every
nonempty finite domain, provided `z` lies in the stationary-root window and `θ < 1 / 100`. -/
private theorem integer_restart_success_lower
    {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (A : Finset I) (θ z z₀ : ℝ) (j : ℕ)
    (hA : 0 < A.card)
    (hθ : Real.sin θ ^ 2 = (A.card : ℝ) / (Fintype.card I : ℝ))
    (hθpos : 0 < θ) (hθsmall : θ < 1 / 100)
    (hz₀ : Real.tan (z₀ / 2) = z₀)
    (hz₀lo : 233112 / 100000 < z₀) (hz₀hi : z₀ < 233113 / 100000)
    (hzlo : z₀ - 4 * θ < z) (hzhi : z < z₀)
    (hj : j = ⌊z / (4 * θ)⌋₊) :
    (78 / 100 : ℝ) < MeasureProb (GroverState A j) A := by
  have hN : 0 < Fintype.card I := Fintype.card_pos_iff.mpr inferInstance
  have hfrac : 0 < (A.card : ℝ) / (Fintype.card I : ℝ) := by
    exact div_pos (by exact_mod_cast hA) (by exact_mod_cast hN)
  have hsin_sq_pos : 0 < Real.sin θ ^ 2 := by rw [hθ]; exact hfrac
  have hs : Real.sin θ ≠ 0 := by
    intro h
    rw [h] at hsin_sq_pos
    norm_num at hsin_sq_pos
  have hc : Real.cos θ ≠ 0 := by
    have hpi : θ < Real.pi / 2 := by linarith [Real.pi_gt_d2]
    exact (Real.cos_pos_of_mem_Ioo ⟨by linarith, hpi⟩).ne'
  have hzpos : 0 < z := by linarith
  have hden : 0 < 4 * θ := by positivity
  have hjle : (j : ℝ) ≤ z / (4 * θ) := by
    rw [hj]
    exact Nat.floor_le (by positivity)
  have hjlt : z / (4 * θ) < (j : ℝ) + 1 := by
    rw [hj]
    exact Nat.lt_floor_add_one _
  have hjθle : (j : ℝ) * θ ≤ z / 4 := by
    have h4 : (4 * θ) * (j : ℝ) ≤ z := by
      have h := mul_le_mul_of_nonneg_left hjle (le_of_lt hden)
      have hc : (4 * θ) * (z / (4 * θ)) = z := by
        field_simp
      linarith
    nlinarith
  have hjθgt : z / 4 - θ < (j : ℝ) * θ := by
    have h4 : z < (4 * θ) * ((j : ℝ) + 1) := by
      have h := mul_lt_mul_of_pos_left hjlt hden
      have hc : (4 * θ) * (z / (4 * θ)) = z := by
        field_simp
      linarith
    nlinarith
  have ha_upper : (2 * (j : ℝ) + 1) * θ ≤ z / 2 + θ := by nlinarith
  have ha_lower : z / 2 - θ < (2 * (j : ℝ) + 1) * θ := by nlinarith
  have hab : |(2 * (j : ℝ) + 1) * θ - z / 2| ≤ θ := by
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hp_eq : MeasureProb (GroverState A j) A =
      Real.sin ((2 * (j : ℝ) + 1) * θ) ^ 2 := by
    have := measureProb_groverState hN A θ hθ hs hc j
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using this
  have hp_lip : |MeasureProb (GroverState A j) A -
      Real.sin (z / 2) ^ 2| ≤ 2 * θ := by
    rw [hp_eq]
    calc
      |Real.sin ((2 * (j : ℝ) + 1) * θ) ^ 2 - Real.sin (z / 2) ^ 2| ≤
          2 * |(2 * (j : ℝ) + 1) * θ - z / 2| := abs_sin_sq_sub_le _ _
      _ ≤ 2 * θ := by linarith
  have hconst := section3OptimalConstantsSubgoal z₀ hz₀ hz₀lo hz₀hi
  have hsin₀ : (8445 / 10000 : ℝ) < Real.sin (z₀ / 2) ^ 2 := hconst.1
  have hzclose : |z / 2 - z₀ / 2| < 2 * θ := by
    have hzz : |z - z₀| < 4 * θ := by
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    rw [show z / 2 - z₀ / 2 = (z - z₀) / 2 by ring, abs_div]
    norm_num
    linarith
  have hsinz_lip := abs_sin_sq_sub_le (z / 2) (z₀ / 2)
  have hsinz : (8445 / 10000 : ℝ) - 4 * θ < Real.sin (z / 2) ^ 2 := by
    have hlow : Real.sin (z₀ / 2) ^ 2 - Real.sin (z / 2) ^ 2 ≤ 4 * θ := by
      have h := (abs_le.mp hsinz_lip).1
      nlinarith [h, hzclose]
    linarith
  have hp_ge : Real.sin (z / 2) ^ 2 - 2 * θ ≤ MeasureProb (GroverState A j) A := by
    have := (abs_le.mp hp_lip).1
    linarith
  nlinarith

/-- There is an absolute constant `C < π / 4` such that, on every nonempty finite search
domain, every nonempty marked set and every sufficiently small angle `θ`, the integer restart
budget `⌊ z / (4 θ) ⌋` taken from a stationary root `z` has marked success above `78 / 100`
and expected paid query cost at most `C / θ`. -/
theorem integer_restart_paid_uniform :
    ∃ C : ℝ, 0 < C ∧ C < Real.pi / 4 ∧
      ∀ {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
        (A : Finset I) (θ z z₀ : ℝ) (j : ℕ),
        0 < A.card →
        (Real.sin θ ^ 2 = (A.card : ℝ) / (Fintype.card I : ℝ)) →
        0 < θ → θ < 1 / 100 →
        Real.tan (z₀ / 2) = z₀ →
        233112 / 100000 < z₀ → z₀ < 233113 / 100000 →
        z₀ - 4 * θ < z → z < z₀ →
        Real.tan (z / 2 + θ) = z →
        j = ⌊z / (4 * θ)⌋₊ →
        (78 / 100 : ℝ) < MeasureProb (GroverState A j) A ∧
          (j + 1 : ℝ) / MeasureProb (GroverState A j) A ≤ C / θ := by
  refine ⟨77 / 100, by norm_num, ?_, ?_⟩
  · nlinarith [Real.pi_gt_d2]
  · intro I _ _ _ A θ z z₀ j hA hθ hθpos hθsmall hz₀ hz₀lo hz₀hi hzlo hzhi _ hj
    have hlower := integer_restart_success_lower A θ z z₀ j hA hθ hθpos hθsmall
      hz₀ hz₀lo hz₀hi hzlo hzhi hj
    refine ⟨hlower, ?_⟩
    have hjle : (j : ℝ) ≤ z / (4 * θ) := by
      rw [hj]
      exact Nat.floor_le (div_nonneg (le_of_lt (by linarith : 0 < z)) (le_of_lt (by positivity : 0 < 4 * θ)))
    have hnum_nonneg : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
    have hp_nonneg : (0 : ℝ) ≤ MeasureProb (GroverState A j) A :=
      measureProb_nonneg _ _
    have hupper₁ : (j + 1 : ℝ) / MeasureProb (GroverState A j) A ≤
        ((j : ℝ) + 1) / (78 / 100) := by
      gcongr
    have hupper₂ : ((j : ℝ) + 1) / (78 / 100) ≤
        (z / (4 * θ) + 1) / (78 / 100) := by
      gcongr
    have hθne : θ ≠ 0 := ne_of_gt hθpos
    have halg : (z / (4 * θ) + 1) = (z / 4 + θ) / θ := by
      field_simp
    have hratio : (z / 4 + θ) / (78 / 100) ≤ 77 / 100 := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 78 / 100)]
      nlinarith
    have hfinal : ((z / 4 + θ) / (78 / 100)) / θ ≤ (77 / 100) / θ := by
      exact div_le_div_of_nonneg_right hratio (le_of_lt hθpos)
    calc
      (j + 1 : ℝ) / MeasureProb (GroverState A j) A ≤
          ((j : ℝ) + 1) / (78 / 100) := hupper₁
      _ ≤ (z / (4 * θ) + 1) / (78 / 100) := hupper₂
      _ = ((z / 4 + θ) / (78 / 100)) / θ := by rw [halg]; ring
      _ ≤ (77 / 100) / θ := hfinal

/-- The integer restart budget implemented by the actual bit-oracle search word followed by one
verification query terminates almost surely and has expected paid time `(j + 1) / p`, where `p`
is the actual marked success probability of the `j`-step Grover word. -/
theorem actual_integer_restart_receipt
    {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (A : Finset I) (θ z z₀ : ℝ) (j : ℕ)
    (hA : 0 < A.card)
    (hθ : Real.sin θ ^ 2 = (A.card : ℝ) / (Fintype.card I : ℝ))
    (hθpos : 0 < θ) (hθsmall : θ < 1 / 100)
    (hz₀ : Real.tan (z₀ / 2) = z₀)
    (hz₀lo : 233112 / 100000 < z₀) (hz₀hi : z₀ < 233113 / 100000)
    (hzlo : z₀ - 4 * θ < z) (hzhi : z < z₀)
    (hj : j = ⌊z / (4 * θ)⌋₊)
    (T' : Matrix I I ℂ) (v : QState I)
    (hT : T' ∈ Matrix.unitaryGroup I ℂ) (hv : Normalized v)
    (hprep : T' *ᵥ v = Uniform I)
    (hC : IsUnitaryCircuit (bbhtBitSearchCircuit T' v j)) :
    let p := MeasureProb (GroverState A j) A
    let next := bbhtActualRestartNextPrice T' v j A hC hv (j + 1)
    QueryCount (bbhtBitSearchCircuit T' v j) + 1 = j + 1 ∧
      0 < p ∧
      generalNeverMass (branchClockNext next) (branchClockEmbed (Sum.inr ())) = 0 ∧
      generalUnboundedTime (branchClockNext next) (branchClockEmbed (Sum.inr ())) =
        ENNReal.ofReal ((j + 1 : ℝ) / p) := by
  have hN : 0 < Fintype.card I := Fintype.card_pos_iff.mpr inferInstance
  have hlower := integer_restart_success_lower A θ z z₀ j hA hθ hθpos hθsmall
    hz₀ hz₀lo hz₀hi hzlo hzhi hj
  have hpos : 0 < MeasureProb (GroverState A j) A := by linarith
  have hword := actualRestartSearchWord I hN T' v hT hv hprep A j
  have hreceipt := actualRestartExpectedReceipt I hN T' v hT hv hprep A j hC (j + 1)
    (by norm_num)
  refine ⟨?_, hpos, ?_, ?_⟩
  · rw [hword.2.1]
  · exact hreceipt.2 hpos |>.1
  · simpa only [Nat.cast_add, Nat.cast_one] using (hreceipt.2 hpos).2.1

end Qatlib.Papers.QSearchBoyer98.MainResults
