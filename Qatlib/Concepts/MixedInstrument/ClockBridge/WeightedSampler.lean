/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.AdversaryBounds.AdvDuality.WeightedSamplerDefs

/-!
# Weighted sampling costs and truncation bounds

This module proves exact expected bit and step costs for a native two-weight sampler, together
with geometric pending tails, outcome partitions, and finite-fuel bias bounds. It accounts
explicitly for loading the encoded input and for approximation of real target probabilities by
natural weights.

For bucket trees and state-dependent weights, leaf masses are normalized weights and resource
costs have nodewise ledgers. Tree truncation budgets control pending probability, leaf bias, and
additional expected step cost. The broader computation framework is described in
[KitaevShenVyalyi2002].

## Main statements

* `expectedBits_eq`: identifies expected bit cost with the product of the weights.
* `expectedInputSteps_eq`: includes the loader in expected step accounting.
* `leafMass_eq`: identifies a leaf mass with its normalized weight.
* `treeTruncationBudget_bound`: bounds pending probability at the chosen tree budget.
* `clause23_complete`: collects cost and encoding laws.
* `clause24_complete`: collects pending-event and truncation laws.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AdversaryBounds.AdvDuality.FairFeedback
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridCounts
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridLeaf
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram.Path
open Qatlib.Concepts.AdversaryBounds.AdvDuality.NativeTape
open Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AdversaryBounds.AdvDuality

set_option autoImplicit false

namespace Qatlib.Concepts.MixedInstrument.ClockBridge

open scoped ENNReal

/-- Prepending a loaded configuration and a supplied bit to a native result leaves its pending
indicator unchanged. -/
theorem pendingIndicator_prepend (a b : ℕ) (bit : Bool)
    (r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control) :
    pendingIndicator (NativeTape.Result.prepend (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b, some bit) r) =
      pendingIndicator r := by
  simp [pendingIndicator, NativeTape.Result.prepend]

/-- Prepending a loaded configuration without a bit to a native result leaves its pending
indicator unchanged. -/
theorem pendingIndicator_prepend_none (a b : ℕ)
    (r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control) :
    pendingIndicator (NativeTape.Result.prepend (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b, none) r) =
      pendingIndicator r := by
  simp [pendingIndicator, NativeTape.Result.prepend]

/-- The finite-fuel pending mass of the two-weight sampler is at most one. -/
theorem pendingMass_le_one (n a b : ℕ) : pendingMass n a b ≤ 1 := by
  unfold pendingMass
  show ∑' r, (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) *
      pendingIndicator r ≤ 1
  calc ∑' r, (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) *
        pendingIndicator r
      ≤ ∑' r, (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) * 1 := by
        refine ENNReal.tsum_le_tsum (fun r => ?_)
        exact mul_le_mul_of_nonneg_left (by
          unfold pendingIndicator
          split <;> norm_num) (bot_le)
    _ = 1 := by
        rw [tsum_congr (fun r => by rw [mul_one])]
        exact (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)).tsum_coe

/-- The finite-fuel pending mass of the two-weight sampler is finite. -/
theorem pendingMass_ne_top (n a b : ℕ) : pendingMass n a b ≠ ∞ :=
  ne_of_lt (lt_of_le_of_lt (pendingMass_le_one n a b) ENNReal.one_lt_top)

/-- For positive weights, the next pending mass is the equally weighted sum of the pending
masses after the two possible unit transfers. -/
theorem pendingMass_succ (n a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    pendingMass (n+1) a b =
      (1/2 : ℝ≥0∞) * pendingMass n (a-1) (b+1) + (1/2 : ℝ≥0∞) * pendingMass n (a+1) (b-1) := by
  have hl := law_coin n a b ha hb
  have hinner : ∀ bit : Bool,
      CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n
          (NativeTape.advance (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)
            (.walk, .move (if bit then .right else .left))))
          (fun r => pendingIndicator (NativeTape.Result.prepend (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b, some bit) r)) =
        CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n
          (NativeTape.advance (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)
            (.walk, .move (if bit then .right else .left))))
          pendingIndicator := by
    intro bit
    apply congrArg (fun g : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control → ℝ≥0∞ =>
      CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n
        (NativeTape.advance (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) (.walk, .move (if bit then .right else .left)))) g)
    funext r
    exact pendingIndicator_prepend a b bit r
  unfold pendingMass
  rw [hl]
  rw [expectation_bind_map (PMF.uniformOfFintype' Bool)
    (fun bit => NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n
      (NativeTape.advance (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)
        (.walk, .move (if bit then .right else .left))))
    (fun bit r => NativeTape.Result.prepend (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b, some bit) r) pendingIndicator]
  rw [show (fun bit => CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n
        (NativeTape.advance (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) (.walk, .move (if bit then .right else .left))))
        (fun r => pendingIndicator (NativeTape.Result.prepend (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b, some bit) r))) =
      (fun bit => CostedLaw.expectation (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n
        (NativeTape.advance (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) (.walk, .move (if bit then .right else .left))))
        pendingIndicator) from funext hinner]
  simp only [CostedLaw.expectation]
  rw [tsum_fintype, Fintype.sum_bool]
  simp only [PMF.uniformOfFintype'_apply, Fintype.card_bool, Nat.cast_ofNat]
  rw [show (2 : ℝ≥0∞)⁻¹ = (1/2 : ℝ≥0∞) by norm_num]
  simp only [show (if True then Turing.Dir.right else Turing.Dir.left) = Turing.Dir.right from
      if_pos trivial,
    show (if true = true then Turing.Dir.right else Turing.Dir.left) = Turing.Dir.right from rfl,
    show (if false = true then Turing.Dir.right else Turing.Dir.left) = Turing.Dir.left from by simp,
    advance_right a b ha hb, advance_left a b ha hb]
  exact add_comm _ _

/-- At a zero left weight, the pending mass is zero for every positive fuel budget. -/
theorem pendingMass_left_endpoint (n b : ℕ) (hn : 0 < n) : pendingMass n 0 b = 0 := by
  unfold pendingMass
  cases b with
  | zero =>
      rw [law_degenerate n, CostedLaw.expectation_pure]
      simp [pendingIndicator, Qatlib.Concepts.AdversaryBounds.AdvDuality.degenerateResult]
  | succ b =>
      rw [law_left_endpoint n (b + 1) hn (by omega), CostedLaw.expectation_pure]
      simp [pendingIndicator, Qatlib.Concepts.AdversaryBounds.AdvDuality.leftEndpointResult]

/-- At a zero right weight and positive left weight, the pending mass is zero for every positive
fuel budget. -/
theorem pendingMass_right_endpoint (n a : ℕ) (hn : 0 < n) (ha : 0 < a) :
    pendingMass n a 0 = 0 := by
  unfold pendingMass
  rw [law_right_endpoint n a hn ha, CostedLaw.expectation_pure]
  simp [pendingIndicator, Qatlib.Concepts.AdversaryBounds.AdvDuality.rightEndpointResult]

/-- With both weights zero, the pending mass is zero at every fuel budget. -/
theorem pendingMass_degenerate (n : ℕ) : pendingMass n 0 0 = 0 := by
  unfold pendingMass
  rw [law_degenerate n, CostedLaw.expectation_pure]
  simp [pendingIndicator, Qatlib.Concepts.AdversaryBounds.AdvDuality.degenerateResult]

/-- With positive total weight and zero fuel, the pending mass is one. -/
theorem pendingMass_zero_budget (a b : ℕ) (h : 0 < a + b) : pendingMass 0 a b = 1 := by
  unfold pendingMass
  have hlaw : NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program 0 (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) =
      PMF.pure ⟨Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b, [], .fuel, []⟩ := by
    cases a with
    | zero =>
        cases b with
        | zero => omega
        | succ b =>
            have hh := head_left (b + 1) (by omega)
            simp [NativeTape.law,
                Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded, hh, Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program]
    | succ a =>
        cases b with
        | zero =>
            have hh := head_right (a + 1) (by omega)
            simp [NativeTape.law,
                Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded, hh, Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program]
        | succ b =>
            have hh := head_cell (a + 1) (b + 1) (by omega) (by omega)
            simp [NativeTape.law,
                Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded, hh, Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program]
  rw [hlaw, CostedLaw.expectation_pure]
  simp [pendingIndicator]

/-- With both weights positive, the pending mass after one unit of fuel is one. -/
theorem pendingMass_one (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : pendingMass 1 a b = 1 := by
  rw [pendingMass_succ 0 a b ha hb, pendingMass_zero_budget (a - 1) (b + 1) (by omega),
    pendingMass_zero_budget (a + 1) (b - 1) (by omega)]
  have hone : (1 / 2 : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ := by
    rw [div_eq_mul_inv, one_mul]
  simp only [hone, mul_one]
  exact ENNReal.inv_two_add_inv_two

/-- For positive weights, the next real pending probability is the average of the pending
probabilities after the two possible unit transfers. -/
theorem pendingProb_succ (n a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    pendingProb (n+1) a b =
      (1/2 : ℝ) * pendingProb n (a-1) (b+1) + (1/2 : ℝ) * pendingProb n (a+1) (b-1) := by
  simp only [pendingProb]
  rw [pendingMass_succ n a b ha hb]
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (by simp) (pendingMass_ne_top n (a-1) (b+1)))
      (ENNReal.mul_ne_top (by simp) (pendingMass_ne_top n (a+1) (b-1)))]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
  norm_num [ENNReal.toReal_inv]

/-- The decay factor is the same for two pairs of weights with equal total weight. -/
theorem decayReal_sum (a b c d : ℕ) (h : a + b = c + d) : decayReal a b = decayReal c d := by
  simp only [decayReal]
  rw [h]

/-- The decay factor is positive when the total weight is at least two. -/
theorem decayReal_pos (a b : ℕ) (hN : 2 ≤ a + b) : 0 < decayReal a b := by
  have hsq : (4 : ℝ) ≤ ((a + b : ℕ) : ℝ) ^ 2 := by
    have h2 : (2 : ℝ) ≤ (a + b : ℕ) := by exact_mod_cast hN
    nlinarith
  have hinv : (1 : ℝ) / ((a + b : ℕ) : ℝ) ^ 2 ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((a + b : ℕ) : ℝ) ^ 2)]
    linarith
  simp only [decayReal]
  linarith

/-- The decay factor is strictly smaller than one when the total weight is at least two. -/
theorem decayReal_lt_one (a b : ℕ) (hN : 2 ≤ a + b) : decayReal a b < 1 := by
  have hpos : (0 : ℝ) < 1 / ((a + b : ℕ) : ℝ) ^ 2 := by positivity
  simp only [decayReal]
  linarith

/-- The product of two natural weights, viewed in ℝ, is at most the square of their sum. -/
theorem ab_le_sq (a b : ℕ) : ((a : ℝ) * (b : ℝ)) ≤ ((a + b : ℕ) : ℝ) ^ 2 := by
  have h1 : (a : ℝ) ≤ (a + b : ℕ) := by
    exact_mod_cast (show a ≤ a + b by omega)
  have h2 : (b : ℝ) ≤ (a + b : ℕ) := by
    exact_mod_cast (show b ≤ a + b by omega)
  nlinarith

/-- For total weight at least two, the pending probability after `n + 1` units of fuel is at
most `a * b * decayReal a b ^ n`. -/
private theorem tail_bound_aux : ∀ (n a b : ℕ), 2 ≤ a + b →
    pendingProb (n+1) a b ≤ ((a : ℝ) * (b : ℝ)) * decayReal a b ^ n := by
  intro n
  induction n with
  | zero =>
      intro a b hN
      by_cases ha : a = 0
      · subst ha
        have h := pendingMass_left_endpoint 1 b (by omega)
        simp only [pendingProb]
        rw [h]
        simp
      · by_cases hb : b = 0
        · subst hb
          have h := pendingMass_right_endpoint 1 a (by omega) (by omega)
          simp only [pendingProb]
          rw [h]
          simp
        · have h := pendingMass_one a b (by omega) (by omega)
          simp only [pendingProb]
          rw [h]
          simp only [ENNReal.toReal_one, pow_zero, mul_one]
          have h1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero ha)
          have h2 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hb)
          nlinarith
  | succ n ih =>
      intro a b hN
      by_cases ha : a = 0
      · subst ha
        have h := pendingMass_left_endpoint (n + 2) b (by omega)
        simp only [pendingProb]
        rw [h]
        simp
      · by_cases hb : b = 0
        · subst hb
          have h := pendingMass_right_endpoint (n + 2) a (by omega) (by omega)
          simp only [pendingProb]
          rw [h]
          simp
        · have hrec := pendingProb_succ (n + 1) a b (by omega) (by omega)
          have h1 := ih (a - 1) (b + 1) (by omega)
          have h2 := ih (a + 1) (b - 1) (by omega)
          have hd1 : decayReal (a - 1) (b + 1) = decayReal a b :=
            decayReal_sum _ _ _ _ (by omega)
          have hd2 : decayReal (a + 1) (b - 1) = decayReal a b :=
            decayReal_sum _ _ _ _ (by omega)
          rw [hd1] at h1
          rw [hd2] at h2
          have hkey : ((a : ℝ) * (b : ℝ)) * decayReal a b ≥ ((a : ℝ) * (b : ℝ)) - 1 := by
            have hsq := ab_le_sq a b
            have hNpos : (0 : ℝ) < ((a + b : ℕ) : ℝ) ^ 2 := by positivity
            have hdiv : ((a : ℝ) * (b : ℝ)) / ((a + b : ℕ) : ℝ) ^ 2 ≤ 1 := by
              rw [div_le_iff₀ hNpos]
              nlinarith [hsq]
            have hsplit : ((a : ℝ) * (b : ℝ)) * decayReal a b =
                ((a : ℝ) * (b : ℝ)) - ((a : ℝ) * (b : ℝ)) / ((a + b : ℕ) : ℝ) ^ 2 := by
              simp only [decayReal]
              ring
            rw [hsplit]
            linarith
          have hq : (((a - 1 : ℕ) : ℝ) * ((b + 1 : ℕ) : ℝ)) +
              (((a + 1 : ℕ) : ℝ) * ((b - 1 : ℕ) : ℝ)) =
              2 * ((a : ℝ) * (b : ℝ)) - 2 := by
            have ha1 : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
              rw [Nat.cast_sub (by omega : 1 ≤ a)]
              norm_num
            have hb1 : ((b - 1 : ℕ) : ℝ) = (b : ℝ) - 1 := by
              rw [Nat.cast_sub (by omega : 1 ≤ b)]
              norm_num
            rw [ha1, hb1]
            push_cast
            ring
          have hρpos : 0 < decayReal a b := decayReal_pos a b hN
          calc pendingProb (n + 1 + 1) a b
              = (1 / 2 : ℝ) * pendingProb (n + 1) (a - 1) (b + 1) +
                  (1 / 2 : ℝ) * pendingProb (n + 1) (a + 1) (b - 1) := hrec
            _ ≤ (1 / 2 : ℝ) * ((((a - 1 : ℕ) : ℝ) * ((b + 1 : ℕ) : ℝ)) * decayReal a b ^ n +
                  (((a + 1 : ℕ) : ℝ) * ((b - 1 : ℕ) : ℝ)) * decayReal a b ^ n) := by
                have e1 : (1 / 2 : ℝ) * pendingProb (n + 1) (a - 1) (b + 1) ≤
                    (1 / 2 : ℝ) * ((((a - 1 : ℕ) : ℝ) * ((b + 1 : ℕ) : ℝ)) * decayReal a b ^ n) :=
                  mul_le_mul_of_nonneg_left h1 (by norm_num)
                have e2 : (1 / 2 : ℝ) * pendingProb (n + 1) (a + 1) (b - 1) ≤
                    (1 / 2 : ℝ) * ((((a + 1 : ℕ) : ℝ) * ((b - 1 : ℕ) : ℝ)) * decayReal a b ^ n) :=
                  mul_le_mul_of_nonneg_left h2 (by norm_num)
                linarith
            _ = ((((a - 1 : ℕ) : ℝ) * ((b + 1 : ℕ) : ℝ)) +
                  (((a + 1 : ℕ) : ℝ) * ((b - 1 : ℕ) : ℝ))) / 2 * decayReal a b ^ n := by ring
            _ = (((a : ℝ) * (b : ℝ)) - 1) * decayReal a b ^ n := by
                rw [hq]
                ring
            _ ≤ ((a : ℝ) * (b : ℝ)) * decayReal a b ^ (n + 1) := by
                have hn : 0 ≤ decayReal a b ^ n := pow_nonneg hρpos.le _
                rw [pow_succ]
                nlinarith

/-- For total weight at least two, the pending probability is bounded by the geometric tail `a *
b * decayReal a b ^ n` at fuel `n + 1`. -/
theorem tail_bound (n a b : ℕ) (hN : 2 ≤ a + b) :
    pendingProb (n+1) a b ≤ ((a : ℝ) * (b : ℝ)) * decayReal a b ^ n :=
  tail_bound_aux n a b hN

/-- In ℝ≥0∞, averaging `1 + x` and `1 + y` gives one plus the average of `x` and `y`. -/
theorem ennreal_half_two (x y : ℝ≥0∞) :
    (1 / 2 : ℝ≥0∞) * ((1 + x) + (1 + y)) = 1 + (1 / 2 : ℝ≥0∞) * (x + y) := by
  have hone : (1 / 2 : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹ := by
    rw [div_eq_mul_inv, one_mul]
  calc (1 / 2 : ℝ≥0∞) * ((1 + x) + (1 + y))
      = (1 / 2 : ℝ≥0∞) * (1 + x) + (1 / 2 : ℝ≥0∞) * (1 + y) := mul_add _ _ _
    _ = ((1 / 2 : ℝ≥0∞) + (1 / 2 : ℝ≥0∞) * x) +
        ((1 / 2 : ℝ≥0∞) + (1 / 2 : ℝ≥0∞) * y) := by
      rw [mul_add, mul_add, mul_one]
    _ = ((1 / 2 : ℝ≥0∞) + (1 / 2 : ℝ≥0∞)) +
        ((1 / 2 : ℝ≥0∞) * x + (1 / 2 : ℝ≥0∞) * y) := by ac_rfl
    _ = 1 + ((1 / 2 : ℝ≥0∞) * x + (1 / 2 : ℝ≥0∞) * y) := by
      rw [hone, ENNReal.inv_two_add_inv_two]
    _ = 1 + (1 / 2 : ℝ≥0∞) * (x + y) := by
      congr 1
      exact (mul_add (1 / 2 : ℝ≥0∞) x y).symm

/-- For positive weights, expected bit cost is one plus the average expected bit cost after
either unit transfer. -/
theorem expectedBits_succ (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    expectedBits a b =
      1 + (1 / 2 : ℝ≥0∞) * (expectedBits (a - 1) (b + 1) + expectedBits (a + 1) (b - 1)) := by
  unfold expectedBits tailMass
  have hrec : ∀ n : ℕ, pendingMass (n + 1) a b =
      (1 / 2 : ℝ≥0∞) * pendingMass n (a - 1) (b + 1) +
        (1 / 2 : ℝ≥0∞) * pendingMass n (a + 1) (b - 1) :=
    fun n => pendingMass_succ n a b ha hb
  have hsplit : (∑' n, pendingMass (n + 1) a b) =
      (1 / 2 : ℝ≥0∞) * (∑' n, pendingMass n (a - 1) (b + 1) +
        ∑' n, pendingMass n (a + 1) (b - 1)) := by
    calc (∑' n, pendingMass (n + 1) a b)
        = ∑' n, ((1 / 2 : ℝ≥0∞) * (pendingMass n (a - 1) (b + 1) +
            pendingMass n (a + 1) (b - 1))) := by
          apply tsum_congr
          intro n
          rw [hrec n, mul_add]
      _ = (1 / 2 : ℝ≥0∞) * (∑' n, pendingMass n (a - 1) (b + 1) +
            ∑' n, pendingMass n (a + 1) (b - 1)) := by
          rw [← ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
  have hshift : (∑' n, pendingMass n (a - 1) (b + 1)) =
      1 + ∑' n, pendingMass (n + 1) (a - 1) (b + 1) := by
    rw [tsum_eq_zero_add' ENNReal.summable, pendingMass_zero_budget (a - 1) (b + 1) (by omega)]
  have hshift2 : (∑' n, pendingMass n (a + 1) (b - 1)) =
      1 + ∑' n, pendingMass (n + 1) (a + 1) (b - 1) := by
    rw [tsum_eq_zero_add' ENNReal.summable, pendingMass_zero_budget (a + 1) (b - 1) (by omega)]
  rw [hsplit, hshift, hshift2]
  exact ennreal_half_two _ _

/-- The extended-real pending mass at fuel `n + 1` is bounded by the embedded geometric tail
with prefactor `a * b`. -/
theorem tail_bound_ennreal (n a b : ℕ) (hN : 2 ≤ a + b) :
    pendingMass (n + 1) a b ≤
      ENNReal.ofReal ((a : ℝ) * (b : ℝ)) * (ENNReal.ofReal (decayReal a b)) ^ n := by
  have hle : pendingProb (n + 1) a b ≤ ((a : ℝ) * (b : ℝ)) * decayReal a b ^ n :=
    tail_bound n a b hN
  have hmass : pendingMass (n + 1) a b = ENNReal.ofReal (pendingProb (n + 1) a b) := by
    rw [pendingProb, ENNReal.ofReal_toReal (pendingMass_ne_top (n + 1) a b)]
  rw [hmass]
  have hmono : ENNReal.ofReal (pendingProb (n + 1) a b) ≤
      ENNReal.ofReal (((a : ℝ) * (b : ℝ)) * decayReal a b ^ n) :=
    ENNReal.ofReal_le_ofReal hle
  have heq : ENNReal.ofReal (((a : ℝ) * (b : ℝ)) * decayReal a b ^ n) =
      ENNReal.ofReal ((a : ℝ) * (b : ℝ)) * (ENNReal.ofReal (decayReal a b)) ^ n := by
    rw [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg b)),
      ENNReal.ofReal_pow (le_of_lt (decayReal_pos a b hN)) n]
  exact hmono.trans_eq heq

/-- The expected bit cost is finite when the total weight is at least two. -/
theorem expectedBits_ne_top (a b : ℕ) (hN : 2 ≤ a + b) : expectedBits a b ≠ ∞ := by
  have hsum : (∑' n, pendingMass (n + 1) a b) ≤
      ENNReal.ofReal ((a : ℝ) * (b : ℝ)) * (1 - ENNReal.ofReal (decayReal a b))⁻¹ := by
    calc (∑' n, pendingMass (n + 1) a b)
        ≤ ∑' n, (ENNReal.ofReal ((a : ℝ) * (b : ℝ)) * (ENNReal.ofReal (decayReal a b)) ^ n) :=
          ENNReal.tsum_le_tsum fun n => tail_bound_ennreal n a b hN
      _ = ENNReal.ofReal ((a : ℝ) * (b : ℝ)) *
            ∑' n, (ENNReal.ofReal (decayReal a b)) ^ n := by
          rw [ENNReal.tsum_mul_left]
      _ = ENNReal.ofReal ((a : ℝ) * (b : ℝ)) *
            (1 - ENNReal.ofReal (decayReal a b))⁻¹ := by
          rw [ENNReal.tsum_geometric]
  have hρlt : ENNReal.ofReal (decayReal a b) < 1 := by
    have h := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mpr
      (decayReal_lt_one a b hN)
    simpa using! h
  have hρne : ENNReal.ofReal (decayReal a b) ≠ ∞ := by
    exact ENNReal.ofReal_ne_top
  have hρle : ENNReal.ofReal (decayReal a b) ≤ 1 := le_of_lt hρlt
  have hdiff : (1 - ENNReal.ofReal (decayReal a b)) ≠ 0 := by
    have hsub : 1 - ENNReal.ofReal (decayReal a b) = ENNReal.ofReal (1 - decayReal a b) := by
      simpa using! (ENNReal.ofReal_sub 1 (le_of_lt (decayReal_pos a b hN))).symm
    rw [hsub]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith [decayReal_lt_one a b hN])
  have hinv : (1 - ENNReal.ofReal (decayReal a b))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr hdiff
  have hfinite : ENNReal.ofReal ((a : ℝ) * (b : ℝ)) *
      (1 - ENNReal.ofReal (decayReal a b))⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hinv
  have hlt : ENNReal.ofReal ((a : ℝ) * (b : ℝ)) *
      (1 - ENNReal.ofReal (decayReal a b))⁻¹ < ∞ := by
    rw [lt_top_iff_ne_top]
    exact hfinite
  have hmain : expectedBits a b = ∑' n, pendingMass (n + 1) a b := rfl
  rw [hmain]
  exact ne_of_lt (lt_of_le_of_lt hsum hlt)

/-- The expected bit cost is zero when the left weight is zero. -/
theorem expectedBits_zero_left (m : ℕ) : expectedBits 0 m = 0 := by
  unfold expectedBits
  apply ENNReal.tsum_eq_zero.mpr
  intro n
  exact pendingMass_left_endpoint (n + 1) m (by omega)

/-- The expected bit cost is zero when the right weight is zero. -/
theorem expectedBits_zero_right (m : ℕ) : expectedBits m 0 = 0 := by
  unfold expectedBits
  apply ENNReal.tsum_eq_zero.mpr
  intro n
  cases m with
  | zero => exact pendingMass_degenerate (n + 1)
  | succ m => exact pendingMass_right_endpoint (n + 1) (m + 1) (by omega) (by omega)

/-- For `i ≤ N` and `N ≥ 2`, the expected bit cost at weights `i` and `N - i` is their product
in ℝ≥0∞. -/
private theorem expectedBits_eq_aux (N : ℕ) (hN : 2 ≤ N) (i : ℕ) (hi : i ≤ N) :
    expectedBits i (N - i) = ((i : ℝ≥0∞) * ((N - i : ℕ) : ℝ≥0∞)) := by
  set e : ℕ → ℝ := fun j => (expectedBits j (N - j)).toReal with he
  have he0 : e 0 = 0 := by
    have hE0 : expectedBits 0 (N - 0) = 0 := by
      rw [show (N - 0) = N by omega]
      exact expectedBits_zero_left N
    show (expectedBits 0 (N - 0)).toReal = 0
    rw [hE0]
    simp
  have heN : e N = 0 := by
    have hEN : expectedBits N (N - N) = 0 := by
      rw [Nat.sub_self]
      exact expectedBits_zero_right N
    show (expectedBits N (N - N)).toReal = 0
    rw [hEN]
    simp
  have he0' : (expectedBits 0 (N - 0)).toReal = 0 := by
    have h := he0
    simp only [he] at h
    exact h
  have heN' : (expectedBits N (N - N)).toReal = 0 := by
    have h := heN
    simp only [he] at h
    exact h
  have herec : ∀ j, 1 ≤ j → j < N → e (j - 1) + e (j + 1) = 2 * e j - 2 := by
    intro j hj1 hjN
    have hjpos : 0 < j := by omega
    have hbpos : 0 < N - j := by omega
    have hsub1 : N - (j - 1) = (N - j) + 1 := by omega
    have hsub2 : N - (j + 1) = (N - j) - 1 := by omega
    have hrec := expectedBits_succ j (N - j) hjpos hbpos
    have hfin1 : expectedBits (j - 1) ((N - j) + 1) ≠ ∞ := expectedBits_ne_top _ _ (by omega)
    have hfin2 : expectedBits (j + 1) ((N - j) - 1) ≠ ∞ := expectedBits_ne_top _ _ (by omega)
    have hZ : (1 / 2 : ℝ≥0∞) *
        (expectedBits (j - 1) ((N - j) + 1) + expectedBits (j + 1) ((N - j) - 1)) ≠ ∞ := by
      exact ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.mpr ⟨hfin1, hfin2⟩)
    have htoReal : (expectedBits j (N - j)).toReal =
        1 + (1 / 2 : ℝ) *
          ((expectedBits (j - 1) ((N - j) + 1)).toReal +
            (expectedBits (j + 1) ((N - j) - 1)).toReal) := by
      rw [hrec, ENNReal.toReal_add ENNReal.one_ne_top hZ, ENNReal.toReal_mul,
        ENNReal.toReal_add hfin1 hfin2]
      simp
    have hgoal : e (j - 1) + e (j + 1) = 2 * e j - 2 := by
      simp only [he]
      rw [hsub1, hsub2]
      linarith
    exact hgoal
  set D : ℕ → ℝ := fun j => e j - (j : ℝ) * ((N - j : ℕ) : ℝ) with hD
  have hD0 : D 0 = 0 := by
    simp only [hD, he]
    rw [he0']
    simp
  have hDN : D N = 0 := by
    simp only [hD, he]
    rw [heN']
    simp
  have hG : ∀ j, 1 ≤ j → j < N →
      ((j - 1 : ℕ) : ℝ) * (((N - (j - 1 : ℕ) : ℕ)) : ℝ) +
        ((j + 1 : ℕ) : ℝ) * (((N - (j + 1 : ℕ) : ℕ)) : ℝ) =
      2 * ((j : ℝ) * ((N - j : ℕ) : ℝ)) - 2 := by
    intro j hj1 hjN
    have h1 : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ j)]
      norm_num
    have h2 : (((N - (j - 1 : ℕ) : ℕ)) : ℝ) = ((N - j : ℕ) : ℝ) + 1 := by
      have hN1 : (N - (j - 1 : ℕ) : ℕ) = (N - j : ℕ) + 1 := by omega
      rw [hN1, Nat.cast_add, Nat.cast_one]
    have h3 : (((N - (j + 1 : ℕ) : ℕ)) : ℝ) = ((N - j : ℕ) : ℝ) - 1 := by
      have hN2 : (N - (j + 1 : ℕ) : ℕ) = (N - j : ℕ) - 1 := by omega
      have hle : 1 ≤ N - j := by omega
      rw [hN2, Nat.cast_sub hle]
      norm_num
    have h4 : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [h1, h2, h3, h4]
    ring
  have hDrec : ∀ j, 1 ≤ j → j < N → D (j - 1) + D (j + 1) = 2 * D j := by
    intro j hj1 hjN
    have h := herec j hj1 hjN
    have hq := hG j hj1 hjN
    simp only [hD, he]
    linarith
  have hharm := harmonic_affine (N := N) (by omega) D 0 0 hD0 hDN hDrec
  have hval := hharm i hi
  have hEi : e i = (i : ℝ) * ((N - i : ℕ) : ℝ) := by
    have hDi : D i = 0 := by simpa using! hval
    have hDi' : D i = e i - (i : ℝ) * ((N - i : ℕ) : ℝ) := by rw [hD]
    linarith
  have htoReal : (expectedBits i (N - i)).toReal = (i : ℝ) * ((N - i : ℕ) : ℝ) := by
    have hEi' : e i = (expectedBits i (N - i)).toReal := by
      simp only [he]
    rw [← hEi']
    exact hEi
  have hne : expectedBits i (N - i) ≠ ∞ := expectedBits_ne_top i (N - i) (by omega)
  rw [← ENNReal.ofReal_toReal hne, htoReal]
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg i)]
  simp

/-- The expected bit cost of the two-weight sampler is exactly the product of its weights in
ℝ≥0∞. -/
theorem expectedBits_eq (a b : ℕ) : expectedBits a b = ((a : ℝ≥0∞) * b) := by
  by_cases ha : a = 0
  · subst ha
    rw [expectedBits_zero_left b]
    simp
  by_cases hb : b = 0
  · subst hb
    rw [expectedBits_zero_right a]
    simp
  have h := expectedBits_eq_aux (a + b) (by omega) a (by omega)
  rw [show (a + b) - a = b by omega] at h
  exact h

/-- For positive total weight, the expected step count is the product of the weights plus one. -/
theorem expectedSteps_eq (a b : ℕ) (h : 0 < a + b) :
    expectedSteps a b = ((a : ℝ≥0∞) * b) + 1 := by
  unfold expectedSteps
  have hshift : (∑' n, pendingMass n a b) =
      pendingMass 0 a b + ∑' n, pendingMass (n + 1) a b := by
    rw [tsum_eq_zero_add' ENNReal.summable]
  rw [hshift, pendingMass_zero_budget a b h]
  have hE : (∑' n, pendingMass (n + 1) a b) = expectedBits a b := rfl
  rw [hE, expectedBits_eq a b]
  ac_rfl

/-- For positive input weights, running the loader for `A + 1` steps with no supplied bits
reaches the loaded configuration, consumes no bits, and records exactly `A + 1` steps. -/
theorem loader_run (A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A + 1) [] (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)).cfg =
        Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded A B ∧
      (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A + 1) [] (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)).bits = [] ∧
      (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A + 1) [] (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)).steps = A + 1 := by
  have h := load_positive (A - 1) (B - 1) []
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [show A - 1 + 2 = A + 1 by omega, show A - 1 + 1 = A by omega,
    show B - 1 + 1 = B by omega] at h1 h2 h3 h4
  exact ⟨h1, h3, h4⟩

/-- For positive input weights, the loader run with budget `A + 1` stops because its fuel is
exhausted. -/
theorem loader_run_fuel (A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A + 1) [] (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)).stop = .fuel := by
  have h := load_positive_fuel (A - 1) (B - 1) []
  rw [show A - 1 + 2 = A + 1 by omega, show A - 1 + 1 = A by omega,
    show B - 1 + 1 = B by omega] at h
  exact h

/-- For positive input weights, removing the loader's `A + 1` steps identifies input pending
mass with loaded-state pending mass. -/
theorem pendingInputMass_eq (n A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    pendingInputMass (A + 1 + n) A B = pendingMass n A B := by
  obtain ⟨hc, hb, hs⟩ := loader_run A B hA hB
  have hstop := loader_run_fuel A B hA hB
  unfold pendingInputMass pendingMass
  rw [show A + 1 + n = (A + 1) + n by omega, NativeTape.law_add]
  rw [NativeTape.law_eq_pure_of_run_nil Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A + 1) (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)
    (by simp [hstop])]
  rw [CostedLaw.expectation_bind, CostedLaw.expectation_pure]
  have hcont : NativeTape.continueLaw Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n
      (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A + 1) [] (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)) =
      (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded A B)).map
        (NativeTape.Result.appendTrace
          (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A + 1) [] (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)).trace) := by
    simp [NativeTape.continueLaw, hstop, hc]
  rw [hcont, CostedLaw.expectation_map]
  have hind : ∀ r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control,
      pendingIndicator (NativeTape.Result.appendTrace
        (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A + 1) [] (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)).trace r) =
        pendingIndicator r := by
    intro r
    simp [pendingIndicator, NativeTape.Result.appendTrace]
  rw [show (fun r => pendingIndicator (NativeTape.Result.appendTrace
      (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A + 1) [] (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)).trace r)) =
      pendingIndicator from funext hind]

/-- The truncation failure mass equals the finite-fuel pending mass. -/
theorem truncationFailure_eq (n a b : ℕ) : truncationFailure n a b = pendingMass n a b := rfl

/-- For total weight at least two and positive `delta`, the prescribed truncation budget plus
one leaves pending probability at most `delta`. -/
theorem truncation_bound (a b : ℕ) (hN : 2 ≤ a + b) (delta : ℝ) (hδ : 0 < delta) :
    pendingProb (truncationBudget a b delta + 1) a b ≤ delta := by
  by_cases ha : a = 0
  · subst ha
    have hz : pendingProb (truncationBudget 0 b delta + 1) 0 b = 0 := by
      simp only [pendingProb]
      rw [pendingMass_left_endpoint (truncationBudget 0 b delta + 1) b (by omega)]
      simp
    rw [hz]
    linarith
  by_cases hb : b = 0
  · subst hb
    have hz : pendingProb (truncationBudget a 0 delta + 1) a 0 = 0 := by
      simp only [pendingProb]
      rw [pendingMass_right_endpoint (truncationBudget a 0 delta + 1) a (by omega) (by omega)]
      simp
    rw [hz]
    linarith
  have htail := tail_bound (truncationBudget a b delta) a b hN
  have hNpos : (0 : ℝ) < ((a + b : ℕ) : ℝ) := by
    have : (2 : ℝ) ≤ (a + b : ℕ) := by exact_mod_cast hN
    positivity
  have hpsi : (0 : ℝ) < (a : ℝ) * (b : ℝ) := by
    have ha' : (0 : ℝ) < (a : ℝ) := by
      have : (0 : ℕ) < a := Nat.pos_of_ne_zero ha
      exact_mod_cast this
    have hb' : (0 : ℝ) < (b : ℝ) := by
      have : (0 : ℕ) < b := Nat.pos_of_ne_zero hb
      exact_mod_cast this
    nlinarith
  have hne : ((a : ℝ) * (b : ℝ)) ≠ 0 := ne_of_gt hpsi
  have hkey : decayReal a b ≤ Real.exp (-(1 / ((a + b : ℕ) : ℝ) ^ 2)) := by
    have h := Real.add_one_le_exp (-(1 / ((a + b : ℕ) : ℝ) ^ 2))
    simp only [decayReal] at *
    linarith
  have hk : (truncationBudget a b delta : ℝ) / ((a + b : ℕ) : ℝ) ^ 2 =
      (Nat.ceil (((a : ℝ) * (b : ℝ)) / delta) : ℝ) := by
    show (((a + b) * (a + b) * Nat.ceil (((a : ℝ) * (b : ℝ)) / delta) : ℕ) : ℝ) /
        ((a + b : ℕ) : ℝ) ^ 2 = (Nat.ceil (((a : ℝ) * (b : ℝ)) / delta) : ℝ)
    rw [Nat.cast_mul, Nat.cast_mul]
    field_simp
  have hstep : decayReal a b ^ (truncationBudget a b delta) ≤
      Real.exp (-((truncationBudget a b delta : ℝ) / ((a + b : ℕ) : ℝ) ^ 2)) := by
    have hpow : (Real.exp (-(1 / ((a + b : ℕ) : ℝ) ^ 2))) ^ (truncationBudget a b delta) =
        Real.exp (-((truncationBudget a b delta : ℝ) / ((a + b : ℕ) : ℝ) ^ 2)) := by
      rw [← Real.exp_nat_mul]
      field_simp
    rw [← hpow]
    exact pow_le_pow_left₀ (le_of_lt (decayReal_pos a b hN)) hkey (truncationBudget a b delta)
  have hceil : ((a : ℝ) * (b : ℝ)) / delta ≤
      (Nat.ceil (((a : ℝ) * (b : ℝ)) / delta) : ℝ) := by
    exact_mod_cast Nat.le_ceil _
  have hexp : Real.exp (-((truncationBudget a b delta : ℝ) / ((a + b : ℕ) : ℝ) ^ 2)) ≤
      Real.exp (-(((a : ℝ) * (b : ℝ)) / delta)) := by
    rw [Real.exp_le_exp, hk]
    linarith
  have hone : Real.exp (-(((a : ℝ) * (b : ℝ)) / delta)) ≤
      1 / (((a : ℝ) * (b : ℝ)) / delta) := by
    have hpos : (0 : ℝ) < ((a : ℝ) * (b : ℝ)) / delta := by positivity
    rw [Real.exp_neg, inv_eq_one_div]
    have h1 : ((a : ℝ) * (b : ℝ)) / delta ≤ Real.exp (((a : ℝ) * (b : ℝ)) / delta) := by
      have := Real.add_one_le_exp (((a : ℝ) * (b : ℝ)) / delta)
      linarith
    exact one_div_le_one_div_of_le hpos h1
  have hdiv : 1 / (((a : ℝ) * (b : ℝ)) / delta) = delta / ((a : ℝ) * (b : ℝ)) := by
    field_simp [hne]
  have hkey3 : Real.exp (-(((a : ℝ) * (b : ℝ)) / delta)) ≤
      delta / ((a : ℝ) * (b : ℝ)) := hone.trans_eq hdiv
  have hfin : ((a : ℝ) * (b : ℝ)) * decayReal a b ^ (truncationBudget a b delta) ≤ delta := by
    calc ((a : ℝ) * (b : ℝ)) * decayReal a b ^ (truncationBudget a b delta)
        ≤ ((a : ℝ) * (b : ℝ)) *
            Real.exp (-((truncationBudget a b delta : ℝ) / ((a + b : ℕ) : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ ≤ ((a : ℝ) * (b : ℝ)) * Real.exp (-(((a : ℝ) * (b : ℝ)) / delta)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ ((a : ℝ) * (b : ℝ)) * (delta / ((a : ℝ) * (b : ℝ))) :=
          mul_le_mul_of_nonneg_left hkey3 (by positivity)
      _ = delta := by field_simp [hne]
  exact htail.trans hfin

/-- For positive input weights, every no-bit loader run with budget at most `A + 1` stops
because its fuel is exhausted. -/
theorem run_fuel_prefix (A B n : ℕ) (hn : n ≤ A + 1) (hA : 0 < A) (hB : 0 < B) :
    (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n [] (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)).stop = .fuel := by
  have hfinal : (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A + 1) [] (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)).stop = .fuel :=
    loader_run_fuel A B hA hB
  have hr :=
      NativeTape.run_add Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n
      (A + 1 - n) [] (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)
  rw [show n + (A + 1 - n) = A + 1 by omega] at hr
  by_cases hs : (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n [] (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)).stop = .fuel
  · exact hs
  · have hstop : (NativeTape.resume Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A + 1 - n)
        (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n [] (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B))).stop =
      (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n [] (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)).stop := by
      simp [NativeTape.resume, hs]
    rw [hr, hstop] at hfinal
    exact absurd hfinal hs

/-- For positive input weights, input pending mass is one throughout budgets at most `A + 1`. -/
theorem pendingInputMass_one (n A B : ℕ) (hn : n ≤ A + 1) (hA : 0 < A) (hB : 0 < B) :
    pendingInputMass n A B = 1 := by
  have hstop := run_fuel_prefix A B n hn hA hB
  unfold pendingInputMass
  rw [NativeTape.law_eq_pure_of_run_nil Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)
    (by simp [hstop])]
  rw [CostedLaw.expectation_pure]
  simp [pendingIndicator, hstop]

/-- An extended-real series consisting of `k + 1` initial ones followed by `g` has sum `k + 1`
plus the sum of `g`. -/
theorem tsum_prefix_shift (f g : ℕ → ℝ≥0∞) (k : ℕ)
    (h1 : ∀ n, n ≤ k → f n = 1) (h2 : ∀ m, f (k + 1 + m) = g m) :
    (∑' n, f n) = (k + 1) + (∑' m, g m) := by
  have key : ∀ j : ℕ, (∑' n, f n) = (Finset.sum (Finset.range j) f) + (∑' n, f (j + n)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hshift : (∑' n, f (j + n)) = f j + (∑' n, f (j + 1 + n)) := by
        have hh := tsum_eq_zero_add' (f := fun n => f (j + n)) ENNReal.summable
        have hh' : (∑' b, f (j + b)) = f j + (∑' b, f (j + (b + 1))) := by
          simpa only [Nat.add_zero] using! hh
        have hidx : (∑' b, f (j + (b + 1))) = (∑' b, f (j + 1 + b)) := by
          apply tsum_congr
          intro b
          congr 1
          omega
        rw [hh', hidx]
      rw [ih, hshift]
      calc Finset.sum (Finset.range j) f + (f j + (∑' n, f (j + 1 + n)))
          = f j + (Finset.sum (Finset.range j) f + (∑' n, f (j + 1 + n))) := by ac_rfl
        _ = Finset.sum (Finset.range (j + 1)) f + (∑' n, f (j + 1 + n)) := by
          rw [Finset.sum_range_succ]
          ac_rfl
  rw [key (k + 1)]
  have hfsum : Finset.sum (Finset.range (k + 1)) f = (k + 1 : ℝ≥0∞) := by
    have hc : Finset.sum (Finset.range (k + 1)) f =
        Finset.sum (Finset.range (k + 1)) (fun _ => (1 : ℝ≥0∞)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hlt : i < k + 1 := Finset.mem_range.mp hi
      exact h1 i (by omega)
    rw [hc, Finset.sum_const, Finset.card_range]
    norm_num
  rw [hfsum]
  have htail : (∑' n, f (k + 1 + n)) = ∑' m, g m := by
    apply tsum_congr
    intro m
    exact h2 m
  rw [htail]

/-- For positive input weights, the expected input step count is `A * B + A + 2` in ℝ≥0∞. -/
theorem expectedInputSteps_eq (A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    expectedInputSteps A B = ((A : ℝ≥0∞) * B) + A + 2 := by
  unfold expectedInputSteps
  rw [tsum_prefix_shift (f := fun n => pendingInputMass n A B)
      (g := fun n => pendingMass n A B) A
    (fun n hn => pendingInputMass_one n A B (by omega) hA hB)
    (fun m => pendingInputMass_eq m A B hA hB)]
  have hsteps : (∑' m, pendingMass m A B) = ((A : ℝ≥0∞) * B) + 1 := by
    show expectedSteps A B = _
    exact expectedSteps_eq A B (by omega)
  rw [hsteps]
  rw [show (2 : ℝ≥0∞) = 1 + 1 by norm_num]
  ac_rfl

/-- After accounting for loading, input pending mass satisfies the same geometric tail bound as
the loaded sampler. -/
theorem pendingInputMass_tail (n A B : ℕ) (hN : 2 ≤ A + B) (hA : 0 < A) (hB : 0 < B) :
    pendingInputMass (A + 1 + n + 1) A B ≤
      ENNReal.ofReal ((A : ℝ) * (B : ℝ)) * (ENNReal.ofReal (decayReal A B)) ^ n := by
  rw [show A + 1 + n + 1 = A + 1 + (n + 1) by omega]
  rw [pendingInputMass_eq (n + 1) A B hA hB]
  exact tail_bound_ennreal n A B hN

/-- For positive input weights, the real input pending probability at fuel `A + 1 + n` equals
the loaded pending probability at fuel `n`. -/
theorem pendingInputProb_eq (n A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    pendingInputProb (A + 1 + n) A B = pendingProb n A B := by
  unfold pendingInputProb pendingProb
  rw [pendingInputMass_eq n A B hA hB]

/-- For positive input weights and positive tolerance, the input truncation budget plus one
leaves pending probability at most that tolerance. -/
theorem pendingInputProb_truncation (A B : ℕ) (hN : 2 ≤ A + B) (hA : 0 < A) (hB : 0 < B)
    (delta : ℝ) (hδ : 0 < delta) :
    pendingInputProb (truncationBudgetInput A B delta + 1) A B ≤ delta := by
  have hbud : truncationBudgetInput A B delta + 1 = A + 1 + (truncationBudget A B delta + 1) := by
    simp only [truncationBudgetInput]
    omega
  rw [hbud, pendingInputProb_eq (truncationBudget A B delta + 1) A B hA hB]
  exact truncation_bound A B hN delta hδ

/-- A halted walk with positive total weight has an output. -/
theorem walk_halted_out (n : ℕ) (bs : List Bool) (a b : ℕ) (hN : 0 < a + b) :
    (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.walk n bs a b).stop = .halted → (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.walk n bs a b).out.isSome = true := by
  induction n generalizing bs a b with
  | zero =>
      cases a with
      | zero =>
          cases b with
          | zero => omega
          | succ b => simp [walk]
      | succ a => simp [walk]
  | succ n ih =>
      cases a with
      | zero =>
          cases b with
          | zero => omega
          | succ b => simp [walk]
      | succ a =>
          cases b with
          | zero => simp [walk]
          | succ b =>
              cases bs with
              | nil => simp [walk]
              | cons bit bs =>
                  cases bit with
                  | false =>
                      have key : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.walk (n + 1) (false :: bs) (a + 1) (b + 1) =
                          (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.walk n bs a (b + 2)).prependBit false := by
                        simp [walk]
                      rw [key]
                      simp only [WalkResult.prependBit]
                      intro h
                      exact ih bs a (b + 2) (by omega) h
                  | true =>
                      have key : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.walk (n + 1) (true :: bs) (a + 1) (b + 1) =
                          (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.walk n bs (a + 2) b).prependBit true := by
                        simp [walk]
                      rw [key]
                      simp only [WalkResult.prependBit]
                      intro h
                      exact ih bs (a + 2) b (by omega) h

/-- For a halted native race with positive total weight, the left and right outcome indicators
sum to one and the pending indicator is zero. -/
theorem race_halted_outcome (n : ℕ) (bs : List Bool) (a b : ℕ) (hN : 0 < a + b)
    (hr : (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n bs (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)).stop = .halted) :
    leftIndicator (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n bs (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)) +
        rightIndicator (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n bs (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)) = 1 ∧
      pendingIndicator (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n bs (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)) = 0 := by
  have hw := run_walk n bs a b
  have hstop : (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.walk n bs a b).stop = .halted := by
    rw [← hw.2.1]
    exact hr
  have hout : (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.walk n bs a b).out.isSome = true :=
    walk_halted_out n bs a b hN hstop
  have hcfg : (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n bs (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)).cfg =
      (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.walk n bs a b).cfg := hw.1
  cases ho :
      (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.walk n bs a b).out with
  | none => simp [ho] at hout
  | some bit =>
      have hhalt :
          (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n bs (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)).stop = .halted := hr
      have hdone : (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n bs (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)).cfg.q = .done := by
        rw [hcfg, WalkResult.cfg, ho]
      have hhead : (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n bs (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)).cfg.Tape.head =
          (if bit then Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol.out1 else Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol.out0) := by
        rw [hcfg, WalkResult.cfg, ho]
        cases bit <;> simp
            [Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.outputSymbol,
            Turing.Tape.write]
      have houtput : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n bs (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)) =
          (if bit then some true else some false) := by
        rw [Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output,
            if_pos ⟨hhalt, hdone⟩]
        cases bit <;> simp [hhead]
      constructor
      · cases bit with
        | false =>
            have ho' : RaceOutcome.of (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n bs (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)) = .left :=
              RaceOutcome.of_eq_left _ (by rw [houtput]; rfl)
            simp [leftIndicator, rightIndicator, ho']
        | true =>
            have ho' : RaceOutcome.of (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n bs (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)) = .right :=
              RaceOutcome.of_eq_right _ (by rw [houtput]; rfl)
            simp [leftIndicator, rightIndicator, ho']
      · have hstopne : (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n bs (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)).stop ≠ .fuel := by
          rw [hhalt]
          simp
        simp [pendingIndicator, hstopne]

/-- For positive total weight, the left-event mass, right-event mass, and pending mass sum to
one. -/
theorem law_outcome_partition (n a b : ℕ) (hN : 0 < a + b) :
    leftEvent n a b + rightEvent n a b + pendingMass n a b = 1 := by
  have hpoint : ∀ r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control,
      (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) *
          (leftIndicator r + rightIndicator r + pendingIndicator r) =
        (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) * 1 := by
    intro r
    by_cases hr : r ∈ (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)).support
    · obtain ⟨hrun, _hu, hne⟩ :=
        NativeTape.law_support_run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r hr
      by_cases hs : r.stop = .fuel
      · have hout : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r = Option.none := by
          unfold Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output
          rw [if_neg (by simp [hs])]
        have ho' : RaceOutcome.of r = .none := RaceOutcome.of_eq_none _ hout
        simp [leftIndicator, rightIndicator, pendingIndicator, ho', hs]
      · have hhalt : r.stop = .halted := by
          cases hstop : r.stop with
          | halted => rfl
          | fuel => exact absurd hstop hs
          | needBits => exact absurd hstop hne
        have hres := race_halted_outcome n r.bits a b hN (by rw [hrun]; exact hhalt)
        rw [hrun] at hres
        simp [hres.1, hres.2]
    · have hz : (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) = 0 := by
        rw [PMF.mem_support_iff] at hr
        exact not_ne_iff.mp hr
      rw [hz]
      ring
  calc leftEvent n a b + rightEvent n a b + pendingMass n a b
      = ∑' r, (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) *
          (leftIndicator r + rightIndicator r + pendingIndicator r) := by
        unfold leftEvent rightEvent pendingMass CostedLaw.expectation
        rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
        apply tsum_congr
        intro r
        ring
    _ = ∑' r, (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r) * 1 := by
        apply tsum_congr
        intro r
        exact hpoint r
    _ = 1 := by
        rw [tsum_congr (fun r => by rw [mul_one])]
        exact (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b)).tsum_coe

/-- Embedding a sum of natural numbers into ℝ equals the sum of their embeddings. -/
theorem natCast_add (a b : ℕ) : ((a + b : ℕ) : ℝ) = (a : ℝ) + (b : ℝ) := by
  push_cast
  ring

/-- For positive total weight, the finite-fuel right-event probability is at most `a / (a + b)`. -/
theorem rightEventProb_le (n a b : ℕ) (hab : 0 < a + b) :
    rightEventProb n a b ≤ (a : ℝ) / ((a + b : ℕ) : ℝ) := by
  unfold rightEventProb
  have hle := rightEvent_le_rightMass n a b
  have h1 : rightEvent n a b ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (rightEvent_le_one n a b) ENNReal.one_lt_top)
  have h2 : rightMass a b ≠ ∞ := rightMass_ne_top a b
  have hle' : (rightEvent n a b).toReal ≤ (rightMass a b).toReal :=
    (ENNReal.toReal_le_toReal h1 h2).mpr hle
  have hg := (Qatlib.Concepts.AdversaryBounds.AdvDuality.clause23_complete a b).1 (by omega)
  rw [hg.2, ENNReal.toReal_ofReal (by positivity)] at hle'
  rw [natCast_add a b]
  exact hle'

/-- For positive total weight, the finite-fuel left-event probability is at most `b / (a + b)`. -/
theorem leftEventProb_le (n a b : ℕ) (hab : 0 < a + b) :
    leftEventProb n a b ≤ (b : ℝ) / ((a + b : ℕ) : ℝ) := by
  unfold leftEventProb
  have hle := leftEvent_le_leftMass n a b
  have h1 : leftEvent n a b ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (leftEvent_le_one n a b) ENNReal.one_lt_top)
  have h2 : leftMass a b ≠ ∞ := leftMass_ne_top a b
  have hle' : (leftEvent n a b).toReal ≤ (leftMass a b).toReal :=
    (ENNReal.toReal_le_toReal h1 h2).mpr hle
  have hg := (Qatlib.Concepts.AdversaryBounds.AdvDuality.clause23_complete a b).1 (by omega)
  rw [hg.1, ENNReal.toReal_ofReal (by positivity)] at hle'
  rw [natCast_add a b]
  exact hle'

/-- For positive total weight, the real left-event, right-event, and pending probabilities sum
to one. -/
theorem event_partition_real (n a b : ℕ) (hN : 0 < a + b) :
    leftEventProb n a b + rightEventProb n a b + pendingProb n a b = 1 := by
  have hp := law_outcome_partition n a b hN
  unfold leftEventProb rightEventProb pendingProb
  have h1 : leftEvent n a b ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (leftEvent_le_one n a b) ENNReal.one_lt_top)
  have h2 : rightEvent n a b ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt (rightEvent_le_one n a b) ENNReal.one_lt_top)
  have h3 : pendingMass n a b ≠ ∞ := pendingMass_ne_top n a b
  have hsum : (leftEvent n a b + rightEvent n a b + pendingMass n a b).toReal =
      (leftEvent n a b).toReal + (rightEvent n a b).toReal + (pendingMass n a b).toReal := by
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨h1, h2⟩) h3]
    rw [ENNReal.toReal_add h1 h2]
  rw [← hsum, hp, ENNReal.toReal_one]

/-- The finite-fuel left-event probability differs from `(1 - pendingProb n a b) * b / (a + b)`
by at most the pending probability. -/
theorem truncation_bias_left (n a b : ℕ) (hN : 0 < a + b) :
    |leftEventProb n a b - (1 - pendingProb n a b) * ((b : ℝ) / (a + b : ℝ))|
      ≤ pendingProb n a b := by
  have hpart : leftEventProb n a b + rightEventProb n a b + pendingProb n a b = 1 := by
    have hp := law_outcome_partition n a b hN
    unfold leftEventProb rightEventProb pendingProb
    have h1 : leftEvent n a b ≠ ∞ :=
      ne_of_lt (lt_of_le_of_lt (leftEvent_le_one n a b) ENNReal.one_lt_top)
    have h2 : rightEvent n a b ≠ ∞ :=
      ne_of_lt (lt_of_le_of_lt (rightEvent_le_one n a b) ENNReal.one_lt_top)
    have h3 : pendingMass n a b ≠ ∞ := pendingMass_ne_top n a b
    have hsum : (leftEvent n a b + rightEvent n a b + pendingMass n a b).toReal =
        (leftEvent n a b).toReal + (rightEvent n a b).toReal + (pendingMass n a b).toReal := by
      rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨h1, h2⟩) h3]
      rw [ENNReal.toReal_add h1 h2]
    rw [← hsum, hp, ENNReal.toReal_one]
  have hLmass : (leftMass a b).toReal = (b : ℝ) / (a + b : ℝ) := by
    have hg := (clause23_complete a b).1 hN
    rw [hg.1, ENNReal.toReal_ofReal (by positivity)]
  have hRmass : (rightMass a b).toReal = (a : ℝ) / (a + b : ℝ) := by
    have hg := (clause23_complete a b).1 hN
    rw [hg.2, ENNReal.toReal_ofReal (by positivity)]
  have hL : leftEventProb n a b ≤ (b : ℝ) / (a + b : ℝ) := by
    unfold leftEventProb
    have hle := leftEvent_le_leftMass n a b
    have h1 : leftEvent n a b ≠ ∞ :=
      ne_of_lt (lt_of_le_of_lt (leftEvent_le_one n a b) ENNReal.one_lt_top)
    have hle' : (leftEvent n a b).toReal ≤ (leftMass a b).toReal :=
      (ENNReal.toReal_le_toReal h1 (leftMass_ne_top a b)).mpr hle
    exact hle'.trans_eq hLmass
  have hR : rightEventProb n a b ≤ (a : ℝ) / (a + b : ℝ) := by
    unfold rightEventProb
    have hle := rightEvent_le_rightMass n a b
    have h1 : rightEvent n a b ≠ ∞ :=
      ne_of_lt (lt_of_le_of_lt (rightEvent_le_one n a b) ENNReal.one_lt_top)
    have hle' : (rightEvent n a b).toReal ≤ (rightMass a b).toReal :=
      (ENNReal.toReal_le_toReal h1 (rightMass_ne_top a b)).mpr hle
    exact hle'.trans_eq hRmass
  have hLR : (b : ℝ) / (a + b : ℝ) + (a : ℝ) / (a + b : ℝ) = 1 := by
    have hpos : (0 : ℝ) < (a + b : ℝ) := by exact_mod_cast hN
    field_simp
    ring
  have hP0 : 0 ≤ pendingProb n a b := by
    unfold pendingProb
    exact ENNReal.toReal_nonneg
  have hP1 : pendingProb n a b ≤ 1 := by
    have hle := pendingMass_le_one n a b
    have h1 : pendingMass n a b ≠ ∞ := pendingMass_ne_top n a b
    have h' : (pendingMass n a b).toReal ≤ (1 : ℝ≥0∞).toReal :=
      (ENNReal.toReal_le_toReal h1 (by simp)).mpr hle
    simpa using! h'
  have hL0 : 0 ≤ (b : ℝ) / (a + b : ℝ) := by
    have hpos : (0 : ℝ) < (a + b : ℝ) := by exact_mod_cast hN
    positivity
  have hR0 : 0 ≤ (a : ℝ) / (a + b : ℝ) := by
    have hpos : (0 : ℝ) < (a + b : ℝ) := by exact_mod_cast hN
    positivity
  have hL1 : (b : ℝ) / (a + b : ℝ) ≤ 1 := by
    have hpos : (0 : ℝ) < (a + b : ℝ) := by exact_mod_cast hN
    have hb0 : (0 : ℝ) ≤ (b : ℝ) := by positivity
    rw [div_le_one hpos]
    linarith
  have hR1 : (a : ℝ) / (a + b : ℝ) ≤ 1 := by
    have hpos : (0 : ℝ) < (a + b : ℝ) := by exact_mod_cast hN
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := by positivity
    rw [div_le_one hpos]
    linarith
  set L : ℝ := (b : ℝ) / (a + b : ℝ) with hLdef
  set R : ℝ := (a : ℝ) / (a + b : ℝ) with hRdef
  set P : ℝ := pendingProb n a b with hPdef
  set Ln : ℝ := leftEventProb n a b with hLnDef
  set Rn : ℝ := rightEventProb n a b with hRnDef
  have hL' : Ln ≤ L := by rw [hLnDef, hLdef]; exact hL
  have hR' : Rn ≤ R := by rw [hRnDef, hRdef]; exact hR
  have hpart' : Ln + Rn + P = 1 := by rw [hLnDef, hRnDef, hPdef]; exact hpart
  have hLR' : L + R = 1 := by rw [hLdef, hRdef]; exact hLR
  have hP0' : 0 ≤ P := by rw [hPdef]; exact hP0
  have hP1' : P ≤ 1 := by rw [hPdef]; exact hP1
  have hL1' : L ≤ 1 := by rw [hLdef]; exact hL1
  have hR1' : R ≤ 1 := by rw [hRdef]; exact hR1
  have hL0' : 0 ≤ L := by rw [hLdef]; exact hL0
  have hR0' : 0 ≤ R := by rw [hRdef]; exact hR0
  rw [abs_le]
  constructor <;> nlinarith

/-- The finite-fuel right-event probability differs from `(1 - pendingProb n a b) * a / (a + b)`
by at most the pending probability. -/
theorem truncation_bias_right (n a b : ℕ) (hN : 0 < a + b) :
    |rightEventProb n a b - (1 - pendingProb n a b) * ((a : ℝ) / (a + b : ℝ))|
      ≤ pendingProb n a b := by
  have hpart : leftEventProb n a b + rightEventProb n a b + pendingProb n a b = 1 := by
    have hp := law_outcome_partition n a b hN
    unfold leftEventProb rightEventProb pendingProb
    have h1 : leftEvent n a b ≠ ∞ :=
      ne_of_lt (lt_of_le_of_lt (leftEvent_le_one n a b) ENNReal.one_lt_top)
    have h2 : rightEvent n a b ≠ ∞ :=
      ne_of_lt (lt_of_le_of_lt (rightEvent_le_one n a b) ENNReal.one_lt_top)
    have h3 : pendingMass n a b ≠ ∞ := pendingMass_ne_top n a b
    have hsum : (leftEvent n a b + rightEvent n a b + pendingMass n a b).toReal =
        (leftEvent n a b).toReal + (rightEvent n a b).toReal + (pendingMass n a b).toReal := by
      rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨h1, h2⟩) h3]
      rw [ENNReal.toReal_add h1 h2]
    rw [← hsum, hp, ENNReal.toReal_one]
  have hRmass : (rightMass a b).toReal = (a : ℝ) / (a + b : ℝ) := by
    have hg := (clause23_complete a b).1 hN
    rw [hg.2, ENNReal.toReal_ofReal (by positivity)]
  have hR : rightEventProb n a b ≤ (a : ℝ) / (a + b : ℝ) := by
    unfold rightEventProb
    have hle := rightEvent_le_rightMass n a b
    have h1 : rightEvent n a b ≠ ∞ :=
      ne_of_lt (lt_of_le_of_lt (rightEvent_le_one n a b) ENNReal.one_lt_top)
    have hle' : (rightEvent n a b).toReal ≤ (rightMass a b).toReal :=
      (ENNReal.toReal_le_toReal h1 (rightMass_ne_top a b)).mpr hle
    exact hle'.trans_eq hRmass
  have hL : leftEventProb n a b ≤ (b : ℝ) / (a + b : ℝ) := by
    unfold leftEventProb
    have hle := leftEvent_le_leftMass n a b
    have h1 : leftEvent n a b ≠ ∞ :=
      ne_of_lt (lt_of_le_of_lt (leftEvent_le_one n a b) ENNReal.one_lt_top)
    have hle' : (leftEvent n a b).toReal ≤ (leftMass a b).toReal :=
      (ENNReal.toReal_le_toReal h1 (leftMass_ne_top a b)).mpr hle
    have hg := (clause23_complete a b).1 hN
    rw [hg.1, ENNReal.toReal_ofReal (by positivity)] at hle'
    exact hle'
  have hLR : (b : ℝ) / (a + b : ℝ) + (a : ℝ) / (a + b : ℝ) = 1 := by
    have hpos : (0 : ℝ) < (a + b : ℝ) := by exact_mod_cast hN
    field_simp
    ring
  have hP0 : 0 ≤ pendingProb n a b := by
    unfold pendingProb
    exact ENNReal.toReal_nonneg
  have hP1 : pendingProb n a b ≤ 1 := by
    have hle := pendingMass_le_one n a b
    have h1 : pendingMass n a b ≠ ∞ := pendingMass_ne_top n a b
    have h' : (pendingMass n a b).toReal ≤ (1 : ℝ≥0∞).toReal :=
      (ENNReal.toReal_le_toReal h1 (by simp)).mpr hle
    simpa using! h'
  have hL0 : 0 ≤ (b : ℝ) / (a + b : ℝ) := by
    have hpos : (0 : ℝ) < (a + b : ℝ) := by exact_mod_cast hN
    positivity
  have hR0 : 0 ≤ (a : ℝ) / (a + b : ℝ) := by
    have hpos : (0 : ℝ) < (a + b : ℝ) := by exact_mod_cast hN
    positivity
  have hR1 : (a : ℝ) / (a + b : ℝ) ≤ 1 := by
    have hpos : (0 : ℝ) < (a + b : ℝ) := by exact_mod_cast hN
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := by positivity
    rw [div_le_one hpos]
    linarith
  set L : ℝ := (b : ℝ) / (a + b : ℝ) with hLdef
  set R : ℝ := (a : ℝ) / (a + b : ℝ) with hRdef
  set P : ℝ := pendingProb n a b with hPdef
  set Ln : ℝ := leftEventProb n a b with hLnDef
  set Rn : ℝ := rightEventProb n a b with hRnDef
  have hL' : Ln ≤ L := by rw [hLnDef, hLdef]; exact hL
  have hR' : Rn ≤ R := by rw [hRnDef, hRdef]; exact hR
  have hpart' : Ln + Rn + P = 1 := by rw [hLnDef, hRnDef, hPdef]; exact hpart
  have hLR' : L + R = 1 := by rw [hLdef, hRdef]; exact hLR
  have hP0' : 0 ≤ P := by rw [hPdef]; exact hP0
  have hP1' : P ≤ 1 := by rw [hPdef]; exact hP1
  have hR1' : R ≤ 1 := by rw [hRdef]; exact hR1
  have hL0' : 0 ≤ L := by rw [hLdef]; exact hL0
  have hR0' : 0 ≤ R := by rw [hRdef]; exact hR0
  rw [abs_le]
  constructor <;> nlinarith

/-- A tree with positive leaf weights has positive total weight. -/
theorem positiveTree_weight (t : BucketTree) (h : PositiveTree t) : 0 < totalWeight t := by
  induction t with
  | leaf w =>
      simpa [PositiveTree, totalWeight] using! h
  | node l r ihl ihr =>
      have hl : PositiveTree l := h.1
      have hr : PositiveTree r := h.2
      simp only [totalWeight]
      have h1 := ihl hl
      have h2 := ihr hr
      omega

/-- The weight of a leaf selected by a valid path is at most the total tree weight. -/
theorem leafWeight_le (t : BucketTree) (p : List Bool) (h : isPath t p) :
    leafWeight t p ≤ totalWeight t := by
  induction t generalizing p with
  | leaf w => simp [leafWeight, totalWeight]
  | node l r ihl ihr =>
      cases p with
      | nil => simp [isPath] at h
      | cons b bs =>
          cases b with
          | true =>
              have hchild : isPath l bs := by simpa [isPath] using! h
              have hm := ihl bs hchild
              simp only [leafWeight, totalWeight]
              omega
          | false =>
              have hchild : isPath r bs := by simpa [isPath] using! h
              have hm := ihr bs hchild
              simp only [leafWeight, totalWeight]
              omega

/-- In a positive tree, the mass of a valid leaf path is its leaf weight divided by the total
tree weight. -/
theorem leafMass_eq (t : BucketTree) (p : List Bool) (h : isPath t p)
    (hpos : PositiveTree t) :
    leafMass t p = (leafWeight t p : ℝ) / (totalWeight t : ℝ) := by
  have hW : 0 < totalWeight t := positiveTree_weight t hpos
  induction t generalizing p with
  | leaf w =>
      have hw : 0 < w := by simpa [PositiveTree] using! hpos
      have hne : (w : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hw)
      rw [leafMass, leafWeight]
      simp only [totalWeight]
      rw [div_self hne]
  | node l r ihl ihr =>
      have hWL : 0 < totalWeight l := positiveTree_weight l hpos.1
      have hWR : 0 < totalWeight r := positiveTree_weight r hpos.2
      have hneL : (totalWeight l : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hWL)
      have hneR : (totalWeight r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hWR)
      have hneW : ((totalWeight l + totalWeight r : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (by omega)
      have hcast : ((totalWeight l + totalWeight r : ℕ) : ℝ) =
          (totalWeight l : ℝ) + (totalWeight r : ℝ) := by
        push_cast
        ring
      have hcast2 : ((totalWeight (.node l r) : ℕ) : ℝ) =
          (totalWeight l : ℝ) + (totalWeight r : ℝ) := by
        simp only [totalWeight]
        push_cast
        ring
      cases p with
      | nil => simp [isPath] at h
      | cons b bs =>
          cases b with
          | true =>
              have hchild : isPath l bs := by simpa [isPath] using! h
              have hm := ihl bs hchild hpos.1 hWL
              rw [leafMass, leafWeight]
              rw [hm, hcast, hcast2]
              field_simp
          | false =>
              have hchild : isPath r bs := by simpa [isPath] using! h
              have hm := ihr bs hchild hpos.2 hWR
              rw [leafMass, leafWeight]
              rw [hm, hcast, hcast2]
              field_simp

/-- The sum of leaf masses in a positive tree is one. -/
theorem massSum_eq_one (t : BucketTree) (hpos : PositiveTree t) : massSum t = 1 := by
  induction t with
  | leaf w =>
      simp [massSum]
  | node l r ihl ihr =>
      have hWL : 0 < totalWeight l := positiveTree_weight l hpos.1
      have hWR : 0 < totalWeight r := positiveTree_weight r hpos.2
      have hneL : (totalWeight l : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hWL)
      have hneR : (totalWeight r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hWR)
      have hneW : ((totalWeight l + totalWeight r : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (by omega)
      rw [massSum, ihl hpos.1, ihr hpos.2]
      have hcast : ((totalWeight l + totalWeight r : ℕ) : ℝ) =
          (totalWeight l : ℝ) + (totalWeight r : ℝ) := by
        push_cast
        ring
      rw [hcast]
      field_simp

/-- The nodewise bit-cost ledger at reach weight `reach` equals `reach` times the recursive tree
bit cost. -/
theorem treeBitsByNodes_eq (t : BucketTree) (reach : ℝ) :
    treeBitsByNodes t reach = reach * treeBits t := by
  induction t generalizing reach with
  | leaf w => simp [treeBitsByNodes, treeBits]
  | node l r ihl ihr =>
      rw [treeBitsByNodes, treeBits, ihl, ihr]
      ring

/-- The nodewise step-cost ledger at reach weight `reach` equals `reach` times the recursive
tree step cost. -/
theorem treeStepsByNodes_eq (t : BucketTree) (reach : ℝ) :
    treeStepsByNodes t reach = reach * treeSteps t := by
  induction t generalizing reach with
  | leaf w => simp [treeStepsByNodes, treeSteps]
  | node l r ihl ihr =>
      rw [treeStepsByNodes, treeSteps, ihl, ihr]
      ring

/-- The recursive tree bit cost equals the nodewise bit-cost ledger at unit reach. -/
theorem treeBits_eq_nodes (t : BucketTree) : treeBits t = treeBitsByNodes t 1 := by
  rw [treeBitsByNodes_eq]
  ring

/-- The recursive tree step cost equals the nodewise step-cost ledger at unit reach. -/
theorem treeSteps_eq_nodes (t : BucketTree) : treeSteps t = treeStepsByNodes t 1 := by
  rw [treeStepsByNodes_eq]
  ring

/-- For positive node weights, expected bits equal `WL * WR` and expected input steps equal `WL
* WR + WL + 2`. -/
theorem node_race_cost (WL WR : ℕ) (hWL : 0 < WL) (hWR : 0 < WR) :
    expectedBits WL WR = ((WL : ℝ≥0∞) * WR) ∧
      expectedInputSteps WL WR = ((WL : ℝ≥0∞) * WR) + (WL : ℝ≥0∞) + 2 := by
  constructor
  · exact expectedBits_eq WL WR
  · exact expectedInputSteps_eq WL WR hWL hWR

/-- A collection of leaf normalization, total-mass, and nodewise bit and step accounting laws
for bucket trees. -/
structure MultiBucketLaws where

  leaf_mass : ∀ t p, PositiveTree t → isPath t p →
    leafMass t p = (leafWeight t p : ℝ) / (totalWeight t : ℝ)

  mass_sum : ∀ t, PositiveTree t → massSum t = 1

  bits : ∀ t, treeBits t = treeBitsByNodes t 1

  steps : ∀ t, treeSteps t = treeStepsByNodes t 1

/-- Establishes the leaf mass, normalization, and nodewise resource identities packaged in
`MultiBucketLaws`. -/
theorem clause23_multibucket : MultiBucketLaws := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t p hpos h
    exact leafMass_eq t p h hpos
  · intro t hpos
    exact massSum_eq_one t hpos
  · intro t
    exact treeBits_eq_nodes t
  · intro t
    exact treeSteps_eq_nodes t

/-- When pending probability is below one, the left probability conditioned on completion
differs from `b / (a + b)` by at most `pendingProb / (1 - pendingProb)`. -/
theorem truncation_bias_relative (n a b : ℕ) (hN : 0 < a + b) (hP : pendingProb n a b < 1) :
    |leftEventProb n a b / (1 - pendingProb n a b) - (b : ℝ) / (a + b : ℝ)|
      ≤ pendingProb n a b / (1 - pendingProb n a b) := by
  have hden : (0 : ℝ) < 1 - pendingProb n a b := by
    have hle := pendingMass_le_one n a b
    have h1 : pendingMass n a b ≠ ∞ := pendingMass_ne_top n a b
    have h' : (pendingMass n a b).toReal ≤ (1 : ℝ≥0∞).toReal :=
      (ENNReal.toReal_le_toReal h1 (by simp)).mpr hle
    have hP1 : pendingProb n a b ≤ 1 := by
      simpa using! h'
    linarith
  have hbias := truncation_bias_left n a b hN
  have hkey : leftEventProb n a b / (1 - pendingProb n a b) - (b : ℝ) / (a + b : ℝ) =
      (leftEventProb n a b - (1 - pendingProb n a b) * ((b : ℝ) / (a + b : ℝ))) /
        (1 - pendingProb n a b) := by
    have hpos : (0 : ℝ) < (a + b : ℝ) := by exact_mod_cast hN
    have hne : (a + b : ℝ) ≠ 0 := by exact_mod_cast (by omega)
    field_simp
  rw [hkey, abs_div, abs_of_pos hden]
  rw [div_le_iff₀ hden]
  have hcancel : (pendingProb n a b / (1 - pendingProb n a b)) * (1 - pendingProb n a b) =
      pendingProb n a b := by
    field_simp
  rw [hcancel]
  exact hbias

/-- For weights `2 ^ m` and one, expected bits are `2 ^ m`, expected steps are `2 ^ m + 1`, and
the encoded input length is `2 ^ m + 2`. -/
theorem binaryWeight_cost (m : ℕ) :
    expectedBits (2 ^ m) 1 = ((2 ^ m : ℕ) : ℝ≥0∞) ∧
      expectedSteps (2 ^ m) 1 = ((2 ^ m : ℕ) : ℝ≥0∞) + 1 ∧
      (Qatlib.Concepts.AdversaryBounds.AdvDuality.encodedInput (2 ^ m) 1).length = 2 ^ m + 2 := by
  have hpos : 0 < 2 ^ m := by positivity
  constructor
  · rw [expectedBits_eq]
    norm_num
  constructor
  · rw [expectedSteps_eq _ _ (by omega)]
    norm_num
  · rw [Qatlib.Concepts.AdversaryBounds.AdvDuality.encodedInput_length (2 ^ m) 1 hpos (by omega)]
    simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.encodedWeight]

/-- The indicator that `stateLabel state r` equals `some true` is the left indicator when
`state` is true and the right indicator otherwise. -/
theorem stateLabel_indicator (state : Bool) (r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control) :
    (if stateLabel state r = some true then 1 else 0) =
      (if state = true then leftIndicator r else rightIndicator r) := by
  cases ho : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r with
  | none => cases state <;> simp [stateLabel, ho, RaceOutcome.of, leftIndicator, rightIndicator]
  | some b =>
      cases b <;> cases state <;>
        simp [stateLabel, ho, RaceOutcome.of, leftIndicator, rightIndicator]

/-- At a state with positive total weight, the left selection probability is `b s / (a s + b
s)`. -/
theorem stateWeighted_leftProb (S : Type) (a b : S → ℕ) (s : S) (h : 0 < a s + b s) :
    leftProb (a s) (b s) = (b s : ℝ) / ((a s : ℝ) + (b s : ℝ)) :=
  leftProb_eq (a s) (b s) h

/-- For positive total weight, the mass of the true state label is `b / (a + b)`. -/
theorem stateLabelMass_true (a b : ℕ) (hN : 0 < a + b) :
    stateLabelMass a b true = (b : ℝ) / ((a : ℝ) + (b : ℝ)) := by
  have hsum : (∑' r, NativeTape.haltedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r *
        (if stateLabel true r = some true then 1 else 0)) = leftMass a b := by
    simp only [leftMass]
    apply tsum_congr
    intro r
    rw [stateLabel_indicator true r]
    simp
  unfold stateLabelMass
  rw [hsum]
  have hg := (clause23_complete a b).1 hN
  rw [hg.1, ENNReal.toReal_ofReal (by positivity)]

/-- For positive total weight, the mass of the false state label is `a / (a + b)`. -/
theorem stateLabelMass_false (a b : ℕ) (hN : 0 < a + b) :
    stateLabelMass a b false = (a : ℝ) / ((a : ℝ) + (b : ℝ)) := by
  have hsum : (∑' r, NativeTape.haltedMass Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded a b) r *
        (if stateLabel false r = some true then 1 else 0)) = rightMass a b := by
    simp only [rightMass]
    apply tsum_congr
    intro r
    rw [stateLabel_indicator false r]
    simp
  unfold stateLabelMass
  rw [hsum]
  have hg := (clause23_complete a b).1 hN
  rw [hg.2, ENNReal.toReal_ofReal (by positivity)]

/-- For nonnegative `x`, the real value of the encoded weight is at most `N * x`. -/
theorem encWeight_le (N : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (encWeight N x : ℝ) ≤ N * x := by
  unfold encWeight
  exact Nat.floor_le (mul_nonneg (Nat.cast_nonneg N) hx)

/-- The scaled real value `N * x` is strictly less than the encoded weight plus one. -/
theorem encWeight_gt (N : ℕ) (x : ℝ) : N * x < (encWeight N x : ℝ) + 1 := by
  unfold encWeight
  exact Nat.lt_floor_add_one (N * x)

/-- For nonnegative `x`, the encoding defect belongs to the half-open interval `[0, 1)`. -/
theorem encDefect_range (N : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ encDefect N x ∧ encDefect N x < 1 := by
  have h1 := encWeight_le N x hx
  have h2 := encWeight_gt N x
  unfold encDefect
  constructor <;> linarith

/-- For complementary nonnegative targets and encoding defects in `[0, 1)`, the normalized
encoded weight `B / (A + B)` differs from `v` by at most `1 / (A + B)`. -/
theorem enc_error_aux (N A B u v α β : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hα : α = N * u - A) (hβ : β = N * v - B) (hS : 0 < A + B) :
    |B / (A + B) - v| ≤ 1 / (A + B) := by
  have hid : B * u - v * A = v * α - u * β := by
    rw [hα, hβ]
    ring
  have hnum : |B * u - v * A| ≤ 1 := by
    rw [hid, abs_le]
    constructor
    · have h1 : v * α ≤ v := by
        have := mul_le_mul_of_nonneg_left hα1.le hv
        simpa using! this
      have h2 : 0 ≤ u * β := mul_nonneg hu hβ0
      have h3 : v ≤ 1 := by linarith
      nlinarith
    · have h1 : u * β ≤ u := by
        have := mul_le_mul_of_nonneg_left hβ1.le hu
        simpa using! this
      have h2 : 0 ≤ v * α := mul_nonneg hv hα0
      have h3 : u ≤ 1 := by linarith
      nlinarith
  have hkey : |B / (A + B) - v| = |B * u - v * A| / (A + B) := by
    have h1 : B / (A + B) - v = (B * u - v * A) / (A + B) := by
      have hb : B - B * v = B * u := by
        have h := congrArg (fun z : ℝ => B * z) huv
        linarith
      field_simp
      linarith
    rw [h1, abs_div, abs_of_pos hS]
  rw [hkey]
  exact div_le_div_of_nonneg_right hnum (le_of_lt hS)

/-- For complementary nonnegative targets and `N ≥ 3`, the encoded left probability differs from
`v` by at most the reciprocal of the total encoded weight. -/
theorem encLeftProb_error (N : ℕ) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1)
    (hN : 3 ≤ N) :
    |leftProb (encWeight N u) (encWeight N v) - v|
      ≤ 1 / ((encWeight N u + encWeight N v : ℕ) : ℝ) := by
  have hA1 : (encWeight N u : ℝ) ≤ N * u := encWeight_le N u hu
  have hB1 : (encWeight N v : ℝ) ≤ N * v := encWeight_le N v hv
  have hA2 : N * u < (encWeight N u : ℝ) + 1 := encWeight_gt N u
  have hB2 : N * v < (encWeight N v : ℝ) + 1 := encWeight_gt N v
  have hsum : 0 < (encWeight N u : ℝ) + (encWeight N v : ℝ) := by
    have hA3 : (N : ℝ) * u - 1 < (encWeight N u : ℝ) := by linarith
    have hB3 : (N : ℝ) * v - 1 < (encWeight N v : ℝ) := by linarith
    have h1 : ((N : ℝ) * u + (N : ℝ) * v : ℝ) - 2 <
        (encWeight N u : ℝ) + (encWeight N v : ℝ) := by linarith
    have h2 : (N : ℝ) * u + (N : ℝ) * v = (N : ℝ) * (u + v) := by ring
    rw [h2] at h1
    have h3 : (N : ℝ) * (u + v) = (N : ℝ) := by rw [huv]; norm_num
    rw [h3] at h1
    have h4 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h5 : (0 : ℝ) < (N : ℝ) - 2 := by linarith
    linarith
  have hab : 0 < encWeight N u + encWeight N v := by exact_mod_cast hsum
  have hl := leftProb_eq (encWeight N u) (encWeight N v) hab
  have hα0 : 0 ≤ N * u - (encWeight N u : ℝ) := by linarith
  have hα1 : N * u - (encWeight N u : ℝ) < 1 := by linarith
  have hβ0 : 0 ≤ N * v - (encWeight N v : ℝ) := by linarith
  have hβ1 : N * v - (encWeight N v : ℝ) < 1 := by linarith
  have h := enc_error_aux N (encWeight N u : ℝ) (encWeight N v : ℝ) u v
    (N * u - (encWeight N u : ℝ)) (N * v - (encWeight N v : ℝ))
    hu hv huv hα0 hα1 hβ0 hβ1 rfl rfl hsum
  rw [hl]
  rw [← natCast_add (encWeight N u) (encWeight N v)]
  rw [← natCast_add (encWeight N u) (encWeight N v)] at h
  exact h

/-- For positive total weight, the deficit of the finite left-event probability from `b / (a +
b)` is at most the pending probability. -/
theorem leftEventProb_deficit (n a b : ℕ) (hab : 0 < a + b) :
    (b : ℝ) / ((a + b : ℕ) : ℝ) - leftEventProb n a b ≤ pendingProb n a b := by
  have hpart := event_partition_real n a b hab
  have hR := rightEventProb_le n a b hab
  have hLR : (b : ℝ) / ((a + b : ℕ) : ℝ) + (a : ℝ) / ((a + b : ℕ) : ℝ) = 1 := by
    have hne : ((a + b : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega)
    rw [← add_div]
    apply (div_eq_iff hne).2
    push_cast
    ring
  linarith

/-- For complementary nonnegative targets, `N ≥ 3`, and `N ≥ 1 / ε + 2` with positive `ε`, the
encoded left probability differs from `v` by at most `ε`. -/
theorem encError_le (N : ℕ) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1)
    (hN : 3 ≤ N) (ε : ℝ) (hε : 0 < ε) (hNε : (1 / ε + 2 : ℝ) ≤ N) :
    |leftProb (encWeight N u) (encWeight N v) - v| ≤ ε := by
  have herr := encLeftProb_error N u v hu hv huv hN
  have hA1 : (encWeight N u : ℝ) ≤ N * u := encWeight_le N u hu
  have hB1 : (encWeight N v : ℝ) ≤ N * v := encWeight_le N v hv
  have hA2 : (N : ℝ) * u < (encWeight N u : ℝ) + 1 := encWeight_gt N u
  have hB2 : (N : ℝ) * v < (encWeight N v : ℝ) + 1 := encWeight_gt N v
  have hsum : (encWeight N u : ℝ) + (encWeight N v : ℝ) > (N : ℝ) - 2 := by
    have hA3 : (N : ℝ) * u - 1 < (encWeight N u : ℝ) := by linarith
    have hB3 : (N : ℝ) * v - 1 < (encWeight N v : ℝ) := by linarith
    have h1 : ((N : ℝ) * u + (N : ℝ) * v : ℝ) - 2 <
        (encWeight N u : ℝ) + (encWeight N v : ℝ) := by linarith
    have h2 : (N : ℝ) * u + (N : ℝ) * v = (N : ℝ) * (u + v) := by ring
    rw [h2] at h1
    have h3 : (N : ℝ) * (u + v) = (N : ℝ) := by rw [huv]; norm_num
    rw [h3] at h1
    exact h1
  have hN2 : (0 : ℝ) < N - 2 := by
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have h1 : 1 / ((encWeight N u + encWeight N v : ℕ) : ℝ) ≤ 1 / (N - 2) := by
    have hcast : ((encWeight N u + encWeight N v : ℕ) : ℝ) =
        (encWeight N u : ℝ) + (encWeight N v : ℝ) := natCast_add _ _
    rw [hcast]
    exact one_div_le_one_div_of_le hN2 (le_of_lt hsum)
  have h2 : 1 / (N - 2) ≤ ε := by
    have hεpos : 0 < 1 / ε := one_div_pos.mpr hε
    have hne : (1 / ε : ℝ) ≤ N - 2 := by linarith
    have := one_div_le_one_div_of_le hεpos hne
    simpa using! this
  linarith

/-- The expected bit cost for encoded weights is the product of those encoded weights in ℝ≥0∞. -/
theorem encExpectedBits (N : ℕ) (u v : ℝ) :
    expectedBits (encWeight N u) (encWeight N v) =
      ((encWeight N u : ℝ≥0∞) * encWeight N v) := by
  rw [expectedBits_eq]

/-- For complementary nonnegative targets, the real expected bit cost of their encoded weights
is at most `N² / 4`. -/
theorem encExpectedBits_le (N : ℕ) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1) :
    (expectedBits (encWeight N u) (encWeight N v)).toReal ≤ (N : ℝ) ^ 2 / 4 := by
  have hA := encWeight_le N u hu
  have hB := encWeight_le N v hv
  have hA0 : 0 ≤ (encWeight N u : ℝ) := by exact_mod_cast (Nat.zero_le _)
  have hB0 : 0 ≤ (encWeight N v : ℝ) := by exact_mod_cast (Nat.zero_le _)
  have huv' : u * v ≤ 1 / 4 := by
    have hsq : 0 ≤ (u - v) ^ 2 := sq_nonneg _
    nlinarith
  have hN0 : 0 ≤ (N : ℝ) ^ 2 := sq_nonneg _
  have h1 : (encWeight N u : ℝ) * (encWeight N v : ℝ)
      ≤ ((N : ℝ) * u) * (encWeight N v : ℝ) :=
    mul_le_mul_of_nonneg_right hA hB0
  have h2 : ((N : ℝ) * u) * (encWeight N v : ℝ) ≤ ((N : ℝ) * u) * ((N : ℝ) * v) :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have h3 : ((N : ℝ) * u) * ((N : ℝ) * v) = (N : ℝ) ^ 2 * (u * v) := by ring
  have h4 : (N : ℝ) ^ 2 * (u * v) ≤ (N : ℝ) ^ 2 / 4 := by
    calc
      (N : ℝ) ^ 2 * (u * v) = (u * v) * (N : ℝ) ^ 2 := by ring
      _ ≤ (1 / 4) * (N : ℝ) ^ 2 := mul_le_mul_of_nonneg_right huv' hN0
      _ = (N : ℝ) ^ 2 / 4 := by ring
  rw [encExpectedBits, ENNReal.toReal_mul]
  exact h1.trans (h2.trans (h3 ▸ h4))

/-- For complementary nonnegative targets and `N ≥ 3`, the truncated encoded left probability
differs from `v` by at most the reciprocal total encoded weight plus pending probability. -/
theorem encTruncation_error (N : ℕ) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1)
    (hN : 3 ≤ N) (n : ℕ) :
    |leftEventProb n (encWeight N u) (encWeight N v) - v|
      ≤ 1 / ((encWeight N u + encWeight N v : ℕ) : ℝ) +
        pendingProb n (encWeight N u) (encWeight N v) := by
  have hA2 : (N : ℝ) * u < (encWeight N u : ℝ) + 1 := encWeight_gt N u
  have hB2 : (N : ℝ) * v < (encWeight N v : ℝ) + 1 := encWeight_gt N v
  have hsum : 0 < (encWeight N u : ℝ) + (encWeight N v : ℝ) := by
    have hA3 : (N : ℝ) * u - 1 < (encWeight N u : ℝ) := by linarith
    have hB3 : (N : ℝ) * v - 1 < (encWeight N v : ℝ) := by linarith
    have h1 : ((N : ℝ) * u + (N : ℝ) * v : ℝ) - 2 <
        (encWeight N u : ℝ) + (encWeight N v : ℝ) := by linarith
    have h2 : (N : ℝ) * u + (N : ℝ) * v = (N : ℝ) * (u + v) := by ring
    rw [h2] at h1
    have h3 : (N : ℝ) * (u + v) = (N : ℝ) := by rw [huv]; norm_num
    rw [h3] at h1
    have h4 : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h5 : (0 : ℝ) < (N : ℝ) - 2 := by linarith
    linarith
  have hab : 0 < encWeight N u + encWeight N v := by exact_mod_cast hsum
  have hLle := leftEventProb_le n (encWeight N u) (encWeight N v) hab
  have hdef := leftEventProb_deficit n (encWeight N u) (encWeight N v) hab
  have herr := encLeftProb_error N u v hu hv huv hN
  have hl := leftProb_eq (encWeight N u) (encWeight N v) hab
  have hcast : (encWeight N v : ℝ) / ((encWeight N u + encWeight N v : ℕ) : ℝ) =
      (encWeight N v : ℝ) / ((encWeight N u : ℝ) + (encWeight N v : ℝ)) := by
    rw [natCast_add]
  have hE1 : |(encWeight N v : ℝ) / ((encWeight N u + encWeight N v : ℕ) : ℝ) - v|
      ≤ 1 / ((encWeight N u + encWeight N v : ℕ) : ℝ) := by
    rw [hl, ← hcast] at herr
    exact herr
  have hP : |leftEventProb n (encWeight N u) (encWeight N v) -
      (encWeight N v : ℝ) / ((encWeight N u + encWeight N v : ℕ) : ℝ)|
      ≤ pendingProb n (encWeight N u) (encWeight N v) := by
    rw [abs_le]
    constructor <;> linarith
  calc
    |leftEventProb n (encWeight N u) (encWeight N v) - v|
        ≤ |leftEventProb n (encWeight N u) (encWeight N v) -
            (encWeight N v : ℝ) / ((encWeight N u + encWeight N v : ℕ) : ℝ)| +
          |(encWeight N v : ℝ) / ((encWeight N u + encWeight N v : ℕ) : ℝ) - v| :=
          abs_sub_le _ _ _
    _ ≤ pendingProb n (encWeight N u) (encWeight N v) +
          1 / ((encWeight N u + encWeight N v : ℕ) : ℝ) := by
          have h := hP
          have h2 := hE1
          linarith
    _ = 1 / ((encWeight N u + encWeight N v : ℕ) : ℝ) +
          pendingProb n (encWeight N u) (encWeight N v) := by ring

/-- A state-dependent tree with positive leaf weights at `s` has positive total weight at `s`. -/
theorem stateTotalWeight_pos {S : Type} (t : StateBucketTree S) (s : S)
    (hw : PositiveStateTree t s) : 0 < stateTotalWeight t s := by
  induction t with
  | leaf w =>
      simp only [stateTotalWeight]
      exact hw
  | node l r ihl ihr =>
      simp only [stateTotalWeight]
      have h1 := ihl hw.1
      have h2 := ihr hw.2
      omega

/-- For positive weights, the fraction `WL / (WL + WR)` equals the race's `rightProb`. -/
theorem stateBranchMass (WL WR : ℕ) (hWL : 0 < WL) (hWR : 0 < WR) :
    (WL : ℝ) / ((WL + WR : ℕ) : ℝ) = rightProb WL WR := by
  rw [rightProb_eq WL WR (by omega)]
  rw [natCast_add]

/-- For a valid path in a state-dependent tree positive at `s`, the leaf mass is its
state-dependent weight divided by the total state-dependent weight. -/
theorem stateLeafMass_eq {S : Type} (t : StateBucketTree S) (s : S) (p : List Bool)
    (hpath : stateIsPath t p)
    (hw : PositiveStateTree t s) :
    stateLeafMass t s p = (stateLeafWeight t s p : ℝ) / (stateTotalWeight t s : ℝ) := by
  induction t generalizing p with
  | leaf w =>
      cases p with
      | nil =>
          have hne : (w s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hw)
          simp [stateLeafMass, stateLeafWeight, stateTotalWeight, hne]
      | cons b bs => simp [stateIsPath] at hpath
  | node l r ihl ihr =>
      have hWL : 0 < stateTotalWeight l s := stateTotalWeight_pos l s hw.1
      have hWR : 0 < stateTotalWeight r s := stateTotalWeight_pos r s hw.2
      have hneL : (stateTotalWeight l s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hWL)
      have hneR : (stateTotalWeight r s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hWR)
      have hneS : ((stateTotalWeight l s + stateTotalWeight r s : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (by omega))
      cases p with
      | nil => simp [stateIsPath] at hpath
      | cons b bs =>
          cases b with
          | true =>
              have hchild : stateIsPath l bs := by simpa [stateIsPath] using! hpath
              have hm := ihl bs hchild hw.1
              rw [stateLeafMass, hm, stateLeafWeight, stateTotalWeight]
              field_simp
          | false =>
              have hchild : stateIsPath r bs := by simpa [stateIsPath] using! hpath
              have hm := ihr bs hchild hw.2
              rw [stateLeafMass, hm, stateLeafWeight, stateTotalWeight]
              field_simp

/-- At a fixed state, the nodewise tree bit ledger equals the reach weight times the recursive
tree bit cost. -/
theorem stateTreeBitsByNodes_eq {S : Type} (t : StateBucketTree S) (s : S) (reach : ℝ) :
    stateTreeBitsByNodes t s reach = reach * stateTreeBits t s := by
  induction t generalizing reach with
  | leaf _ =>
      simp [stateTreeBitsByNodes, stateTreeBits]
  | node l r ihl ihr =>
      rw [stateTreeBitsByNodes, stateTreeBits, ihl, ihr]
      ring

/-- At a fixed state, the recursive tree bit cost equals the nodewise bit ledger at unit reach. -/
theorem stateTreeBits_eq_nodes {S : Type} (t : StateBucketTree S) (s : S) :
    stateTreeBits t s = stateTreeBitsByNodes t s 1 := by
  rw [stateTreeBitsByNodes_eq]
  ring

/-- The expected bit cost at state `s` is the product of the two weights at that state. -/
theorem stateExpectedBits {S : Type} (a b : S → ℕ) (s : S) :
    expectedBits (a s) (b s) = ((a s : ℝ≥0∞) * b s) := by
  exact expectedBits_eq (a s) (b s)

/-- When both weights at `s` are positive, expected input steps equal their product plus the
first weight plus two. -/
theorem stateExpectedInputSteps {S : Type} (a b : S → ℕ) (s : S) (hA : 0 < a s) (hB : 0 < b s) :
    expectedInputSteps (a s) (b s) = ((a s : ℝ≥0∞) * b s) + (a s : ℝ≥0∞) + 2 := by
  exact expectedInputSteps_eq (a s) (b s) hA hB

/-- When total weight at `s` is at least two, pending probability at fuel `n + 1` is bounded by
the product of the state weights times their decay factor to the power `n`. -/
theorem stateTail {S : Type} (a b : S → ℕ) (s : S) (n : ℕ) (hN : 2 ≤ a s + b s) :
    pendingProb (n + 1) (a s) (b s) ≤ ((a s : ℝ) * (b s : ℝ)) * decayReal (a s) (b s) ^ n := by
  exact tail_bound n (a s) (b s) hN

/-- At a state with positive total weight, the finite left-event probability differs from the
completed mass times its ideal left probability by at most pending probability. -/
theorem stateTruncationBias {S : Type} (a b : S → ℕ) (s : S) (n : ℕ) (hN : 0 < a s + b s) :
    |leftEventProb n (a s) (b s) - (1 - pendingProb n (a s) (b s)) *
        ((b s : ℝ) / ((a s : ℝ) + (b s : ℝ)))| ≤ pendingProb n (a s) (b s) := by
  exact truncation_bias_left n (a s) (b s) hN

/-- A collection of state-dependent selection probabilities, label masses, leaf mass and
bit-cost identities, and pending-tail bounds. -/
structure StateSelectionLaws where

  weighted : ∀ (S : Type) (a b : S → ℕ) (s : S), 0 < a s + b s →
    leftProb (a s) (b s) = (b s : ℝ) / ((a s : ℝ) + (b s : ℝ))

  label_true : ∀ a b, 0 < a + b → stateLabelMass a b true = (b : ℝ) / ((a : ℝ) + (b : ℝ))

  label_false : ∀ a b, 0 < a + b → stateLabelMass a b false = (a : ℝ) / ((a : ℝ) + (b : ℝ))

  state_leaf_mass : ∀ (S : Type) (t : StateBucketTree S) (s : S) (p : List Bool),
    PositiveStateTree t s → stateIsPath t p →
    stateLeafMass t s p = (stateLeafWeight t s p : ℝ) / (stateTotalWeight t s : ℝ)

  state_bits : ∀ (S : Type) (t : StateBucketTree S) (s : S),
    stateTreeBits t s = stateTreeBitsByNodes t s 1

  state_cost : ∀ (S : Type) (a b : S → ℕ) (s : S),
    expectedBits (a s) (b s) = ((a s : ℝ≥0∞) * b s)

  state_tail : ∀ (S : Type) (a b : S → ℕ) (s : S) (n : ℕ), 2 ≤ a s + b s →
    pendingProb (n + 1) (a s) (b s) ≤ ((a s : ℝ) * (b s : ℝ)) * decayReal (a s) (b s) ^ n

/-- Establishes the probability, leaf mass, cost, and tail identities packaged in
`StateSelectionLaws`. -/
theorem clause23_state_selection : StateSelectionLaws := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S a b s h
    exact stateWeighted_leftProb S a b s h
  · intro a b h
    exact stateLabelMass_true a b h
  · intro a b h
    exact stateLabelMass_false a b h
  · intro S t s p hw hpath
    exact stateLeafMass_eq t s p hpath hw
  · intro S t s
    exact stateTreeBits_eq_nodes t s
  · intro S a b s
    exact stateExpectedBits a b s
  · intro S a b s n hN
    exact stateTail a b s n hN

/-- For positive input weights, the left-event mass after `A + 1 + n` steps equals the loaded
sampler's left-event mass after `n` steps. -/
theorem inputLeftEvent_eq (n A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    inputLeftEvent (A + 1 + n) A B = leftEvent n A B := by
  obtain ⟨hc, hb, hs⟩ := loader_run A B hA hB
  have hstop := loader_run_fuel A B hA hB
  unfold inputLeftEvent leftEvent
  rw [show A + 1 + n = (A + 1) + n by omega, NativeTape.law_add]
  rw [NativeTape.law_eq_pure_of_run_nil Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A + 1) (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)
    (by simp [hstop])]
  rw [CostedLaw.expectation_bind, CostedLaw.expectation_pure]
  have hcont : NativeTape.continueLaw Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n
      (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A + 1) [] (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)) =
      (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded A B)).map
        (NativeTape.Result.appendTrace
          (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A + 1) [] (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)).trace) := by
    simp [NativeTape.continueLaw, hstop, hc]
  rw [hcont, CostedLaw.expectation_map]
  have hind : ∀ r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control,
      leftIndicator (NativeTape.Result.appendTrace
        (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A + 1) [] (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)).trace r) =
        leftIndicator r := by
    intro r
    have hout : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output (NativeTape.Result.appendTrace
        (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A + 1) [] (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)).trace r) =
        Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r := by
      simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output,
          NativeTape.Result.appendTrace]
    have ho : RaceOutcome.of (NativeTape.Result.appendTrace
        (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A + 1) [] (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)).trace r) =
        RaceOutcome.of r := by
      simp [RaceOutcome.of, hout]
    simp only [leftIndicator]
    rw [ho]
  rw [show (fun r => leftIndicator (NativeTape.Result.appendTrace
      (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A + 1) [] (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)).trace r)) =
      leftIndicator from funext hind]

/-- For positive input weights, the right-event mass after `A + 1 + n` steps equals the loaded
sampler's right-event mass after `n` steps. -/
theorem inputRightEvent_eq (n A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    inputRightEvent (A + 1 + n) A B = rightEvent n A B := by
  obtain ⟨hc, hb, hs⟩ := loader_run A B hA hB
  have hstop := loader_run_fuel A B hA hB
  unfold inputRightEvent rightEvent
  rw [show A + 1 + n = (A + 1) + n by omega, NativeTape.law_add]
  rw [NativeTape.law_eq_pure_of_run_nil Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A + 1) (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)
    (by simp [hstop])]
  rw [CostedLaw.expectation_bind, CostedLaw.expectation_pure]
  have hcont : NativeTape.continueLaw Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n
      (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A + 1) [] (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)) =
      (NativeTape.law Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program n (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.loaded A B)).map
        (NativeTape.Result.appendTrace
          (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A + 1) [] (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)).trace) := by
    simp [NativeTape.continueLaw, hstop, hc]
  rw [hcont, CostedLaw.expectation_map]
  have hind : ∀ r : NativeTape.Result Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Symbol Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.Control,
      rightIndicator (NativeTape.Result.appendTrace
        (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A + 1) [] (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)).trace r) =
        rightIndicator r := by
    intro r
    have hout : Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output (NativeTape.Result.appendTrace
        (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A + 1) [] (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)).trace r) =
        Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output r := by
      simp [Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.output,
          NativeTape.Result.appendTrace]
    have ho : RaceOutcome.of (NativeTape.Result.appendTrace
        (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A + 1) [] (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)).trace r) =
        RaceOutcome.of r := by
      simp [RaceOutcome.of, hout]
    simp only [rightIndicator]
    rw [ho]
  rw [show (fun r => rightIndicator (NativeTape.Result.appendTrace
      (NativeTape.run Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.program (A + 1) [] (Qatlib.Concepts.AdversaryBounds.AdvDuality.RandomBitsNativeDefs.input A B)).trace r)) =
      rightIndicator from funext hind]

/-- For positive input weights, removing the loader's `A + 1` steps preserves the real
left-event probability. -/
theorem inputLeftEventProb_eq (n A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    inputLeftEventProb (A + 1 + n) A B = leftEventProb n A B := by
  have h := inputLeftEvent_eq n A B hA hB
  unfold inputLeftEventProb leftEventProb
  rw [h]

/-- For positive input weights, removing the loader's `A + 1` steps preserves the real
right-event probability. -/
theorem inputRightEventProb_eq (n A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    inputRightEventProb (A + 1 + n) A B = rightEventProb n A B := by
  have h := inputRightEvent_eq n A B hA hB
  unfold inputRightEventProb rightEventProb
  rw [h]

/-- For positive node weights, `nodeLaw` identifies left routing with the loaded right event,
right routing with the loaded left event, and pending mass with `pendingProb`. -/
theorem nodeLaw_eq_loaded (n WL WR : ℕ) (hWL : 0 < WL) (hWR : 0 < WR) :
    (nodeLaw n WL WR).toLeft = rightEventProb n WL WR ∧
    (nodeLaw n WL WR).toRight = leftEventProb n WL WR ∧
    (nodeLaw n WL WR).pending = pendingProb n WL WR := by
  have h1 := inputRightEventProb_eq n WL WR hWL hWR
  have h2 := inputLeftEventProb_eq n WL WR hWL hWR
  have h3 := pendingInputProb_eq n WL WR hWL hWR
  simp only [nodeLaw]
  rw [h1, h2, h3]
  exact ⟨rfl, rfl, rfl⟩

/-- For positive node weights, the truncated left-routing probability is at most `WL / (WL +
WR)`. -/
theorem nodeLaw_toLeft_le (n WL WR : ℕ) (hWL : 0 < WL) (hWR : 0 < WR) :
    (nodeLaw n WL WR).toLeft ≤ (WL : ℝ) / ((WL + WR : ℕ) : ℝ) := by
  obtain ⟨h1, _, _⟩ := nodeLaw_eq_loaded n WL WR hWL hWR
  rw [h1]
  exact rightEventProb_le n WL WR (by omega)

/-- For positive node weights, the truncated right-routing probability is at most `WR / (WL +
WR)`. -/
theorem nodeLaw_toRight_le (n WL WR : ℕ) (hWL : 0 < WL) (hWR : 0 < WR) :
    (nodeLaw n WL WR).toRight ≤ (WR : ℝ) / ((WL + WR : ℕ) : ℝ) := by
  obtain ⟨_, h2, _⟩ := nodeLaw_eq_loaded n WL WR hWL hWR
  rw [h2]
  exact leftEventProb_le n WL WR (by omega)

/-- The left-routing probability in `nodeLaw` is nonnegative. -/
theorem nodeLaw_toLeft_nonneg (n WL WR : ℕ) :
    0 ≤ (nodeLaw n WL WR).toLeft := by
  unfold nodeLaw
  exact ENNReal.toReal_nonneg

/-- The right-routing probability in `nodeLaw` is nonnegative. -/
theorem nodeLaw_toRight_nonneg (n WL WR : ℕ) :
    0 ≤ (nodeLaw n WL WR).toRight := by
  unfold nodeLaw
  exact ENNReal.toReal_nonneg

/-- The pending probability in `nodeLaw` is nonnegative. -/
theorem nodeLaw_pending_nonneg (n WL WR : ℕ) :
    0 ≤ (nodeLaw n WL WR).pending := by
  unfold nodeLaw
  exact ENNReal.toReal_nonneg

/-- For positive node weights, the left-routing, right-routing, and pending probabilities in
`nodeLaw` sum to one. -/
theorem nodeLaw_sum_eq_one (n WL WR : ℕ) (hWL : 0 < WL) (hWR : 0 < WR) :
    (nodeLaw n WL WR).toLeft + (nodeLaw n WL WR).toRight + (nodeLaw n WL WR).pending = 1 := by
  obtain ⟨h1, h2, h3⟩ := nodeLaw_eq_loaded n WL WR hWL hWR
  rw [h1, h2, h3]
  simpa [add_comm] using! event_partition_real n WL WR (by omega)

/-- For positive node weights, the pending probability is one minus the two routing
probabilities. -/
theorem nodeLaw_pending_eq (n WL WR : ℕ) (hWL : 0 < WL) (hWR : 0 < WR) :
    (nodeLaw n WL WR).pending =
      1 - (nodeLaw n WL WR).toLeft - (nodeLaw n WL WR).toRight := by
  obtain ⟨h1, h2, h3⟩ := nodeLaw_eq_loaded n WL WR hWL hWR
  rw [h1, h2, h3]
  linarith [event_partition_real n WL WR (by omega)]

/-- For two positive subtree weights, their fractions of the combined weight sum to one. -/
theorem branchMass_sum_eq_one (l r : BucketTree) (hWL : 0 < totalWeight l)
    (hWR : 0 < totalWeight r) :
    (totalWeight l : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) +
      (totalWeight r : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) = 1 := by
  have hcast : ((totalWeight l + totalWeight r : ℕ) : ℝ) =
      (totalWeight l : ℝ) + (totalWeight r : ℝ) := by
    push_cast
    ring
  rw [hcast]
  have hne : (totalWeight l : ℝ) + (totalWeight r : ℝ) ≠ 0 := by positivity
  field_simp

/-- The truncated success probability of a positive tree is at most one. -/
theorem treeSuccessProb_le_one (n : ℕ) (t : BucketTree) (hpos : PositiveTree t) :
    treeSuccessProb n t ≤ 1 := by
  induction t with
  | leaf w =>
      simp [treeSuccessProb]
  | node l r ihl ihr =>
      have hWL : 0 < totalWeight l := positiveTree_weight l hpos.1
      have hWR : 0 < totalWeight r := positiveTree_weight r hpos.2
      have hL := nodeLaw_toLeft_le n (totalWeight l) (totalWeight r) hWL hWR
      have hR := nodeLaw_toRight_le n (totalWeight l) (totalWeight r) hWL hWR
      have hL0 := nodeLaw_toLeft_nonneg n (totalWeight l) (totalWeight r)
      have hR0 := nodeLaw_toRight_nonneg n (totalWeight l) (totalWeight r)
      have h1 := ihl hpos.1
      have h2 := ihr hpos.2
      rw [treeSuccessProb]
      calc
        (nodeLaw n (totalWeight l) (totalWeight r)).toLeft * treeSuccessProb n l +
              (nodeLaw n (totalWeight l) (totalWeight r)).toRight * treeSuccessProb n r
            ≤ (nodeLaw n (totalWeight l) (totalWeight r)).toLeft * 1 +
                (nodeLaw n (totalWeight l) (totalWeight r)).toRight * 1 := by
                  have h1' : (nodeLaw n (totalWeight l) (totalWeight r)).toLeft *
                        treeSuccessProb n l
                      ≤ (nodeLaw n (totalWeight l) (totalWeight r)).toLeft * 1 := by
                    calc
                      (nodeLaw n (totalWeight l) (totalWeight r)).toLeft * treeSuccessProb n l
                          = treeSuccessProb n l *
                              (nodeLaw n (totalWeight l) (totalWeight r)).toLeft := by ring
                      _ ≤ 1 * (nodeLaw n (totalWeight l) (totalWeight r)).toLeft :=
                        mul_le_mul_of_nonneg_right h1 hL0
                      _ = (nodeLaw n (totalWeight l) (totalWeight r)).toLeft * 1 := by ring
                  have h2' : (nodeLaw n (totalWeight l) (totalWeight r)).toRight *
                        treeSuccessProb n r
                      ≤ (nodeLaw n (totalWeight l) (totalWeight r)).toRight * 1 := by
                    calc
                      (nodeLaw n (totalWeight l) (totalWeight r)).toRight * treeSuccessProb n r
                          = treeSuccessProb n r *
                              (nodeLaw n (totalWeight l) (totalWeight r)).toRight := by ring
                      _ ≤ 1 * (nodeLaw n (totalWeight l) (totalWeight r)).toRight :=
                        mul_le_mul_of_nonneg_right h2 hR0
                      _ = (nodeLaw n (totalWeight l) (totalWeight r)).toRight * 1 := by ring
                  exact add_le_add h1' h2'
        _ = (nodeLaw n (totalWeight l) (totalWeight r)).toLeft +
              (nodeLaw n (totalWeight l) (totalWeight r)).toRight := by ring
        _ ≤ (totalWeight l : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) +
              (totalWeight r : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) :=
              add_le_add hL hR
        _ = 1 := branchMass_sum_eq_one l r hWL hWR

/-- The truncated pending probability of a positive tree is nonnegative. -/
theorem treePendingProb_nonneg (n : ℕ) (t : BucketTree) (hpos : PositiveTree t) :
    0 ≤ treePendingProb n t := by
  have h := treeSuccessProb_le_one n t hpos
  unfold treePendingProb
  linarith

/-- At an internal node, truncated success probability is the sum of each routing probability
times the corresponding subtree success probability. -/
theorem treeSuccessProb_succ (n : ℕ) (l r : BucketTree) :
    treeSuccessProb n (.node l r) =
      (nodeLaw n (totalWeight l) (totalWeight r)).toLeft * treeSuccessProb n l +
        (nodeLaw n (totalWeight l) (totalWeight r)).toRight * treeSuccessProb n r := rfl

/-- For a positive internal node, tree pending probability is its own pending probability plus
each routing probability times the corresponding subtree pending probability. -/
theorem treePendingProb_succ (n : ℕ) (l r : BucketTree) (hpos : PositiveTree (.node l r)) :
    treePendingProb n (.node l r) =
      (nodeLaw n (totalWeight l) (totalWeight r)).pending +
        (nodeLaw n (totalWeight l) (totalWeight r)).toLeft * treePendingProb n l +
        (nodeLaw n (totalWeight l) (totalWeight r)).toRight * treePendingProb n r := by
  have hWL : 0 < totalWeight l := positiveTree_weight l hpos.1
  have hWR : 0 < totalWeight r := positiveTree_weight r hpos.2
  have hsum := nodeLaw_sum_eq_one n (totalWeight l) (totalWeight r) hWL hWR
  have hsucc := treeSuccessProb_succ n l r
  unfold treePendingProb
  rw [hsucc]
  linarith

/-- Every truncated tree leaf mass is nonnegative. -/
theorem treeLeafMassTrunc_nonneg (n : ℕ) : ∀ (t : BucketTree) (p : List Bool),
    0 ≤ treeLeafMassTrunc n t p := by
  intro t
  induction t with
  | leaf w =>
      intro p
      cases p with
      | nil => simp [treeLeafMassTrunc]
      | cons b bs => simp [treeLeafMassTrunc]
  | node l r ihl ihr =>
      intro p
      cases p with
      | nil => simp [treeLeafMassTrunc]
      | cons b bs =>
          cases b with
          | true =>
              rw [treeLeafMassTrunc]
              exact mul_nonneg (nodeLaw_toLeft_nonneg n (totalWeight l) (totalWeight r))
                (ihl bs)
          | false =>
              rw [treeLeafMassTrunc]
              exact mul_nonneg (nodeLaw_toRight_nonneg n (totalWeight l) (totalWeight r))
                (ihr bs)

/-- Every tree leaf mass is nonnegative. -/
theorem leafMass_nonneg : ∀ (t : BucketTree) (p : List Bool), 0 ≤ leafMass t p := by
  intro t
  induction t with
  | leaf w =>
      intro p
      simp [leafMass]
  | node l r ihl ihr =>
      intro p
      cases p with
      | nil => simp [leafMass]
      | cons b bs =>
          cases b with
          | true =>
              rw [leafMass]
              exact mul_nonneg (by positivity) (ihl bs)
          | false =>
              rw [leafMass]
              exact mul_nonneg (by positivity) (ihr bs)

/-- For positive subtree weights, the left subtree's fraction of the combined weight is at most
one. -/
theorem branchMass_left_le_one (l r : BucketTree) (hWL : 0 < totalWeight l)
    (hWR : 0 < totalWeight r) :
    (totalWeight l : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) ≤ 1 := by
  have h := branchMass_sum_eq_one l r hWL hWR
  have h0 : 0 ≤ (totalWeight r : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) := by
    positivity
  linarith

/-- For positive subtree weights, the right subtree's fraction of the combined weight is at most
one. -/
theorem branchMass_right_le_one (l r : BucketTree) (hWL : 0 < totalWeight l)
    (hWR : 0 < totalWeight r) :
    (totalWeight r : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) ≤ 1 := by
  have h := branchMass_sum_eq_one l r hWL hWR
  have h0 : 0 ≤ (totalWeight l : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) := by
    positivity
  linarith

/-- The mass of a valid leaf path in a positive tree is at most one. -/
theorem leafMass_le_one (t : BucketTree) (p : List Bool) (hpath : isPath t p)
    (hpos : PositiveTree t) : leafMass t p ≤ 1 := by
  induction t generalizing p with
  | leaf w =>
      cases p with
      | nil => simp [leafMass]
      | cons b bs =>
          have hfalse : False := by simpa [isPath] using! hpath
          exact hfalse.elim
  | node l r ihl ihr =>
      have hWL : 0 < totalWeight l := positiveTree_weight l hpos.1
      have hWR : 0 < totalWeight r := positiveTree_weight r hpos.2
      cases p with
      | nil =>
          have hfalse : False := by simpa [isPath] using! hpath
          exact hfalse.elim
      | cons b bs =>
          cases b with
          | true =>
              have hchild : isPath l bs := by
                simp [isPath] at hpath
                exact hpath
              have hm := ihl bs hchild hpos.1
              have hfrac := branchMass_left_le_one l r hWL hWR
              rw [leafMass]
              calc
                (totalWeight l : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) * leafMass l bs
                    ≤ 1 * leafMass l bs :=
                      mul_le_mul_of_nonneg_right hfrac (leafMass_nonneg l bs)
                _ = leafMass l bs := by ring
                _ ≤ 1 := hm
          | false =>
              have hchild : isPath r bs := by
                simp [isPath] at hpath
                exact hpath
              have hm := ihr bs hchild hpos.2
              have hfrac := branchMass_right_le_one l r hWL hWR
              rw [leafMass]
              calc
                (totalWeight r : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) * leafMass r bs
                    ≤ 1 * leafMass r bs :=
                      mul_le_mul_of_nonneg_right hfrac (leafMass_nonneg r bs)
                _ = leafMass r bs := by ring
                _ ≤ 1 := hm

/-- For a valid path in a positive tree, truncated leaf mass is at most the ideal leaf mass. -/
theorem treeLeafMassTrunc_le (n : ℕ) (t : BucketTree) (p : List Bool)
    (hpath : isPath t p) (hpos : PositiveTree t) :
    treeLeafMassTrunc n t p ≤ leafMass t p := by
  induction t generalizing p with
  | leaf w =>
      cases p with
      | nil => simp [treeLeafMassTrunc, leafMass]
      | cons b bs =>
          have hfalse : False := by simpa [isPath] using! hpath
          exact hfalse.elim
  | node l r ihl ihr =>
      have hWL : 0 < totalWeight l := positiveTree_weight l hpos.1
      have hWR : 0 < totalWeight r := positiveTree_weight r hpos.2
      have hL := nodeLaw_toLeft_le n (totalWeight l) (totalWeight r) hWL hWR
      have hR := nodeLaw_toRight_le n (totalWeight l) (totalWeight r) hWL hWR
      have hL0 := nodeLaw_toLeft_nonneg n (totalWeight l) (totalWeight r)
      have hR0 := nodeLaw_toRight_nonneg n (totalWeight l) (totalWeight r)
      cases p with
      | nil =>
          have hfalse : False := by simpa [isPath] using! hpath
          exact hfalse.elim
      | cons b bs =>
          cases b with
          | true =>
              have hchild : isPath l bs := by
                simp [isPath] at hpath
                exact hpath
              have hm := ihl bs hchild hpos.1
              rw [treeLeafMassTrunc, leafMass]
              exact mul_le_mul hL hm (treeLeafMassTrunc_nonneg n l bs) (by positivity)
          | false =>
              have hchild : isPath r bs := by
                simp [isPath] at hpath
                exact hpath
              have hm := ihr bs hchild hpos.2
              rw [treeLeafMassTrunc, leafMass]
              exact mul_le_mul hR hm (treeLeafMassTrunc_nonneg n r bs) (by positivity)

/-- Under the stated routing, normalization, and nonnegativity bounds, `R * M - TL * T` is at
most the pending term plus the two weighted residual bounds. -/
theorem deficit_step (R L TL TR P pending M T P' : ℝ)
    (hTL : TL ≤ R) (hTR : TR ≤ L) (hfrac : R + L = 1) (hsum : TL + TR + pending = 1)
    (hTL0 : 0 ≤ TL) (hTR0 : 0 ≤ TR) (hP0 : 0 ≤ pending)
    (hdef : M - T ≤ P) (hM1 : M ≤ 1) (hM0 : 0 ≤ M) (hP'0 : 0 ≤ P') :
    R * M - TL * T ≤ pending + TL * P + TR * P' := by
  have hgap : R - TL ≤ pending := by
    have h1 : 0 ≤ L - TR := by linarith
    linarith
  have hgap0 : 0 ≤ R - TL := by linarith
  have h1 : TL * (M - T) ≤ TL * P := mul_le_mul_of_nonneg_left hdef hTL0
  have h2 : (R - TL) * M ≤ (R - TL) * 1 := by
    have h' : M * (R - TL) ≤ 1 * (R - TL) := mul_le_mul_of_nonneg_right hM1 hgap0
    calc
      (R - TL) * M = M * (R - TL) := by ring
      _ ≤ 1 * (R - TL) := h'
      _ = (R - TL) * 1 := by ring
  have h3 : (R - TL) * 1 ≤ pending := by
    calc
      (R - TL) * 1 = R - TL := by ring
      _ ≤ pending := hgap
  have h4 : 0 ≤ TR * P' := by positivity
  calc
    R * M - TL * T = TL * (M - T) + (R - TL) * M := by ring
    _ ≤ TL * P + (R - TL) * M := by exact add_le_add h1 (le_refl _)
    _ ≤ TL * P + (R - TL) * 1 := by exact add_le_add (le_refl _) h2
    _ ≤ TL * P + pending := by exact add_le_add_right h3 _
    _ ≤ pending + TL * P + TR * P' := by linarith

/-- For a valid path in a positive tree, the ideal leaf mass minus its truncated mass is at most
the tree pending probability. -/
theorem treeDeficit_le (n : ℕ) (t : BucketTree) (p : List Bool)
    (hpath : isPath t p) (hpos : PositiveTree t) :
    leafMass t p - treeLeafMassTrunc n t p ≤ treePendingProb n t := by
  induction t generalizing p with
  | leaf w =>
      cases p with
      | nil => simp [treeLeafMassTrunc, leafMass, treePendingProb, treeSuccessProb]
      | cons b bs =>
          have hfalse : False := by simpa [isPath] using! hpath
          exact hfalse.elim
  | node l r ihl ihr =>
      have hWL : 0 < totalWeight l := positiveTree_weight l hpos.1
      have hWR : 0 < totalWeight r := positiveTree_weight r hpos.2
      have hL := nodeLaw_toLeft_le n (totalWeight l) (totalWeight r) hWL hWR
      have hR := nodeLaw_toRight_le n (totalWeight l) (totalWeight r) hWL hWR
      have hL0 := nodeLaw_toLeft_nonneg n (totalWeight l) (totalWeight r)
      have hR0 := nodeLaw_toRight_nonneg n (totalWeight l) (totalWeight r)
      have hP0 := nodeLaw_pending_nonneg n (totalWeight l) (totalWeight r)
      have hsum := nodeLaw_sum_eq_one n (totalWeight l) (totalWeight r) hWL hWR
      have hfrac := branchMass_sum_eq_one l r hWL hWR
      have hsucc := treePendingProb_succ n l r ⟨hpos.1, hpos.2⟩
      cases p with
      | nil =>
          have hfalse : False := by simpa [isPath] using! hpath
          exact hfalse.elim
      | cons b bs =>
          cases b with
          | true =>
              have hchild : isPath l bs := by
                simp [isPath] at hpath
                exact hpath
              have hm := ihl bs hchild hpos.1
              have hM1 := leafMass_le_one l bs hchild hpos.1
              have hP'0 := treePendingProb_nonneg n r hpos.2
              rw [treeLeafMassTrunc, leafMass, hsucc]
              exact deficit_step
                ((totalWeight l : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ))
                ((totalWeight r : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ))
                (nodeLaw n (totalWeight l) (totalWeight r)).toLeft
                (nodeLaw n (totalWeight l) (totalWeight r)).toRight
                (treePendingProb n l) (nodeLaw n (totalWeight l) (totalWeight r)).pending
                (leafMass l bs) (treeLeafMassTrunc n l bs) (treePendingProb n r)
                hL hR hfrac hsum hL0 hR0 hP0 hm hM1 (leafMass_nonneg l bs) hP'0
          | false =>
              have hchild : isPath r bs := by
                simp [isPath] at hpath
                exact hpath
              have hm := ihr bs hchild hpos.2
              have hM1 := leafMass_le_one r bs hchild hpos.2
              have hP'0 := treePendingProb_nonneg n l hpos.1
              rw [treeLeafMassTrunc, leafMass, hsucc]
              simpa only [add_comm, add_left_comm, add_assoc] using!
                (deficit_step
                  ((totalWeight r : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ))
                  ((totalWeight l : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ))
                  (nodeLaw n (totalWeight l) (totalWeight r)).toRight
                  (nodeLaw n (totalWeight l) (totalWeight r)).toLeft
                  (treePendingProb n r) (nodeLaw n (totalWeight l) (totalWeight r)).pending
                  (leafMass r bs) (treeLeafMassTrunc n r bs) (treePendingProb n l)
                  hR hL (by rw [add_comm]; exact hfrac)
                    (by simpa only [add_comm, add_left_comm, add_assoc] using! hsum)
                    hR0 hL0 hP0 hm hM1
                  (leafMass_nonneg r bs) hP'0)

/-- For a valid path in a positive tree, truncated leaf mass differs from completed mass times
ideal leaf mass by at most the tree pending probability. -/
theorem treeTruncationBias (n : ℕ) (t : BucketTree) (p : List Bool)
    (hpath : isPath t p) (hpos : PositiveTree t) :
    |treeLeafMassTrunc n t p - (1 - treePendingProb n t) * leafMass t p|
      ≤ treePendingProb n t := by
  have hdef := treeDeficit_le n t p hpath hpos
  have hM1 := leafMass_le_one t p hpath hpos
  have hM0 := leafMass_nonneg t p
  have hT0 := treeLeafMassTrunc_nonneg n t p
  have hP0 := treePendingProb_nonneg n t hpos
  have hT1 := treeLeafMassTrunc_le n t p hpath hpos
  have hkey : treeLeafMassTrunc n t p - (1 - treePendingProb n t) * leafMass t p =
      treePendingProb n t * leafMass t p - (leafMass t p - treeLeafMassTrunc n t p) := by
    ring
  rw [hkey, abs_le]
  constructor <;> nlinarith

/-- The pending probability of a positive tree is at most its nodewise pending ledger at unit
reach. -/
theorem treePendingProb_le_nodes (n : ℕ) (t : BucketTree) (hpos : PositiveTree t) :
    treePendingProb n t ≤ treePendingByNodes n t 1 := by
  have key : ∀ (t : BucketTree) (reach : ℝ), PositiveTree t →
      reach * treePendingProb n t ≤ treePendingByNodes n t reach := by
    intro t
    induction t with
    | leaf w =>
        intro reach hpos
        simp [treePendingByNodes, treePendingProb, treeSuccessProb]
    | node l r ihl ihr =>
        intro reach hpos
        have hsucc := treePendingProb_succ n l r ⟨hpos.1, hpos.2⟩
        have h1 := ihl (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toLeft) hpos.1
        have h2 := ihr (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toRight) hpos.2
        calc
          reach * treePendingProb n (.node l r)
              = reach * (nodeLaw n (totalWeight l) (totalWeight r)).pending +
                  (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toLeft) *
                      treePendingProb n l +
                  (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toRight) *
                      treePendingProb n r := by rw [hsucc]; ring
          _ ≤ reach * (nodeLaw n (totalWeight l) (totalWeight r)).pending +
                treePendingByNodes n l
                  (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toLeft) +
                treePendingByNodes n r
                  (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toRight) := by
                    exact add_le_add
                      (add_le_add_right h1
                        (reach * (nodeLaw n (totalWeight l) (totalWeight r)).pending)) h2
          _ = treePendingByNodes n (.node l r) reach := rfl
  simpa using! key t 1 hpos

/-- The real pending probability of the two-weight sampler is at most one. -/
theorem pendingProb_le_one (n a b : ℕ) : pendingProb n a b ≤ 1 := by
  have hle := pendingMass_le_one n a b
  have h1 : pendingMass n a b ≠ ∞ := pendingMass_ne_top n a b
  have h' : (pendingMass n a b).toReal ≤ (1 : ℝ≥0∞).toReal :=
    (ENNReal.toReal_le_toReal h1 (by simp)).mpr hle
  simpa using! h'

/-- For positive total weight, increasing fuel by one cannot increase pending probability. -/
theorem pendingProb_mono_step (n a b : ℕ) (h : 0 < a + b) :
    pendingProb (n + 1) a b ≤ pendingProb n a b := by
  induction n generalizing a b with
  | zero =>
      have h1 := pendingProb_le_one 1 a b
      have h0 : pendingProb 0 a b = 1 := by
        simp only [pendingProb]
        rw [pendingMass_zero_budget a b h]
        simp
      linarith
  | succ n ih =>
      by_cases ha : a = 0
      · subst ha
        have h1 : pendingProb (n + 2) 0 b = 0 := by
          simp only [pendingProb]
          rw [pendingMass_left_endpoint (n + 2) b (by omega)]
          simp
        have h2 : pendingProb (n + 1) 0 b = 0 := by
          simp only [pendingProb]
          rw [pendingMass_left_endpoint (n + 1) b (by omega)]
          simp
        calc pendingProb (n + 2) 0 b = 0 := h1
          _ ≤ 0 := by linarith
          _ = pendingProb (n + 1) 0 b := h2.symm
      by_cases hb : b = 0
      · subst hb
        have h1 : pendingProb (n + 2) a 0 = 0 := by
          simp only [pendingProb]
          rw [pendingMass_right_endpoint (n + 2) a (by omega) (by omega)]
          simp
        have h2 : pendingProb (n + 1) a 0 = 0 := by
          simp only [pendingProb]
          rw [pendingMass_right_endpoint (n + 1) a (by omega) (by omega)]
          simp
        calc pendingProb (n + 2) a 0 = 0 := h1
          _ ≤ 0 := by linarith
          _ = pendingProb (n + 1) a 0 := h2.symm
      have ha' : 0 < a := Nat.pos_of_ne_zero ha
      have hb' : 0 < b := Nat.pos_of_ne_zero hb
      have hrec := pendingProb_succ (n + 1) a b ha' hb'
      have hrec' := pendingProb_succ n a b ha' hb'
      have h1 := ih (a - 1) (b + 1) (by omega)
      have h2 := ih (a + 1) (b - 1) (by omega)
      rw [hrec, hrec']
      linarith

/-- For positive total weight, pending probability is non-increasing as fuel grows. -/
theorem pendingProb_mono {n m a b : ℕ} (h : 0 < a + b) (hnm : n ≤ m) :
    pendingProb m a b ≤ pendingProb n a b := by
  refine Nat.le_induction (m := n)
      (P := fun k _ => pendingProb k a b ≤ pendingProb n a b) ?_ ?_ m hnm
  · exact le_rfl
  · intro k _ ih
    exact (pendingProb_mono_step k a b h).trans ih

/-- Increasing a tree budget preserves `BudgetCovers`. -/
theorem budgetCovers_mono (count : ℕ) (delta : ℝ) (b b' : ℕ) (t : BucketTree)
    (h : b ≤ b') (hc : BudgetCovers count delta b t) : BudgetCovers count delta b' t := by
  induction t with
  | leaf w => trivial
  | node l r ihl ihr =>
      exact ⟨Nat.le_trans hc.1 h, ihl hc.2.1, ihr hc.2.2⟩

/-- The budget `treeTruncationBudgetWith count t delta` satisfies `BudgetCovers count delta` for
`t`. -/
theorem treeTruncationBudgetWith_covers (count : ℕ) (delta : ℝ) (t : BucketTree) :
    BudgetCovers count delta (treeTruncationBudgetWith count t delta) t := by
  induction t with
  | leaf w => trivial
  | node l r ihl ihr =>
      simp only [treeTruncationBudgetWith]
      refine ⟨Nat.le_max_left _ _, ?_, ?_⟩
      · exact budgetCovers_mono count delta (treeTruncationBudgetWith count l delta) _
          l (le_trans (Nat.le_max_left (treeTruncationBudgetWith count l delta)
              (treeTruncationBudgetWith count r delta))
            (Nat.le_max_right (nodeBudget count delta (totalWeight l) (totalWeight r))
              (max (treeTruncationBudgetWith count l delta)
                (treeTruncationBudgetWith count r delta)))) ihl
      · exact budgetCovers_mono count delta (treeTruncationBudgetWith count r delta) _
          r (le_trans (Nat.le_max_right (treeTruncationBudgetWith count l delta)
              (treeTruncationBudgetWith count r delta))
            (Nat.le_max_right (nodeBudget count delta (totalWeight l) (totalWeight r))
              (max (treeTruncationBudgetWith count l delta)
                (treeTruncationBudgetWith count r delta)))) ihr

/-- For a positive tree, positive tolerance, and positive count, a covering budget bounds each
node's pending probability by `delta / count`. -/
theorem nodePendingBound_of_covers (count : ℕ) (delta : ℝ) (hδ : 0 < delta)
    (hcount : 0 < count) (budget : ℕ) (t : BucketTree) (hpos : PositiveTree t)
    (hcov : BudgetCovers count delta budget t) :
    NodePendingBound budget (delta / (count : ℝ)) t := by
  induction t with
  | leaf w => trivial
  | node l r ihl ihr =>
      have hWL : 0 < totalWeight l := positiveTree_weight l hpos.1
      have hWR : 0 < totalWeight r := positiveTree_weight r hpos.2
      have heps : 0 < delta / (count : ℝ) := by
        positivity
      have hN : 2 ≤ totalWeight l + totalWeight r := by omega
      have hpend : (nodeLaw budget (totalWeight l) (totalWeight r)).pending ≤
          delta / (count : ℝ) := by
        obtain ⟨_, _, h3⟩ := nodeLaw_eq_loaded budget (totalWeight l) (totalWeight r) hWL hWR
        rw [h3]
        have hbudget : truncationBudget (totalWeight l) (totalWeight r) (delta / (count : ℝ)) + 1
            ≤ budget := by
          simpa [nodeBudget] using! hcov.1
        have hmono : pendingProb budget (totalWeight l) (totalWeight r) ≤
            pendingProb
              (truncationBudget (totalWeight l) (totalWeight r) (delta / (count : ℝ)) + 1)
              (totalWeight l) (totalWeight r) :=
          pendingProb_mono (h := by omega) hbudget
        have htrunc :=
            truncation_bound (totalWeight l) (totalWeight r) hN (delta / (count : ℝ)) heps
        exact hmono.trans htrunc
      refine ⟨hpend, ihl hpos.1 hcov.2.1, ihr hpos.2 hcov.2.2⟩

/-- With node pending probabilities bounded by nonnegative `eps` and nonnegative reach, the
nodewise pending ledger is at most reach times the internal-node count times `eps`. -/
theorem treePendingByNodes_le (n : ℕ) (t : BucketTree) (reach eps : ℝ)
    (hpos : PositiveTree t) (hb : NodePendingBound n eps t) (hreach : 0 ≤ reach)
    (heps : 0 ≤ eps) :
    treePendingByNodes n t reach ≤ reach * (treeInternalCount t : ℝ) * eps := by
  induction t generalizing reach with
  | leaf w =>
      simp [treePendingByNodes, treeInternalCount]
  | node l r ihl ihr =>
      have hWL : 0 < totalWeight l := positiveTree_weight l hpos.1
      have hWR : 0 < totalWeight r := positiveTree_weight r hpos.2
      have hL0 := nodeLaw_toLeft_nonneg n (totalWeight l) (totalWeight r)
      have hR0 := nodeLaw_toRight_nonneg n (totalWeight l) (totalWeight r)
      have htoL : (nodeLaw n (totalWeight l) (totalWeight r)).toLeft ≤ 1 :=
        (nodeLaw_toLeft_le n (totalWeight l) (totalWeight r) hWL hWR).trans
          (branchMass_left_le_one l r hWL hWR)
      have htoR : (nodeLaw n (totalWeight l) (totalWeight r)).toRight ≤ 1 :=
        (nodeLaw_toRight_le n (totalWeight l) (totalWeight r) hWL hWR).trans
          (branchMass_right_le_one l r hWL hWR)
      have h1 := ihl (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toLeft)
        hpos.1 hb.2.1 (mul_nonneg hreach hL0)
      have h2 := ihr (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toRight)
        hpos.2 hb.2.2 (mul_nonneg hreach hR0)
      rw [treePendingByNodes]
      calc
        reach * (nodeLaw n (totalWeight l) (totalWeight r)).pending +
              treePendingByNodes n l (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toLeft) +
              treePendingByNodes n r (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toRight)
            ≤ reach * eps +
                (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toLeft) *
                    (treeInternalCount l : ℝ) * eps +
                (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toRight) *
                    (treeInternalCount r : ℝ) * eps := by
                  have hA : reach * (nodeLaw n (totalWeight l) (totalWeight r)).pending ≤ reach * eps := by
                    have hn := hb.1
                    nlinarith
                  have hB : treePendingByNodes n l
                        (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toLeft)
                      ≤ (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toLeft) *
                          (treeInternalCount l : ℝ) * eps := h1
                  have hC : treePendingByNodes n r
                        (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toRight)
                      ≤ (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toRight) *
                          (treeInternalCount r : ℝ) * eps := h2
                  linarith
        _ ≤ reach * eps + reach * (treeInternalCount l : ℝ) * eps +
              reach * (treeInternalCount r : ℝ) * eps := by
                  have hstep1 : (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toLeft) *
                        (treeInternalCount l : ℝ) * eps ≤
                      reach * (treeInternalCount l : ℝ) * eps := by
                    calc (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toLeft) *
                            (treeInternalCount l : ℝ) * eps
                        = reach * ((nodeLaw n (totalWeight l) (totalWeight r)).toLeft *
                            ((treeInternalCount l : ℝ) * eps)) := by ring
                      _ ≤ reach * (1 * ((treeInternalCount l : ℝ) * eps)) := by
                        exact mul_le_mul_of_nonneg_left
                          (mul_le_mul_of_nonneg_right htoL (by positivity)) (by positivity)
                      _ = reach * (treeInternalCount l : ℝ) * eps := by ring
                  have hstep2 : (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toRight) *
                        (treeInternalCount r : ℝ) * eps ≤
                      reach * (treeInternalCount r : ℝ) * eps := by
                    calc (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toRight) *
                            (treeInternalCount r : ℝ) * eps
                        = reach * ((nodeLaw n (totalWeight l) (totalWeight r)).toRight *
                            ((treeInternalCount r : ℝ) * eps)) := by ring
                      _ ≤ reach * (1 * ((treeInternalCount r : ℝ) * eps)) := by
                        exact mul_le_mul_of_nonneg_left
                          (mul_le_mul_of_nonneg_right htoR (by positivity)) (by positivity)
                      _ = reach * (treeInternalCount r : ℝ) * eps := by ring
                  linarith
        _ = reach * (treeInternalCount (.node l r) : ℝ) * eps := by
          rw [treeInternalCount]
          push_cast
          ring

/-- For a positive tree and positive tolerance, the prescribed tree truncation budget leaves
pending probability at most that tolerance. -/
theorem treeTruncationBudget_bound (t : BucketTree) (delta : ℝ) (hpos : PositiveTree t)
    (hδ : 0 < delta) :
    treePendingProb (treeTruncationBudget t delta) t ≤ delta := by
  cases t with
  | leaf w =>
      simp [treePendingProb, treeSuccessProb]
      linarith
  | node l r =>
      have hcount : 0 < treeInternalCount (.node l r) := by
        simp [treeInternalCount]
      have hcov : BudgetCovers (treeInternalCount (.node l r)) delta
          (treeTruncationBudget (.node l r) delta) (.node l r) := by
        rw [treeTruncationBudget]
        exact treeTruncationBudgetWith_covers (treeInternalCount (.node l r)) delta (.node l r)
      have hbound := nodePendingBound_of_covers (treeInternalCount (.node l r)) delta hδ hcount
        (treeTruncationBudget (.node l r) delta) (.node l r) hpos hcov
      have hnodes :=
          treePendingProb_le_nodes (treeTruncationBudget (.node l r) delta) (.node l r) hpos
      have hledger := treePendingByNodes_le (treeTruncationBudget (.node l r) delta) (.node l r) 1
        (delta / (treeInternalCount (.node l r) : ℝ)) hpos hbound (by norm_num) (by positivity)
      have hcountne : (treeInternalCount (.node l r) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hcount)
      calc
        treePendingProb (treeTruncationBudget (.node l r) delta) (.node l r)
            ≤ treePendingByNodes (treeTruncationBudget (.node l r) delta) (.node l r) 1 := hnodes
        _ ≤ 1 * (treeInternalCount (.node l r) : ℝ) *
            (delta / (treeInternalCount (.node l r) : ℝ)) := hledger
        _ = delta := by field_simp

/-- The cost of every valid tree path is at most `treeWorstSteps`. -/
theorem treePathCost_le_worst (n : ℕ) (t : BucketTree) (p : List Bool) (hpath : isPath t p) :
    treePathCost n t p ≤ treeWorstSteps n t := by
  induction t generalizing p with
  | leaf w =>
      cases p with
      | nil => simp [treePathCost, treeWorstSteps]
      | cons b bs =>
          have hfalse : False := by
            simp only [isPath] at hpath
          exact hfalse.elim
  | node l r ihl ihr =>
      cases p with
      | nil =>
          have hfalse : False := by
            simp only [isPath] at hpath
          exact hfalse.elim
      | cons b bs =>
          cases b with
          | true =>
              have hsub : isPath l bs := by
                simp only [isPath] at hpath
                exact hpath
              have h1 := ihl bs hsub
              simp only [treePathCost, treeWorstSteps]
              have hmax : (totalWeight l : ℝ) + 1 + n + treeWorstSteps n l ≤
                  max ((totalWeight l : ℝ) + 1 + n + treeWorstSteps n l)
                    ((totalWeight l : ℝ) + 1 + n + treeWorstSteps n r) := by
                exact le_max_left _ _
              linarith
          | false =>
              have hsub : isPath r bs := by
                simp only [isPath] at hpath
                exact hpath
              have h1 := ihr bs hsub
              simp only [treePathCost, treeWorstSteps]
              have hmax : (totalWeight l : ℝ) + 1 + n + treeWorstSteps n r ≤
                  max ((totalWeight l : ℝ) + 1 + n + treeWorstSteps n l)
                    ((totalWeight l : ℝ) + 1 + n + treeWorstSteps n r) := by
                exact le_max_right _ _
              linarith

/-- There exists a valid tree path whose cost attains `treeWorstSteps`. -/
theorem treeWorstSteps_attained (n : ℕ) (t : BucketTree) :
    ∃ p, isPath t p ∧ treePathCost n t p = treeWorstSteps n t := by
  induction t with
  | leaf w =>
      refine ⟨[], by simp [isPath], by simp [treePathCost, treeWorstSteps]⟩
  | node l r ihl ihr =>
      obtain ⟨p_l, hpl, heql⟩ := ihl
      obtain ⟨p_r, hpr, heqr⟩ := ihr
      by_cases h : treeWorstSteps n l ≥ treeWorstSteps n r
      · refine ⟨true :: p_l, by simp [isPath, hpl], ?_⟩
        simp only [treePathCost, treeWorstSteps]
        rw [heql]
        have hle : (totalWeight l : ℝ) + 1 + n + treeWorstSteps n r ≤
            (totalWeight l : ℝ) + 1 + n + treeWorstSteps n l := by linarith
        exact max_eq_left hle |>.symm
      · refine ⟨false :: p_r, by simp [isPath, hpr], ?_⟩
        simp only [treePathCost, treeWorstSteps]
        rw [heqr]
        have hle : (totalWeight l : ℝ) + 1 + n + treeWorstSteps n l ≤
            (totalWeight l : ℝ) + 1 + n + treeWorstSteps n r := by linarith
        exact max_eq_right hle |>.symm

/-- The worst tree path cost is at most `treeDepth t * (totalWeight t + 1 + n)`, with the
factors viewed in ℝ. -/
theorem treeWorstSteps_le (n : ℕ) (t : BucketTree) :
    treeWorstSteps n t ≤ (treeDepth t : ℝ) * ((totalWeight t : ℝ) + 1 + n) := by
  induction t with
  | leaf w =>
      simp [treeWorstSteps, treeDepth, totalWeight]
  | node l r ihl ihr =>
      have hWL : (totalWeight l : ℝ) ≤ (totalWeight (.node l r) : ℝ) := by
        simp only [totalWeight]
        exact_mod_cast (show totalWeight l ≤ totalWeight l + totalWeight r by omega)
      have hWR : (totalWeight r : ℝ) ≤ (totalWeight (.node l r) : ℝ) := by
        simp only [totalWeight]
        exact_mod_cast (show totalWeight r ≤ totalWeight l + totalWeight r by omega)
      have h1 := ihl
      have h2 := ihr
      have h1' : treeWorstSteps n l ≤ (treeDepth l : ℝ) *
          ((totalWeight (.node l r) : ℝ) + 1 + n) := by
        calc treeWorstSteps n l ≤ (treeDepth l : ℝ) * ((totalWeight l : ℝ) + 1 + n) := h1
          _ ≤ (treeDepth l : ℝ) * ((totalWeight (.node l r) : ℝ) + 1 + n) := by
            exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h2' : treeWorstSteps n r ≤ (treeDepth r : ℝ) *
          ((totalWeight (.node l r) : ℝ) + 1 + n) := by
        calc treeWorstSteps n r ≤ (treeDepth r : ℝ) * ((totalWeight r : ℝ) + 1 + n) := h2
          _ ≤ (treeDepth r : ℝ) * ((totalWeight (.node l r) : ℝ) + 1 + n) := by
            exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have hXY : (totalWeight l : ℝ) + 1 + n ≤ (totalWeight (.node l r) : ℝ) + 1 + n := by
        linarith
      have hA : (totalWeight l : ℝ) + 1 + n + treeWorstSteps n l ≤
          (1 + (treeDepth l : ℝ)) * ((totalWeight (.node l r) : ℝ) + 1 + n) := by
        calc (totalWeight l : ℝ) + 1 + n + treeWorstSteps n l
              ≤ (totalWeight l : ℝ) + 1 + n + (treeDepth l : ℝ) *
                  ((totalWeight (.node l r) : ℝ) + 1 + n) := by
                exact add_le_add_right h1' _
            _ = ((totalWeight l : ℝ) + 1 + n) + (treeDepth l : ℝ) *
                  ((totalWeight (.node l r) : ℝ) + 1 + n) := by ring
            _ ≤ ((totalWeight (.node l r) : ℝ) + 1 + n) + (treeDepth l : ℝ) *
                  ((totalWeight (.node l r) : ℝ) + 1 + n) := by
                exact add_le_add_left hXY _
            _ = (1 + (treeDepth l : ℝ)) * ((totalWeight (.node l r) : ℝ) + 1 + n) := by ring
      have hB : (totalWeight l : ℝ) + 1 + n + treeWorstSteps n r ≤
          (1 + (treeDepth r : ℝ)) * ((totalWeight (.node l r) : ℝ) + 1 + n) := by
        calc (totalWeight l : ℝ) + 1 + n + treeWorstSteps n r
              ≤ (totalWeight l : ℝ) + 1 + n + (treeDepth r : ℝ) *
                  ((totalWeight (.node l r) : ℝ) + 1 + n) := by
                exact add_le_add_right h2' _
            _ ≤ ((totalWeight (.node l r) : ℝ) + 1 + n) + (treeDepth r : ℝ) *
                  ((totalWeight (.node l r) : ℝ) + 1 + n) := by
                exact add_le_add_left hXY _
            _ = (1 + (treeDepth r : ℝ)) * ((totalWeight (.node l r) : ℝ) + 1 + n) := by ring
      have hdl : 1 + (treeDepth l : ℝ) ≤ ((1 + max (treeDepth l) (treeDepth r) : ℕ) : ℝ) := by
        have h : (treeDepth l : ℝ) ≤ (max (treeDepth l) (treeDepth r) : ℝ) := by
          exact_mod_cast (Nat.le_max_left _ _)
        have h' : (1 + (treeDepth l : ℝ)) ≤ 1 + (max (treeDepth l) (treeDepth r) : ℝ) := by
          linarith
        have h'' : (1 + (max (treeDepth l) (treeDepth r) : ℝ)) =
            ((1 + max (treeDepth l) (treeDepth r) : ℕ) : ℝ) := by
          push_cast
          ring
        linarith
      have hdr : 1 + (treeDepth r : ℝ) ≤ ((1 + max (treeDepth l) (treeDepth r) : ℕ) : ℝ) := by
        have h : (treeDepth r : ℝ) ≤ (max (treeDepth l) (treeDepth r) : ℝ) := by
          exact_mod_cast (Nat.le_max_right _ _)
        have h' : (1 + (treeDepth r : ℝ)) ≤ 1 + (max (treeDepth l) (treeDepth r) : ℝ) := by
          linarith
        have h'' : (1 + (max (treeDepth l) (treeDepth r) : ℝ)) =
            ((1 + max (treeDepth l) (treeDepth r) : ℕ) : ℝ) := by
          push_cast
          ring
        linarith
      have hmulL : (1 + (treeDepth l : ℝ)) * ((totalWeight (.node l r) : ℝ) + 1 + n) ≤
          ((1 + max (treeDepth l) (treeDepth r) : ℕ) : ℝ) *
            ((totalWeight (.node l r) : ℝ) + 1 + n) :=
        mul_le_mul_of_nonneg_right hdl (by positivity)
      have hmulR : (1 + (treeDepth r : ℝ)) * ((totalWeight (.node l r) : ℝ) + 1 + n) ≤
          ((1 + max (treeDepth l) (treeDepth r) : ℕ) : ℝ) *
            ((totalWeight (.node l r) : ℝ) + 1 + n) :=
        mul_le_mul_of_nonneg_right hdr (by positivity)
      show max ((totalWeight l : ℝ) + 1 + n + treeWorstSteps n l)
          ((totalWeight l : ℝ) + 1 + n + treeWorstSteps n r) ≤
          ((1 + max (treeDepth l) (treeDepth r) : ℕ) : ℝ) *
            ((totalWeight (.node l r) : ℝ) + 1 + n)
      rw [max_le_iff]
      constructor
      · exact hA.trans hmulL
      · exact hB.trans hmulR

/-- For positive input weights, finite-fuel input pending mass is finite. -/
theorem pendingInputMass_ne_top (n A B : ℕ) (hA : 0 < A) (hB : 0 < B) :
    pendingInputMass n A B ≠ ∞ := by
  by_cases hle : n ≤ A + 1
  · rw [pendingInputMass_one n A B hle hA hB]
    simp
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = A + 1 + m := by
      have : A + 1 < n := by omega
      exact ⟨n - (A + 1), by omega⟩
    rw [pendingInputMass_eq m A B hA hB]
    exact pendingMass_ne_top m A B

/-- Truncated input step cost is at most unbounded expected input steps plus the fuel budget
times the pending mass. -/
theorem truncatedInputSteps_le (n A B : ℕ) :
    truncatedInputSteps n A B ≤ expectedInputSteps A B + (n : ℝ≥0∞) * pendingInputMass n A B := by
  have hsum : (∑ k ∈ Finset.range n, pendingInputMass k A B) ≤ expectedInputSteps A B :=
    ENNReal.sum_le_tsum (Finset.range n)
  calc truncatedInputSteps n A B
      = (∑ k ∈ Finset.range n, pendingInputMass k A B) + (n : ℝ≥0∞) * pendingInputMass n A B := rfl
    _ ≤ (∑' k, pendingInputMass k A B) + (n : ℝ≥0∞) * pendingInputMass n A B :=
      add_le_add_left hsum _
    _ = expectedInputSteps A B + (n : ℝ≥0∞) * pendingInputMass n A B := rfl

/-- For positive node weights, truncated node steps are at most `WL * WR + WL + 2` plus `(WL + 1
+ n)` times the node pending probability. -/
theorem nodeTruncSteps_le (n WL WR : ℕ) (hA : 0 < WL) (hB : 0 < WR) :
    nodeTruncSteps n WL WR ≤
      (WL : ℝ) * (WR : ℝ) + (WL : ℝ) + 2 +
        ((WL + 1 + n : ℕ) : ℝ) * (nodeLaw n WL WR).pending := by
  have hne : pendingInputMass (WL + 1 + n) WL WR ≠ ∞ :=
    pendingInputMass_ne_top (WL + 1 + n) WL WR hA hB
  have hfin : ∀ k ∈ Finset.range (WL + 1 + n), pendingInputMass k WL WR ≠ ∞ := by
    intro k hk
    exact pendingInputMass_ne_top k WL WR hA hB
  have hsumne : (∑ k ∈ Finset.range (WL + 1 + n), pendingInputMass k WL WR) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr hfin
  have hexpne : expectedInputSteps WL WR ≠ ∞ := by
    rw [expectedInputSteps_eq WL WR hA hB]
    refine ENNReal.add_ne_top.mpr ⟨?_, by simp⟩
    rw [ENNReal.add_ne_top]
    exact ⟨ENNReal.mul_ne_top (by simp) (by simp), by simp⟩
  have htruncne : truncatedInputSteps (WL + 1 + n) WL WR ≠ ∞ := by
    unfold truncatedInputSteps
    rw [ENNReal.add_ne_top]
    exact ⟨hsumne, ENNReal.mul_ne_top (by simp) hne⟩
  have hENN := truncatedInputSteps_le (WL + 1 + n) WL WR
  have hRne : expectedInputSteps WL WR +
      ((WL + 1 + n : ℕ) : ℝ≥0∞) * pendingInputMass (WL + 1 + n) WL WR ≠ ∞ := by
    rw [ENNReal.add_ne_top]
    exact ⟨hexpne, ENNReal.mul_ne_top (by simp) hne⟩
  have hconv : (truncatedInputSteps (WL + 1 + n) WL WR).toReal ≤
      (expectedInputSteps WL WR).toReal +
        (((WL + 1 + n : ℕ) : ℝ≥0∞) * pendingInputMass (WL + 1 + n) WL WR).toReal := by
    have h' := (ENNReal.toReal_le_toReal htruncne hRne).mpr hENN
    have hrhs : (expectedInputSteps WL WR +
        ((WL + 1 + n : ℕ) : ℝ≥0∞) * pendingInputMass (WL + 1 + n) WL WR).toReal =
        (expectedInputSteps WL WR).toReal +
          (((WL + 1 + n : ℕ) : ℝ≥0∞) * pendingInputMass (WL + 1 + n) WL WR).toReal :=
      ENNReal.toReal_add hexpne (ENNReal.mul_ne_top (by simp) hne)
    rw [hrhs] at h'
    exact h'
  have hval : (expectedInputSteps WL WR).toReal = (WL : ℝ) * (WR : ℝ) + (WL : ℝ) + 2 := by
    have hmul' : ((WL : ℝ≥0∞) * WR).toReal = (WL : ℝ) * (WR : ℝ) := by
      rw [ENNReal.toReal_mul]
      simp [ENNReal.toReal_natCast]
    have hA' : (WL : ℝ≥0∞).toReal = (WL : ℝ) := by
      simp [ENNReal.toReal_natCast]
    rw [expectedInputSteps_eq WL WR hA hB]
    have houter : (((WL : ℝ≥0∞) * WR) + (WL : ℝ≥0∞) + 2).toReal =
        (((WL : ℝ≥0∞) * WR) + (WL : ℝ≥0∞)).toReal + (2 : ℝ≥0∞).toReal := by
      exact ENNReal.toReal_add (by
        rw [ENNReal.add_ne_top]
        exact ⟨ENNReal.mul_ne_top (by simp) (by simp), by simp⟩) (by simp)
    rw [houter]
    have hinner : (((WL : ℝ≥0∞) * WR) + (WL : ℝ≥0∞)).toReal =
        ((WL : ℝ≥0∞) * WR).toReal + (WL : ℝ≥0∞).toReal := by
      exact ENNReal.toReal_add (ENNReal.mul_ne_top (by simp) (by simp)) (by simp)
    rw [hinner, hmul', hA']
    norm_num
  have hmul : (((WL + 1 + n : ℕ) : ℝ≥0∞) * pendingInputMass (WL + 1 + n) WL WR).toReal =
      ((WL + 1 + n : ℕ) : ℝ) * (pendingInputMass (WL + 1 + n) WL WR).toReal := by
    have h : (((WL + 1 + n : ℕ) : ℝ≥0∞) * pendingInputMass (WL + 1 + n) WL WR).toReal =
        ((WL + 1 + n : ℕ) : ℝ≥0∞).toReal * (pendingInputMass (WL + 1 + n) WL WR).toReal :=
      ENNReal.toReal_mul
    have h2 : ((WL + 1 + n : ℕ) : ℝ≥0∞).toReal = ((WL + 1 + n : ℕ) : ℝ) :=
      ENNReal.toReal_natCast (WL + 1 + n)
    rw [h, h2]
  have hprefix : (∑ k ∈ Finset.range (WL + 1 + n), pendingInputProb k WL WR) ≤
      (WL : ℝ) * (WR : ℝ) + (WL : ℝ) + 2 := by
    have hconv2 : (∑ k ∈ Finset.range (WL + 1 + n), pendingInputMass k WL WR).toReal =
        ∑ k ∈ Finset.range (WL + 1 + n), (pendingInputMass k WL WR).toReal :=
      ENNReal.toReal_sum hfin
    have hle : (∑ k ∈ Finset.range (WL + 1 + n), pendingInputMass k WL WR) ≤
        expectedInputSteps WL WR :=
      ENNReal.sum_le_tsum (Finset.range (WL + 1 + n))
    have hle' : (∑ k ∈ Finset.range (WL + 1 + n), (pendingInputMass k WL WR).toReal) ≤
        (expectedInputSteps WL WR).toReal := by
      rw [← hconv2]
      exact (ENNReal.toReal_le_toReal hsumne hexpne).mpr hle
    rw [hval] at hle'
    simpa only [pendingInputProb] using! hle'
  have htail : pendingInputProb (WL + 1 + n) WL WR = (nodeLaw n WL WR).pending := rfl
  calc nodeTruncSteps n WL WR
      = (∑ k ∈ Finset.range (WL + 1 + n), pendingInputProb k WL WR) +
          ((WL + 1 + n : ℕ) : ℝ) * pendingInputProb (WL + 1 + n) WL WR := rfl
    _ ≤ ((WL : ℝ) * (WR : ℝ) + (WL : ℝ) + 2) +
          ((WL + 1 + n : ℕ) : ℝ) * (nodeLaw n WL WR).pending := by
      rw [htail]
      linarith

/-- The recursive tree step cost is nonnegative. -/
theorem treeSteps_nonneg (t : BucketTree) : 0 ≤ treeSteps t := by
  induction t with
  | leaf w =>
      simp [treeSteps]
  | node l r ihl ihr =>
      have h1 : 0 ≤ (totalWeight l : ℝ) * (totalWeight r : ℝ) + (totalWeight l : ℕ) + 2 := by
        positivity
      have h2 : 0 ≤ (totalWeight l : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) :=
        div_nonneg (by positivity) (by positivity)
      have h3 : 0 ≤ (totalWeight r : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) :=
        div_nonneg (by positivity) (by positivity)
      have h4 : 0 ≤ (totalWeight l : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) * treeSteps l :=
        mul_nonneg h2 ihl
      have h5 : 0 ≤ (totalWeight r : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) * treeSteps r :=
        mul_nonneg h3 ihr
      simp only [treeSteps]
      linarith

/-- Scaling the reach parameter scales the tree truncation waste by the same factor. -/
theorem treeTruncWaste_scale (n : ℕ) (t : BucketTree) (c reach : ℝ) :
    treeTruncWaste n t (c * reach) = c * treeTruncWaste n t reach := by
  induction t generalizing c reach with
  | leaf w =>
      simp [treeTruncWaste]
  | node l r ihl ihr =>
      simp only [treeTruncWaste]
      have hL : treeTruncWaste n l
            (c * (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toLeft)) =
          c * treeTruncWaste n l (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toLeft) :=
        ihl c (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toLeft)
      have hR : treeTruncWaste n r
            (c * (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toRight)) =
          c * treeTruncWaste n r (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toRight) :=
        ihr c (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toRight)
      have e1 : c * reach * (nodeLaw n (totalWeight l) (totalWeight r)).toLeft =
          c * (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toLeft) := by ring
      have e2 : c * reach * (nodeLaw n (totalWeight l) (totalWeight r)).toRight =
          c * (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toRight) := by ring
      rw [e1, e2, hL, hR]
      ring

/-- For a positive tree, truncated expected steps are at most the unbounded tree step cost plus
truncation waste at unit reach. -/
theorem treeTruncSteps_le (n : ℕ) (t : BucketTree) (hpos : PositiveTree t) :
    treeTruncSteps n t ≤ treeSteps t + treeTruncWaste n t 1 := by
  induction t with
  | leaf w =>
      simp [treeTruncSteps, treeTruncWaste, treeSteps]
  | node l r ihl ihr =>
      have hWL : 0 < totalWeight l := positiveTree_weight l hpos.1
      have hWR : 0 < totalWeight r := positiveTree_weight r hpos.2
      have hnode0 := nodeTruncSteps_le n (totalWeight l) (totalWeight r) hWL hWR
      have hcast : ((totalWeight l + 1 + n : ℕ) : ℝ) = (totalWeight l : ℝ) + 1 + n := by
        push_cast
        ring
      have hnode := hnode0
      rw [hcast] at hnode
      have hL := nodeLaw_toLeft_le n (totalWeight l) (totalWeight r) hWL hWR
      have hR := nodeLaw_toRight_le n (totalWeight l) (totalWeight r) hWL hWR
      have hL0 := nodeLaw_toLeft_nonneg n (totalWeight l) (totalWeight r)
      have hR0 := nodeLaw_toRight_nonneg n (totalWeight l) (totalWeight r)
      have h1 := ihl hpos.1
      have h2 := ihr hpos.2
      have hsl := treeSteps_nonneg l
      have hsr := treeSteps_nonneg r
      have hscaleL : treeTruncWaste n l (1 * (nodeLaw n (totalWeight l) (totalWeight r)).toLeft) =
          (nodeLaw n (totalWeight l) (totalWeight r)).toLeft * treeTruncWaste n l 1 := by
        simpa using! treeTruncWaste_scale n l
          (nodeLaw n (totalWeight l) (totalWeight r)).toLeft 1
      have hscaleR : treeTruncWaste n r (1 * (nodeLaw n (totalWeight l) (totalWeight r)).toRight) =
          (nodeLaw n (totalWeight l) (totalWeight r)).toRight * treeTruncWaste n r 1 := by
        simpa using! treeTruncWaste_scale n r
          (nodeLaw n (totalWeight l) (totalWeight r)).toRight 1
      simp only [treeTruncSteps, treeTruncWaste, treeSteps]
      have hL1 : (nodeLaw n (totalWeight l) (totalWeight r)).toLeft * treeSteps l ≤
          (totalWeight l : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) * treeSteps l := by
        nlinarith
      have hR1 : (nodeLaw n (totalWeight l) (totalWeight r)).toRight * treeSteps r ≤
          (totalWeight r : ℝ) / ((totalWeight l + totalWeight r : ℕ) : ℝ) * treeSteps r := by
        nlinarith
      have hL2 : (nodeLaw n (totalWeight l) (totalWeight r)).toLeft * treeTruncSteps n l ≤
          (nodeLaw n (totalWeight l) (totalWeight r)).toLeft *
            (treeSteps l + treeTruncWaste n l 1) := by
        nlinarith
      have hR2 : (nodeLaw n (totalWeight l) (totalWeight r)).toRight * treeTruncSteps n r ≤
          (nodeLaw n (totalWeight l) (totalWeight r)).toRight *
            (treeSteps r + treeTruncWaste n r 1) := by
        nlinarith
      rw [hscaleL, hscaleR]
      linarith

/-- With total tree weight at most `W` and nonnegative reach, truncation waste is at most `(W +
1 + n)` times the nodewise pending ledger. -/
theorem treeTruncWaste_le_ledger (n : ℕ) (t : BucketTree) (reach W : ℝ) (hpos : PositiveTree t)
    (hW : (totalWeight t : ℝ) ≤ W) (hreach : 0 ≤ reach) :
    treeTruncWaste n t reach ≤ (W + 1 + n) * treePendingByNodes n t reach := by
  induction t generalizing reach with
  | leaf w =>
      simp [treeTruncWaste, treePendingByNodes]
  | node l r ihl ihr =>
      have hWL : 0 < totalWeight l := positiveTree_weight l hpos.1
      have hWR : 0 < totalWeight r := positiveTree_weight r hpos.2
      have hweightL : (totalWeight l : ℝ) ≤ W := by
        have h' : (totalWeight l : ℝ) ≤ (totalWeight (.node l r) : ℝ) := by
          simp only [totalWeight]
          exact_mod_cast (show totalWeight l ≤ totalWeight l + totalWeight r by omega)
        linarith
      have hweightR : (totalWeight r : ℝ) ≤ W := by
        have h' : (totalWeight r : ℝ) ≤ (totalWeight (.node l r) : ℝ) := by
          simp only [totalWeight]
          exact_mod_cast (show totalWeight r ≤ totalWeight l + totalWeight r by omega)
        linarith
      have h1 := ihl (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toLeft) hpos.1 hweightL
        (mul_nonneg hreach (nodeLaw_toLeft_nonneg n (totalWeight l) (totalWeight r)))
      have h2 := ihr (reach * (nodeLaw n (totalWeight l) (totalWeight r)).toRight) hpos.2 hweightR
        (mul_nonneg hreach (nodeLaw_toRight_nonneg n (totalWeight l) (totalWeight r)))
      have hp0 : 0 ≤ (nodeLaw n (totalWeight l) (totalWeight r)).pending :=
        nodeLaw_pending_nonneg n (totalWeight l) (totalWeight r)
      have hbudget : (totalWeight l : ℝ) + 1 + n ≤ W + 1 + n := by
        linarith
      have hroot : reach * ((totalWeight l : ℝ) + 1 + n) *
            (nodeLaw n (totalWeight l) (totalWeight r)).pending ≤
          reach * (W + 1 + n) * (nodeLaw n (totalWeight l) (totalWeight r)).pending := by
        calc reach * ((totalWeight l : ℝ) + 1 + n) *
                (nodeLaw n (totalWeight l) (totalWeight r)).pending
              = (reach * (nodeLaw n (totalWeight l) (totalWeight r)).pending) *
                ((totalWeight l : ℝ) + 1 + n) := by ring
            _ ≤ (reach * (nodeLaw n (totalWeight l) (totalWeight r)).pending) * (W + 1 + n) :=
              mul_le_mul_of_nonneg_left hbudget (mul_nonneg hreach hp0)
            _ = reach * (W + 1 + n) * (nodeLaw n (totalWeight l) (totalWeight r)).pending := by ring
      simp only [treeTruncWaste, treePendingByNodes]
      linarith

/-- For a positive tree with node pending probabilities bounded by nonnegative `eps`, truncation
waste at unit reach is at most `(totalWeight + 1 + n) * treeInternalCount * eps`. -/
theorem treeTruncWaste_le (n : ℕ) (t : BucketTree) (eps : ℝ) (hpos : PositiveTree t)
    (hb : NodePendingBound n eps t) (heps : 0 ≤ eps) :
    treeTruncWaste n t 1 ≤
      ((totalWeight t : ℝ) + 1 + n) * (treeInternalCount t : ℝ) * eps := by
  have hledger := treeTruncWaste_le_ledger n t 1 (totalWeight t : ℝ) hpos (by rfl) (by norm_num)
  have hnodes := treePendingByNodes_le n t 1 eps hpos hb (by norm_num) heps
  have hmul : ((totalWeight t : ℝ) + 1 + n) * treePendingByNodes n t 1 ≤
      ((totalWeight t : ℝ) + 1 + n) * (treeInternalCount t : ℝ) * eps := by
    calc ((totalWeight t : ℝ) + 1 + n) * treePendingByNodes n t 1
          = ((totalWeight t : ℝ) + 1 + n) * (treePendingByNodes n t 1) := by ring
        _ ≤ ((totalWeight t : ℝ) + 1 + n) * (1 * (treeInternalCount t : ℝ) * eps) :=
          mul_le_mul_of_nonneg_left hnodes (by positivity)
        _ = ((totalWeight t : ℝ) + 1 + n) * (treeInternalCount t : ℝ) * eps := by ring
  linarith

/-- For a positive tree with at least one internal node, a per-node pending bound of `delta /
treeInternalCount` bounds truncated steps by tree steps plus `(totalWeight + 1 + n) *
delta`. -/
theorem treeTruncSteps_le_budget (n : ℕ) (t : BucketTree) (delta : ℝ) (hpos : PositiveTree t)
    (hδ : 0 < delta) (hcount : 0 < treeInternalCount t)
    (hb : NodePendingBound n (delta / (treeInternalCount t : ℝ)) t) :
    treeTruncSteps n t ≤ treeSteps t + ((totalWeight t : ℝ) + 1 + n) * delta := by
  have hsteps := treeTruncSteps_le n t hpos
  have hwaste := treeTruncWaste_le n t (delta / (treeInternalCount t : ℝ)) hpos hb (by positivity)
  have hcountne : (treeInternalCount t : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hcount)
  have hmul : ((totalWeight t : ℝ) + 1 + n) * (treeInternalCount t : ℝ) *
      (delta / (treeInternalCount t : ℝ)) = ((totalWeight t : ℝ) + 1 + n) * delta := by
    field_simp
  linarith

/-- At the prescribed budget for a positive tree and positive tolerance, truncated steps are at
most tree steps plus `(totalWeight + 1 + budget) * delta`. -/
theorem treeTruncBudget_le (t : BucketTree) (delta : ℝ) (hpos : PositiveTree t)
    (hδ : 0 < delta) :
    treeTruncSteps (treeTruncationBudget t delta) t ≤
      treeSteps t + ((totalWeight t : ℝ) + 1 + treeTruncationBudget t delta) * delta := by
  cases t with
  | leaf w =>
      simp [treeTruncSteps, treeSteps]
      nlinarith [hδ]
  | node l r =>
      have hcount : 0 < treeInternalCount (.node l r) := by
        simp [treeInternalCount]
      have hcov : BudgetCovers (treeInternalCount (.node l r)) delta
          (treeTruncationBudget (.node l r) delta) (.node l r) := by
        rw [treeTruncationBudget]
        exact treeTruncationBudgetWith_covers (treeInternalCount (.node l r)) delta (.node l r)
      have hbound := nodePendingBound_of_covers (treeInternalCount (.node l r)) delta hδ hcount
        (treeTruncationBudget (.node l r) delta) (.node l r) hpos hcov
      exact treeTruncSteps_le_budget (treeTruncationBudget (.node l r) delta) (.node l r) delta
        hpos hδ hcount hbound

/-- The two encoded weights of complementary nonnegative targets sum to at most `N`. -/
theorem encWeight_sum_le (N : ℕ) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1) :
    encWeight N u + encWeight N v ≤ N := by
  have h1 := encWeight_le N u hu
  have h2 := encWeight_le N v hv
  have hsum : (encWeight N u : ℝ) + (encWeight N v : ℝ) ≤ (N : ℝ) * (u + v) := by
    linarith
  rw [huv] at hsum
  have hsum' : (encWeight N u : ℝ) + (encWeight N v : ℝ) ≤ (N : ℝ) := by
    simpa using! hsum
  exact_mod_cast hsum'

/-- When both encoded weights are positive, total encoding steps equal their sum plus their
product plus the first encoded weight plus two. -/
theorem encTotalSteps_eq (N : ℕ) (u v : ℝ) (hAu : 0 < encWeight N u) (hAv : 0 < encWeight N v) :
    encTotalSteps N u v = ((encWeight N u + encWeight N v : ℕ) : ℝ) +
      ((encWeight N u : ℝ) * (encWeight N v : ℝ) + (encWeight N u : ℝ) + 2) := by
  have h' : (expectedInputSteps (encWeight N u) (encWeight N v)).toReal =
      (encWeight N u : ℝ) * (encWeight N v : ℝ) + (encWeight N u : ℝ) + 2 := by
    have hmul : ((encWeight N u : ℝ≥0∞) * (encWeight N v : ℝ≥0∞)).toReal =
        (encWeight N u : ℝ) * (encWeight N v : ℝ) := by
      rw [ENNReal.toReal_mul]
      simp [ENNReal.toReal_natCast]
    have hA : (encWeight N u : ℝ≥0∞).toReal = (encWeight N u : ℝ) := by
      simp [ENNReal.toReal_natCast]
    have hne1 : ((encWeight N u : ℝ≥0∞) * (encWeight N v : ℝ≥0∞)) ≠ ∞ :=
      ENNReal.mul_ne_top (by simp) (by simp)
    have hne2 : (encWeight N u : ℝ≥0∞) ≠ ∞ := by simp
    have hne3 : (2 : ℝ≥0∞) ≠ ∞ := by simp
    have houter : (((encWeight N u : ℝ≥0∞) * (encWeight N v : ℝ≥0∞)) + (encWeight N u : ℝ≥0∞) + 2).toReal
        = (((encWeight N u : ℝ≥0∞) * (encWeight N v : ℝ≥0∞)) + (encWeight N u : ℝ≥0∞)).toReal + 2 := by
      exact ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hne1, hne2⟩) hne3
    have hinner : (((encWeight N u : ℝ≥0∞) * (encWeight N v : ℝ≥0∞)) + (encWeight N u : ℝ≥0∞)).toReal
        = ((encWeight N u : ℝ≥0∞) * (encWeight N v : ℝ≥0∞)).toReal + (encWeight N u : ℝ≥0∞).toReal := by
      exact ENNReal.toReal_add hne1 hne2
    rw [expectedInputSteps_eq (encWeight N u) (encWeight N v) hAu hAv]
    rw [houter, hinner, hmul, hA]
  unfold encTotalSteps encEvalSteps
  rw [h']

/-- For complementary nonnegative targets with positive encoded weights, total encoding steps
are at most `N² / 4 + 2 * N + 2`. -/
theorem encTotalSteps_le (N : ℕ) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1)
    (hAu : 0 < encWeight N u) (hAv : 0 < encWeight N v) :
    encTotalSteps N u v ≤ (N : ℝ) ^ 2 / 4 + 2 * (N : ℝ) + 2 := by
  have hsum := encWeight_sum_le N u v hu hv huv
  have hsumR : (encWeight N u : ℝ) + (encWeight N v : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hsum
  have hprod : (encWeight N u : ℝ) * (encWeight N v : ℝ) ≤ (N : ℝ) ^ 2 / 4 := by
    have hsq : 4 * ((encWeight N u : ℝ) * (encWeight N v : ℝ)) ≤
        ((encWeight N u : ℝ) + (encWeight N v : ℝ)) ^ 2 := by
      nlinarith [sq_nonneg ((encWeight N u : ℝ) - (encWeight N v : ℝ))]
    have h2 : ((encWeight N u : ℝ) + (encWeight N v : ℝ)) ^ 2 ≤ (N : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((N : ℝ) - ((encWeight N u : ℝ) + (encWeight N v : ℝ)))]
    nlinarith
  have h := encTotalSteps_eq N u v hAu hAv
  have hcast : ((encWeight N u + encWeight N v : ℕ) : ℝ) =
      (encWeight N u : ℝ) + (encWeight N v : ℝ) := by
    push_cast
    rfl
  rw [hcast] at h
  linarith

/-- A collection of exact sampler costs, geometric pending tails, encoding error and cost
bounds, and worst-path tree resource bounds. -/
structure CostLaws where

  expectedBits_eq : ∀ a b : ℕ, expectedBits a b = ((a : ℝ≥0∞) * b)

  expectedSteps_eq : ∀ a b : ℕ, 0 < a + b → expectedSteps a b = ((a : ℝ≥0∞) * b) + 1

  tail_bound : ∀ n a b : ℕ, 2 ≤ a + b →
    pendingProb (n + 1) a b ≤ ((a : ℝ) * (b : ℝ)) * decayReal a b ^ n

  input_steps_eq : ∀ A B : ℕ, 0 < A → 0 < B →
    expectedInputSteps A B = ((A : ℝ≥0∞) * B) + A + 2

  input_tail : ∀ n A B : ℕ, 2 ≤ A + B → 0 < A → 0 < B →
    pendingInputMass (A + 1 + n + 1) A B ≤
      ENNReal.ofReal ((A : ℝ) * (B : ℝ)) * (ENNReal.ofReal (decayReal A B)) ^ n

  encoding_error : ∀ (N : ℕ) (u v : ℝ), 0 ≤ u → 0 ≤ v → u + v = 1 → 3 ≤ N →
    |leftProb (encWeight N u) (encWeight N v) - v|
      ≤ 1 / ((encWeight N u + encWeight N v : ℕ) : ℝ)

  encoding_cost : ∀ (N : ℕ) (u v : ℝ), 0 ≤ u → 0 ≤ v → u + v = 1 →
    (expectedBits (encWeight N u) (encWeight N v)).toReal ≤ (N : ℝ) ^ 2 / 4

  tree_worst : ∀ (n : ℕ) (t : BucketTree),
    treeWorstSteps n t ≤ (treeDepth t : ℝ) * ((totalWeight t : ℝ) + 1 + n)

  tree_worst_attained : ∀ (n : ℕ) (t : BucketTree),
    ∃ p, isPath t p ∧ treePathCost n t p = treeWorstSteps n t

  encoding_fee : ∀ (N : ℕ) (u v : ℝ), 0 ≤ u → 0 ≤ v → u + v = 1 →
    0 < encWeight N u → 0 < encWeight N v →
    encTotalSteps N u v ≤ (N : ℝ) ^ 2 / 4 + 2 * (N : ℝ) + 2

/-- Establishes the expected costs, tail bounds, encoding estimates, and tree path bounds
packaged in `CostLaws`. -/
theorem clause23_complete : CostLaws := by
  refine ⟨expectedBits_eq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b h
    exact expectedSteps_eq a b h
  · intro n a b hN
    exact tail_bound n a b hN
  · intro A B hA hB
    exact expectedInputSteps_eq A B hA hB
  · intro n A B hN hA hB
    exact pendingInputMass_tail n A B hN hA hB
  · intro N u v hu hv huv hN
    exact encLeftProb_error N u v hu hv huv hN
  · intro N u v hu hv huv
    exact encExpectedBits_le N u v hu hv huv
  · intro n t
    exact treeWorstSteps_le n t
  · intro n t
    exact treeWorstSteps_attained n t
  · intro N u v hu hv huv hAu hAv
    exact encTotalSteps_le N u v hu hv huv hAu hAv

/-- A collection of pending-mass recurrences, outcome partitions, loader identities, and
truncation error and resource bounds for races and bucket trees. -/
structure PendingEventLaws where

  mass_le_one : ∀ n a b : ℕ, pendingMass n a b ≤ 1

  succ : ∀ n a b : ℕ, 0 < a → 0 < b →
    pendingMass (n + 1) a b =
      (1 / 2 : ℝ≥0∞) * pendingMass n (a - 1) (b + 1) +
        (1 / 2 : ℝ≥0∞) * pendingMass n (a + 1) (b - 1)

  zero_budget : ∀ a b : ℕ, 0 < a + b → pendingMass 0 a b = 1

  degenerate : ∀ n : ℕ, pendingMass n 0 0 = 0

  left_endpoint : ∀ n a b : ℕ, 0 < a + b → pendingMass (n + 1) 0 b = 0

  truncation : ∀ a b : ℕ, 2 ≤ a + b → ∀ delta : ℝ, 0 < delta →
    pendingProb (truncationBudget a b delta + 1) a b ≤ delta

  loader : ∀ n A B : ℕ, 0 < A → 0 < B →
    pendingInputMass (A + 1 + n) A B = pendingMass n A B

  partition : ∀ n a b : ℕ, 0 < a + b →
    leftEvent n a b + rightEvent n a b + pendingMass n a b = 1

  bias_left : ∀ n a b : ℕ, 0 < a + b →
    |leftEventProb n a b - (1 - pendingProb n a b) * ((b : ℝ) / (a + b : ℝ))|
      ≤ pendingProb n a b

  bias_right : ∀ n a b : ℕ, 0 < a + b →
    |rightEventProb n a b - (1 - pendingProb n a b) * ((a : ℝ) / (a + b : ℝ))|
      ≤ pendingProb n a b

  tree_success : ∀ (n : ℕ) (t : BucketTree), PositiveTree t → treeSuccessProb n t ≤ 1

  tree_succ : ∀ (n : ℕ) (l r : BucketTree), PositiveTree (.node l r) →
    treePendingProb n (.node l r) =
      (nodeLaw n (totalWeight l) (totalWeight r)).pending +
        (nodeLaw n (totalWeight l) (totalWeight r)).toLeft * treePendingProb n l +
        (nodeLaw n (totalWeight l) (totalWeight r)).toRight * treePendingProb n r

  tree_bias : ∀ (n : ℕ) (t : BucketTree) (p : List Bool), PositiveTree t → isPath t p →
    |treeLeafMassTrunc n t p - (1 - treePendingProb n t) * leafMass t p|
      ≤ treePendingProb n t

  tree_nodes : ∀ (n : ℕ) (t : BucketTree), PositiveTree t →
    treePendingProb n t ≤ treePendingByNodes n t 1

  tree_budget : ∀ (t : BucketTree) (delta : ℝ), PositiveTree t → 0 < delta →
    treePendingProb (treeTruncationBudget t delta) t ≤ delta

  tree_expected : ∀ (t : BucketTree) (delta : ℝ), PositiveTree t → 0 < delta →
    treeTruncSteps (treeTruncationBudget t delta) t ≤
      treeSteps t + ((totalWeight t : ℝ) + 1 + treeTruncationBudget t delta) * delta

  trunc_waste : ∀ n A B : ℕ,
    truncatedInputSteps n A B ≤ expectedInputSteps A B + (n : ℝ≥0∞) * pendingInputMass n A B

  encoding_truncation : ∀ (N : ℕ) (u v : ℝ), 0 ≤ u → 0 ≤ v → u + v = 1 → 3 ≤ N →
    ∀ n : ℕ,
    |leftEventProb n (encWeight N u) (encWeight N v) - v|
      ≤ 1 / ((encWeight N u + encWeight N v : ℕ) : ℝ) +
        pendingProb n (encWeight N u) (encWeight N v)

/-- Establishes the pending-event, truncation-bias, and resource estimates packaged in
`PendingEventLaws`. -/
theorem clause24_complete : PendingEventLaws := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n a b
    exact pendingMass_le_one n a b
  · intro n a b ha hb
    exact pendingMass_succ n a b ha hb
  · intro a b h
    exact pendingMass_zero_budget a b h
  · intro n
    exact pendingMass_degenerate n
  · intro n a b h
    exact pendingMass_left_endpoint (n + 1) b (by omega)
  · intro a b hN delta hδ
    exact truncation_bound a b hN delta hδ
  · intro n A B hA hB
    exact pendingInputMass_eq n A B hA hB
  · intro n a b h
    exact law_outcome_partition n a b h
  · intro n a b h
    exact truncation_bias_left n a b h
  · intro n a b h
    exact truncation_bias_right n a b h
  · intro n t h
    exact treeSuccessProb_le_one n t h
  · intro n l r h
    exact treePendingProb_succ n l r h
  · intro n t p h h'
    exact treeTruncationBias n t p h' h
  · intro n t h
    exact treePendingProb_le_nodes n t h
  · intro t delta h h'
    exact treeTruncationBudget_bound t delta h h'
  · intro t delta h h'
    exact treeTruncBudget_le t delta h h'
  · intro n A B
    exact truncatedInputSteps_le n A B
  · intro N u v hu hv huv hN n
    exact encTruncation_error N u v hu hv huv hN n

end Qatlib.Concepts.MixedInstrument.ClockBridge
