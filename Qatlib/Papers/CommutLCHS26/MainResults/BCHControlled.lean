/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHHalfBudget
import Qatlib.Papers.CommutLCHS26.MainResults.BCHConvergence
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHControlled

open Matrix Filter
open scoped BigOperators Classical Matrix.Norms.L2Operator NNReal ENNReal Topology
open BCHHalfBudget BCHConvergence BCHFormal
open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.RecursiveSuzuki
set_option warningAsError false

variable {I : Type} [Fintype I] [DecidableEq I]

def OddControl (xs : List (Matrix I I ℂ)) (r : ℝ≥0) (J : ℕ) : Prop :=
  ∀ n : ℕ, J ≤ n → Odd n → (r : ℝ) ^ n * pfCommAlphaSelf xs n ≤ 1

theorem radius_norm_summable (xs : List (Matrix I I ℂ)) (r : ℝ≥0) (J : ℕ)
    (hcontrol : OddControl xs r J) :
    Summable (fun n => (r : ℝ) ^ n * ‖BCHFormal.logCoefficient
      (SubdivisionPolynomial.wordSeries (recursiveSuzukiGenerators xs 0)) n‖) := by
  let N := max J 1
  have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by decide)
  apply (summable_nat_add_iff N).mp
  apply ((summable_nat_add_iff N).mpr hp).of_nonneg_of_le
  · intro n
    exact mul_nonneg (pow_nonneg r.2 _) (norm_nonneg _)
  · intro n
    have hn : 0 < n + N := by dsimp only [N]; omega
    rcases Nat.even_or_odd (n + N) with he | ho
    · rw [frozen_half_log_even xs (n + N) he, norm_zero, mul_zero]
      positivity
    · have hc := hcontrol (n + N) (by dsimp only [N]; omega) ho
      calc
        _ ≤ (r : ℝ) ^ (n + N) * (pfCommAlphaSelf xs (n + N) / ((n + N : ℕ) : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (norm_frozen_half_log_le xs (n + N) hn)
            (pow_nonneg r.2 _)
        _ = ((r : ℝ) ^ (n + N) * pfCommAlphaSelf xs (n + N)) / ((n + N : ℕ) : ℝ) ^ 2 := by ring
        _ ≤ _ := div_le_div_of_nonneg_right hc (sq_nonneg _)

theorem norm_scaled_log_le_radius (xs : List (Matrix I I ℂ)) (r : ℝ≥0)
    (z : ℂ) (hz : ‖z‖ ≤ r) (n : ℕ) :
    ‖scaled (BCHFormal.logSeries
      (SubdivisionPolynomial.wordSeries (recursiveSuzukiGenerators xs 0))) z n‖ ≤
        (r : ℝ) ^ n * ‖BCHFormal.logCoefficient
          (SubdivisionPolynomial.wordSeries (recursiveSuzukiGenerators xs 0)) n‖ := by
  simp only [scaled, BCHFormal.logSeries, PowerSeries.coeff_mk, norm_smul, norm_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg z) hz n) (norm_nonneg _)

theorem log_norm_summable_closed (xs : List (Matrix I I ℂ)) (r : ℝ≥0) (J : ℕ)
    (hcontrol : OddControl xs r J) (z : ℂ) (hz : ‖z‖ ≤ r) :
    Summable (fun n => ‖scaled (BCHFormal.logSeries
      (SubdivisionPolynomial.wordSeries (recursiveSuzukiGenerators xs 0))) z n‖) :=
  (radius_norm_summable xs r J hcontrol).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_scaled_log_le_radius xs r z hz)

theorem log_uniform_closed (xs : List (Matrix I I ℂ)) (r : ℝ≥0) (J : ℕ)
    (hcontrol : OddControl xs r J) :
    TendstoUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N, scaled (BCHFormal.logSeries
        (SubdivisionPolynomial.wordSeries (recursiveSuzukiGenerators xs 0))) z n)
      (evaluate (BCHFormal.logSeries
        (SubdivisionPolynomial.wordSeries (recursiveSuzukiGenerators xs 0)))) atTop
      (Metric.closedBall (0 : ℂ) r) := by
  apply tendstoUniformlyOn_tsum_nat (radius_norm_summable xs r J hcontrol)
  intro n z hz
  apply norm_scaled_log_le_radius xs r z
  simpa only [Metric.mem_closedBall, dist_zero_right] using! hz

theorem controlled_radius (xs : List (Matrix I I ℂ)) (r : ℝ≥0) (J : ℕ)
    (hcontrol : OddControl xs r J) :
    (r : ℝ≥0∞) ≤ (analyticSeries (recursiveSuzukiGenerators xs 0)).radius := by
  exact analyticSeries_radius_of_summable _ r (radius_norm_summable xs r J hcontrol)

theorem log_analyticAt (xs : List (Matrix I I ℂ)) (r : ℝ≥0) (J : ℕ)
    (hcontrol : OddControl xs r J) (z : ℂ) (hz : ‖z‖ < r) :
    AnalyticAt ℂ (evaluate (BCHFormal.logSeries
      (SubdivisionPolynomial.wordSeries (recursiveSuzukiGenerators xs 0)))) z := by
  have hmem : z ∈ Metric.eball (0 : ℂ) (analyticSeries (recursiveSuzukiGenerators xs 0)).radius := by
    apply lt_of_lt_of_le _ (controlled_radius xs r J hcontrol)
    rw [edist_dist, dist_zero_right, ENNReal.ofReal_lt_coe_iff (norm_nonneg z)]
    exact hz
  exact (analyticSeries_sum (recursiveSuzukiGenerators xs 0)) ▸
    (analyticSeries (recursiveSuzukiGenerators xs 0)).analyticOnNhd z hmem

theorem exp_log_closed (xs : List (Matrix I I ℂ)) (r : ℝ≥0) (J : ℕ)
    (hcontrol : OddControl xs r J) (z : ℂ) (hz : ‖z‖ ≤ r) :
    NormedSpace.exp (evaluate (BCHFormal.logSeries
      (SubdivisionPolynomial.wordSeries (recursiveSuzukiGenerators xs 0))) z) =
        complexWord (recursiveSuzukiGenerators xs 0) z := by
  rw [exp_evaluate_log _ (by simp [SubdivisionPolynomial.wordSeries]) z
    (log_norm_summable_closed xs r J hcontrol z hz)]
  exact (complexWord_hasSum (recursiveSuzukiGenerators xs 0) z).tsum_eq

theorem exp_log_one (xs : List (Matrix I I ℂ)) (J : ℕ)
    (hcomm : ∀ n : ℕ, J ≤ n → Odd n → pfCommAlphaSelf xs n ≤ 1) :
    NormedSpace.exp (evaluate (BCHFormal.logSeries
      (SubdivisionPolynomial.wordSeries (recursiveSuzukiGenerators xs 0))) 1) =
        complexWord (recursiveSuzukiGenerators xs 0) 1 := by
  apply exp_log_closed xs 1 J _ 1 (by simp)
  intro n hn ho
  simpa only [NNReal.coe_one, one_pow, one_mul] using! hcomm n hn ho

theorem log_one_odd_tail (xs : List (Matrix I I ℂ)) (J : ℕ)
    (hcomm : ∀ n : ℕ, J ≤ n → Odd n → pfCommAlphaSelf xs n ≤ 1) :
    evaluate (BCHFormal.logSeries
      (SubdivisionPolynomial.wordSeries (recursiveSuzukiGenerators xs 0))) 1 =
      xs.sum + ∑' j : ℕ, BCHFormal.logCoefficient
        (SubdivisionPolynomial.wordSeries (recursiveSuzukiGenerators xs 0)) (2 * j + 3) := by
  let c := BCHFormal.logCoefficient
    (SubdivisionPolynomial.wordSeries (recursiveSuzukiGenerators xs 0))
  have hc : Summable c := by
    have hs := radius_norm_summable xs 1 J (by
      intro n hn ho
      simpa only [NNReal.coe_one, one_pow, one_mul] using! hcomm n hn ho)
    exact (by simpa only [NNReal.coe_one, one_pow, one_mul] using! hs :
      Summable (fun n => ‖c n‖)).of_norm
  have he : Summable (fun j : ℕ => c (2 * j)) :=
    hc.comp_injective (by intro a b h; change 2 * a = 2 * b at h; omega)
  have ho : Summable (fun j : ℕ => c (2 * j + 1)) :=
    hc.comp_injective (by intro a b h; change 2 * a + 1 = 2 * b + 1 at h; omega)
  have hz : (∑' j : ℕ, c (2 * j)) = 0 := by
    have heven (j : ℕ) : c (2 * j) = 0 := frozen_half_log_even xs _ (even_two_mul j)
    simp only [heven, tsum_zero]
  have hsplit := tsum_even_add_odd he ho
  rw [hz, zero_add] at hsplit
  change (∑' n, scaled _ 1 n) = _
  simp only [scaled, one_pow, one_smul, BCHFormal.logSeries, PowerSeries.coeff_mk]
  rw [← hsplit, ho.tsum_eq_zero_add]
  change c 1 + (∑' j : ℕ, c (2 * (j + 1) + 1)) = _
  have hc1 : c 1 = xs.sum := frozen_half_log_one xs
  rw [hc1]
  congr 1

theorem half_product_eq_exp_odd_tail (xs : List (Matrix I I ℂ)) (J : ℕ)
    (hcomm : ∀ n : ℕ, J ≤ n → Odd n → pfCommAlphaSelf xs n ≤ 1) :
    (xs.map (fun A => NormedSpace.exp ((1 / 2 : ℝ) • A))).prod *
      (xs.reverse.map (fun A => NormedSpace.exp ((1 / 2 : ℝ) • A))).prod =
      NormedSpace.exp (xs.sum + ∑' j : ℕ, BCHFormal.logCoefficient
        (SubdivisionPolynomial.wordSeries (recursiveSuzukiGenerators xs 0)) (2 * j + 3)) := by
  have h := (exp_log_one xs J hcomm).symm
  rw [log_one_odd_tail xs J hcomm] at h
  simpa only [complexWord, recursiveSuzukiGenerators, List.map_append,
    List.prod_append, List.map_map, Function.comp_def, one_smul] using! h

theorem oddControl_neg_I (xs : List (Matrix I I ℂ)) (r : ℝ≥0) (J : ℕ) :
    OddControl (xs.map (fun A => (-Complex.I) • A)) r J ↔ OddControl xs r J := by
  simp only [OddControl, frozen_profile_neg_I]

theorem real_unitary_log_skew (xs : List (Matrix I I ℂ))
    (hxs : ∀ A ∈ xs, Aᴴ = A) (r : ℝ≥0) (J : ℕ)
    (hcontrol : OddControl xs r J) (t : ℝ) (ht : |t| ≤ r) :
    (Summable fun n => ‖scaled (BCHFormal.logSeries (SubdivisionPolynomial.wordSeries
      (recursiveSuzukiGenerators (xs.map (fun A => (-Complex.I) • A)) 0))) (t : ℂ) n‖) ∧
    (evaluate (BCHFormal.logSeries (SubdivisionPolynomial.wordSeries
      (recursiveSuzukiGenerators (xs.map (fun A => (-Complex.I) • A)) 0))) (t : ℂ))ᴴ =
      -evaluate (BCHFormal.logSeries (SubdivisionPolynomial.wordSeries
        (recursiveSuzukiGenerators (xs.map (fun A => (-Complex.I) • A)) 0))) (t : ℂ) := by
  refine ⟨log_norm_summable_closed _ r J ((oddControl_neg_I xs r J).mpr hcontrol)
    (t : ℂ) (by simpa only [Complex.norm_real, Real.norm_eq_abs] using! ht), ?_⟩
  have hs (n : ℕ) : (scaled (BCHFormal.logSeries (SubdivisionPolynomial.wordSeries
      (recursiveSuzukiGenerators (xs.map (fun A => (-Complex.I) • A)) 0))) (t : ℂ) n)ᴴ =
      -scaled (BCHFormal.logSeries (SubdivisionPolynomial.wordSeries
        (recursiveSuzukiGenerators (xs.map (fun A => (-Complex.I) • A)) 0))) (t : ℂ) n := by
    simp only [scaled, BCHFormal.logSeries, PowerSeries.coeff_mk, ← Complex.ofReal_pow,
      Complex.coe_smul, Matrix.conjTranspose_smul, star_trivial,
      unitary_half_log_skew xs hxs, smul_neg]
  simp only [evaluate, Matrix.conjTranspose_tsum, hs, tsum_neg]

end Qatlib.Papers.CommutLCHS26.MainResults.BCHControlled
