/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Matching.MatchedMedianTail
import Mathlib.Data.Nat.Sqrt

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Matched Plan Arithmetic

Matched Plan Arithmetic constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
open scoped BigOperators
open Qatlib

/-- Construction for ceil Sqrt Q in the matched plan arithmetic model. -/
def ceilSqrtQ (q : ℚ) : ℕ :=
  let n := Nat.sqrt (ceilNatQ q)
  if (n : ℚ)^2 < q then n+1 else n

/-- Construction for matched Count Q in the matched plan arithmetic model. -/
def matchedCountQ (M : ℕ) (ε ρ : ℚ) : ℕ :=
  ceilSqrtQ (256*(M : ℚ)*(ceilLog2Q (7/ρ) : ℚ)/ε^2)

/-- Construction for saturated Blocks Q in the matched plan arithmetic model. -/
def saturatedBlocksQ (M : ℕ) (ε ρ : ℚ) : ℕ :=
  let n := max 1 (ceilNatQ (2048*(ceilLog2Q (7/ρ) : ℚ)/((M : ℚ)*ε^2)))
  n+(1-n%2)

noncomputable section

/-- Complete original `ceil_sqrt_q_square` guarantee for `MatchedPlanArithmetic`; all source hypotheses and output obligations are retained. -/
theorem ceil_sqrt_q_square (q : ℚ) (hq : 0≤q) : (q : ℝ) ≤ (ceilSqrtQ q : ℝ)^2 := by
  dsimp only [ceilSqrtQ]
  split_ifs with h
  · have hc := (ceil_nat_bounds q hq).1
    have hs : (ceilNatQ q : ℝ) < ((Nat.sqrt (ceilNatQ q)+1 : ℕ) : ℝ)^2 := by
      exact_mod_cast Nat.lt_succ_sqrt' (ceilNatQ q)
    exact (hc.trans hs.le)
  · exact_mod_cast le_of_not_gt h

/-- Complete original `saturated_blocks_pos` guarantee for `MatchedPlanArithmetic`; all source hypotheses and output obligations are retained. -/
theorem saturated_blocks_pos (M : ℕ) (ε ρ : ℚ) : 0<saturatedBlocksQ M ε ρ := by
  dsimp only [saturatedBlocksQ]
  omega

/-- Complete original `saturated_blocks_odd` guarantee for `MatchedPlanArithmetic`; all source hypotheses and output obligations are retained. -/
theorem saturated_blocks_odd (M : ℕ) (ε ρ : ℚ) : (saturatedBlocksQ M ε ρ)%2=1 := by
  dsimp only [saturatedBlocksQ]
  omega

/-- Complete original `saturated_blocks_ge_ceil` guarantee for `MatchedPlanArithmetic`; all source hypotheses and output obligations are retained. -/
theorem saturated_blocks_ge_ceil (M : ℕ) (ε ρ : ℚ) :
    ceilNatQ (2048*(ceilLog2Q (7/ρ) : ℚ)/((M : ℚ)*ε^2)) ≤ saturatedBlocksQ M ε ρ := by
  dsimp only [saturatedBlocksQ]
  omega

/-- Complete original `saturated_blocks_log_budget` guarantee for `MatchedPlanArithmetic`; all source hypotheses and output obligations are retained. -/
theorem saturated_blocks_log_budget (M : ℕ) (hM : 0<M) (ε ρ : ℚ)
    (hε : 0<ε) (hρ : 0<ρ) :
    2048*Real.log (1/(ρ : ℝ)) ≤
      (saturatedBlocksQ M ε ρ : ℝ)*(M : ℝ)*(ε : ℝ)^2 := by
  let q := 2048*(ceilLog2Q (7/ρ) : ℚ)/((M : ℚ)*ε^2)
  have hq : 0≤q := by dsimp [q]; positivity
  have hc := (ceil_nat_bounds q hq).1
  have hn : (ceilNatQ q : ℝ) ≤ (saturatedBlocksQ M ε ρ : ℝ) := by
    dsimp only [q]
    exact_mod_cast saturated_blocks_ge_ceil M ε ρ
  have hratio : 2048*(ceilLog2Q (7/ρ) : ℝ)/((M : ℝ)*(ε : ℝ)^2) ≤
      (saturatedBlocksQ M ε ρ : ℝ) := by
    simpa only [q, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_natCast, Rat.cast_ofNat] using hc.trans hn
  have hx : (0 : ℝ)<(M : ℝ)*(ε : ℝ)^2 := by
    have hm : (0 : ℝ)<M := by exact_mod_cast hM
    have he : (0 : ℝ)<ε := Rat.cast_pos.mpr hε
    positivity
  have hb := (div_le_iff₀ hx).mp hratio
  have hρR : (0 : ℝ)<ρ := Rat.cast_pos.mpr hρ
  have hlog : Real.log (1/(ρ : ℝ)) ≤ (ceilLog2Q (7/ρ) : ℝ) := by
    have hl := ceil_log2_log_bound (7/ρ) (by positivity)
    have hl' : Real.log (7/(ρ : ℝ)) ≤ (ceilLog2Q (7/ρ) : ℝ) := by
      simpa only [Rat.cast_div, Rat.cast_ofNat] using hl
    have harg : (1 : ℝ)/(ρ : ℝ) ≤ 7/(ρ : ℝ) :=
      div_le_div_of_nonneg_right (by norm_num : (1 : ℝ)≤7) hρR.le
    exact (Real.log_le_log (by positivity) harg).trans hl'
  calc
    _ ≤ 2048*(ceilLog2Q (7/ρ) : ℝ) := mul_le_mul_of_nonneg_left hlog (by norm_num)
    _ ≤ (saturatedBlocksQ M ε ρ : ℝ)*((M : ℝ)*(ε : ℝ)^2) := hb
    _ = _ := by ring

/-- Complete original `confidence_log_count_pos` guarantee for `MatchedPlanArithmetic`; all source hypotheses and output obligations are retained. -/
theorem confidence_log_count_pos (ρ : ℚ) (hρ : 0<ρ) (hρ1 : ρ<1) :
    0<ceilLog2Q (7/ρ) := by
  have harg : (1 : ℚ)<7/ρ := (lt_div_iff₀ hρ).mpr (by linarith)
  by_contra hn
  have hn0 : ceilLog2Q (7/ρ)=0 := by omega
  have hp := ceil_log2_power (7/ρ)
  rw [hn0, pow_zero] at hp
  linarith

/-- Complete original `matched_count_square_budget` guarantee for `MatchedPlanArithmetic`; all source hypotheses and output obligations are retained. -/
theorem matched_count_square_budget (M : ℕ) (ε ρ : ℚ) (hε : 0<ε) :
    256*(M : ℝ)*(ceilLog2Q (7/ρ) : ℝ) ≤
      (matchedCountQ M ε ρ : ℝ)^2*(ε : ℝ)^2 := by
  have hq : (0 : ℚ)≤256*(M : ℚ)*(ceilLog2Q (7/ρ) : ℚ)/ε^2 := by positivity
  have hs := ceil_sqrt_q_square _ hq
  have hsr : 256*(M : ℝ)*(ceilLog2Q (7/ρ) : ℝ)/(ε : ℝ)^2 ≤
      (matchedCountQ M ε ρ : ℝ)^2 := by
    simpa only [matchedCountQ, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_natCast, Rat.cast_ofNat] using hs
  have he : (0 : ℝ)<(ε : ℝ)^2 := by
    have hεR : (0 : ℝ)<ε := Rat.cast_pos.mpr hε
    positivity
  exact (div_le_iff₀ he).mp hsr

/-- Complete original `matched_count_pos` guarantee for `MatchedPlanArithmetic`; all source hypotheses and output obligations are retained. -/
theorem matched_count_pos (M : ℕ) (hM : 0<M) (ε ρ : ℚ)
    (hε : 0<ε) (hρ : 0<ρ) (hρ1 : ρ<1) : 0<matchedCountQ M ε ρ := by
  have hL := confidence_log_count_pos ρ hρ hρ1
  have hb := matched_count_square_budget M ε ρ hε
  have hM' : (0 : ℝ)<M := by exact_mod_cast hM
  have hL' : (0 : ℝ)<ceilLog2Q (7/ρ) := by exact_mod_cast hL
  by_contra hn
  have hn0 : matchedCountQ M ε ρ=0 := by omega
  rw [hn0] at hb
  norm_num at hb
  nlinarith [mul_pos hM' hL']

variable {S : Type} [Fintype S] [Nonempty S] [DecidableEq S]

/-- Complete original `signed_planned_saturated_median_confidence` guarantee for `MatchedPlanArithmetic`; all source hypotheses and output obligations are retained. -/
theorem signed_planned_saturated_median_confidence (τ : Equiv.Perm S)
    (a b : S → ℝ) (ha : ∀ x, |a x|≤1) (hb : ∀ x, |b x|≤1)
    (ε ρ : ℚ) (hε : 0<ε) (hε1 : ε≤1) (hρ : 0<ρ)
    (hx : (2048 : ℚ)≤(Fintype.card S : ℚ)*ε^2) :
    (productLaw (cohortLaw (signedRecordLaw a ha) (Fintype.card S))
      (cohortLaw (signedRecordLaw b hb) (Fintype.card S))).probEvent
      (fun ω : Fin (saturatedBlocksQ (Fintype.card S) ε ρ) →
          ((Fin (Fintype.card S) → S × Bool) × (Fin (Fintype.card S) → S × Bool)) =>
        (ε : ℝ) < |(rawBlockMedianQ (fun z => matchedStatisticQ z.1 z.2 τ) ω : ℝ)-
          setAverage Finset.univ (fun x => a x*b (τ x))|) ≤ (ρ : ℝ) := by
  apply signed_saturated_median_confidence τ (saturated_blocks_pos _ ε ρ) a b ha hb
  · exact_mod_cast hε
  · exact_mod_cast hε1
  · exact_mod_cast hρ
  · exact_mod_cast hx
  · exact saturated_blocks_log_budget _ Fintype.card_pos ε ρ hε hρ

/-- Complete original `signed_planned_single_match_confidence` guarantee for `MatchedPlanArithmetic`; all source hypotheses and output obligations are retained. -/
theorem signed_planned_single_match_confidence (τ : Equiv.Perm S)
    (a b : S → ℝ) (ha : ∀ x, |a x|≤1) (hb : ∀ x, |b x|≤1)
    (ε ρ : ℚ) (hε : 0<ε) (hε1 : ε≤1) (hρ : 0<ρ) (hρ1 : ρ<1)
    (hcount : matchedCountQ (Fintype.card S) ε ρ ≤ Fintype.card S) :
    finiteBadMass
      (productLaw (cohortLaw (signedRecordLaw a ha) (matchedCountQ (Fintype.card S) ε ρ))
        (cohortLaw (signedRecordLaw b hb) (matchedCountQ (Fintype.card S) ε ρ)))
      (fun z => (matchedStatisticQ z.1 z.2 τ : ℝ))
      (setAverage Finset.univ (fun x => a x*b (τ x))) (ε : ℝ) ≤ (ρ : ℝ) := by
  let n := matchedCountQ (Fintype.card S) ε ρ
  let L := ceilLog2Q (7/ρ)
  have hM : (0 : ℝ)<Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hρR : (0 : ℝ)<ρ := Rat.cast_pos.mpr hρ
  have hn0 : 0<n := matched_count_pos _ Fintype.card_pos ε ρ hε hρ hρ1
  have hbudget := matched_count_square_budget (Fintype.card S) ε ρ hε
  have hratio : (L : ℝ) ≤ (n : ℝ)^2*(ε : ℝ)^2/(256*(Fintype.card S : ℝ)) := by
    apply (le_div_iff₀ (show (0 : ℝ)<256*(Fintype.card S : ℝ) by positivity)).mpr
    nlinarith only [hbudget]
  have hargpos : (0 : ℝ)<7/(ρ : ℝ) := by positivity
  have hlog : Real.log (7/(ρ : ℝ)) ≤ (L : ℝ) := by
    have hh := ceil_log2_log_bound (7/ρ) (by positivity)
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hh
  have hexp : Real.exp (-(L : ℝ)) ≤ (ρ : ℝ)/7 := by
    calc
      _ ≤ Real.exp (-Real.log (7/(ρ : ℝ))) := Real.exp_le_exp.mpr (neg_le_neg hlog)
      _ = _ := by rw [Real.exp_neg, Real.exp_log hargpos, inv_div]
  have ht := signed_matched_unconditional_tail τ n n hn0 hn0 hcount hcount a b ha hb
    (ε : ℝ) (by exact_mod_cast hε) (by exact_mod_cast hε1)
  have heq : -(n : ℝ)*(n : ℝ)*(ε : ℝ)^2/(256*(Fintype.card S : ℝ)) =
      -((n : ℝ)^2*(ε : ℝ)^2/(256*(Fintype.card S : ℝ))) := by ring
  rw [heq] at ht
  calc
    _ ≤ 6*Real.exp (-((n : ℝ)^2*(ε : ℝ)^2/(256*(Fintype.card S : ℝ)))) := ht
    _ ≤ 6*Real.exp (-(L : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hratio)) (by norm_num)
    _ ≤ 6*((ρ : ℝ)/7) := mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ ≤ (ρ : ℝ) := by linarith

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.ceil_sqrt_q_square
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.saturated_blocks_pos
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.saturated_blocks_odd
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.saturated_blocks_log_budget
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matched_count_square_budget
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.signed_planned_saturated_median_confidence
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.signed_planned_single_match_confidence
