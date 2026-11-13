/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.EffCosts.EffectiveDysonDefinitions
import Qatlib.Concepts.InteractionEvo.MeanDerivGrid.EffectiveMeanDerivativeGridErrorHami

/-!
# Dyadic segment parameters for Dyson accuracy

This module proves that effective segment parameters supply a positive dyadic grid at least as
large as the squared cutoff. It also gives a ceiling-logarithm cutoff rate and the segment error
bound obtained from the integrated derivative estimate. The parameter choices serve the
short-segment Dyson analysis of [LowWiebe2018].

## Main statements

* `effectiveSegment_grid_structure`: positivity and the squared-cutoff grid bound.
* `effectiveDysonParameters_error`: error at most `2^(-(precision + 6))`.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.InteractionEvo.ComputedGrid
open Qatlib.Concepts.InteractionEvo.EffCosts
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.DysonMeanDerivativeGrid
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.EffectiveMeanDerivativeGridErrorHami
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open scoped BigOperators Matrix.Norms.L2Operator

/-- Segment parameters satisfying the domain conditions have positive grid size and squared
cutoff at most the grid size. -/
theorem effectiveSegment_grid_structure (p : EffectiveSegmentParameters)
    (hp : effectiveSegmentDomain p) :
    0 < effectiveSegmentM p ∧ (effectiveSegmentK p)^2 ≤ effectiveSegmentM p := by
  constructor
  · exact pow_pos (by decide) _
  · exact (le_max_right 1 ((effectiveSegmentK p)^2)).trans
      ((le_max_left _ _).trans hp.2.2.2.2)

/-- For all sufficiently large `k`, the cutoff at `k + 8` times `Nat.clog 2 (k + 2)` is bounded
by a constant times `k + 2`. -/
theorem effectiveDysonCutoff_clog_rate : ∃ C m0 : ℕ, ∀ k : ℕ, m0 ≤ k →
    computedDysonCutoff (k+8)*Nat.clog 2 (k+2) ≤ C*(k+2) := by
  obtain ⟨C,m0,_hC,_hm0,hr⟩ := computedDysonCutoff_tail_and_rate.2
  refine ⟨10*C,m0,?_⟩
  intro k hk
  have hlog : 1 ≤ Nat.log 2 (k+10) := by
    apply (Nat.le_log_iff_pow_le (by decide) (by omega)).mpr
    norm_num
  have hclog : Nat.clog 2 (k+2) ≤ Nat.log 2 (k+10)+1 := by
    apply Nat.clog_le_of_le_pow
    exact (show k+2 ≤ k+10 by omega).trans (Nat.lt_pow_succ_log_self (by decide) (k+10)).le
  have hl2 : Nat.clog 2 (k+2) ≤ 2*Nat.log 2 (k+10) := by omega
  have hrate := hr (k+8) (by omega)
  calc
    _ ≤ computedDysonCutoff (k+8)*(2*Nat.log 2 (k+10)) := Nat.mul_le_mul_left _ hl2
    _ = 2*(computedDysonCutoff (k+8)*Nat.log 2 (k+10)) := by ring
    _ ≤ 2*(C*(k+10)) := Nat.mul_le_mul_left _ hrate
    _ ≤ (10*C)*(k+2) := by nlinarith

/-- Under the segment domain and field hypotheses, the computed truncated grid has operator
error at most `(1 / 2)^(p.precision + 6)`. -/
theorem effectiveDysonParameters_error (p : EffectiveSegmentParameters)
    (H Hd : ℝ → Matrix (Reg p.ns) (Reg p.ns) ℂ)
    (hp : effectiveSegmentDomain p) (hF : EffectiveField p H Hd) :
    ‖dysonGridTruncatedSum H p.time (effectiveSegmentM p) (effectiveSegmentK p) -
      orderedEvolution (fun u => Complex.I • H u) 0 p.time‖ ≤ (1/2 : ℝ)^(p.precision+6) := by
  rcases hp with ⟨ht,hα,hχ,hsmall,hM⟩
  rcases hF with ⟨hH,hint,hderiv,hbound,hmean⟩
  have htr : (0 : ℝ) ≤ p.time := by exact_mod_cast ht
  have har : (0 : ℝ) ≤ p.alpha := by exact_mod_cast hα.le
  have hcr : (0 : ℝ) ≤ p.meanDerivative := by exact_mod_cast hχ
  have hMpos : (0 : ℝ) < effectiveSegmentM p := by
    exact_mod_cast (pow_pos (by decide : 0 < (2 : ℕ)) p.nd)
  have hlog : (p.alpha : ℝ)*(p.time : ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this
    exact hsmall.trans this
  have he := effectiveMeanDerivativeGridError (Reg p.ns) H Hd p.time p.alpha
    (effectiveSegmentM p) (effectiveSegmentK p) hH hint hderiv htr har
    (by exact_mod_cast hMpos) hbound hlog
  have htail := computedDysonCutoff_tail_and_rate.1 (p.precision+8)
    ((p.alpha : ℝ)*(p.time : ℝ)) (mul_nonneg har htr) hlog
  have hgrid : 16*(p.time : ℝ)^2*((p.meanDerivative : ℝ)+(p.alpha : ℝ)^2)*
      (2 : ℝ)^(p.precision+8) ≤ effectiveSegmentM p := by
    have hn : Nat.ceil (16*(p.time : ℝ)^2*((p.meanDerivative : ℝ)+(p.alpha : ℝ)^2)*
        (2 : ℝ)^(p.precision+8)) ≤ effectiveSegmentM p := (le_max_right _ _).trans hM
    exact (Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
  have hexp : Real.exp ((p.alpha : ℝ)*(p.time : ℝ)) ≤ 2 := by
    have hh := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log (by norm_num : (0 : ℝ)<2)] at hh
    exact hh
  have hint0 : 0 ≤ ∫ u in (0 : ℝ)..(p.time : ℝ), ‖Hd u‖ :=
    intervalIntegral.integral_nonneg htr (fun _ _ => norm_nonneg _)
  have hbudget : (p.time : ℝ)^2*((p.meanDerivative : ℝ)+(p.alpha : ℝ)^2)/
      effectiveSegmentM p ≤ (1/2 : ℝ)^(p.precision+8)/16 := by
    apply (div_le_iff₀ hMpos).mpr
    have hpow : (0 : ℝ) < 2^(p.precision+8) := by positivity
    rw [div_pow, one_pow]
    field_simp
    nlinarith
  have hfirst : Real.exp ((p.alpha : ℝ)*(p.time : ℝ))*(p.alpha : ℝ)^2*(p.time : ℝ)^2/
      (2*effectiveSegmentM p) ≤ (p.alpha : ℝ)^2*(p.time : ℝ)^2/effectiveSegmentM p := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<2*effectiveSegmentM p)).mpr
    field_simp
    nlinarith [mul_nonneg (sq_nonneg (p.alpha : ℝ)) (sq_nonneg (p.time : ℝ))]
  have hsecond : ((p.time : ℝ)/effectiveSegmentM p)*
      (∫ u in (0 : ℝ)..(p.time : ℝ), ‖Hd u‖) ≤
      (p.meanDerivative : ℝ)*(p.time : ℝ)^2/effectiveSegmentM p := by
    have hh := mul_le_mul_of_nonneg_left hmean (div_nonneg htr hMpos.le)
    convert! hh using 1; ring
  have hboth := add_le_add hfirst hsecond
  have hdisc : Real.exp ((p.alpha : ℝ)*(p.time : ℝ))*(p.alpha : ℝ)^2*(p.time : ℝ)^2/
      (2*effectiveSegmentM p) + ((p.time : ℝ)/effectiveSegmentM p)*
      (∫ u in (0 : ℝ)..(p.time : ℝ), ‖Hd u‖) ≤ (1/2 : ℝ)^(p.precision+8)/16 := by
    apply hboth.trans
    convert! hbudget using 1; ring
  apply he.trans
  have hs := add_le_add hdisc htail
  change _ ≤ (1/2 : ℝ)^(p.precision+6)
  apply hs.trans
  rw [show p.precision+8 = (p.precision+6)+2 by omega, pow_add]
  norm_num
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) (p.precision+6)]

end Qatlib.Concepts.InteractionEvo.MeanDerivGrid
