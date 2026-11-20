/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.SpinorSampling.Matching.CorrelationPlan

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

/-!
# Correlation Plan Bounds

Correlation Plan Bounds constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

set_option autoImplicit false

namespace Qatlib.Concepts.SpinorSampling.Matching.Matched
noncomputable section

/-- For a nonnegative rational `q`, its integer square-root ceiling is at most one above the
real square root. -/
theorem ceil_sqrt_q_upper (q : ℚ) (hq : 0≤q) :
    (ceilSqrtQ q : ℝ) ≤ Real.sqrt (q : ℝ)+1 := by
  have hqR : (0 : ℝ)≤q := Rat.cast_nonneg.mpr hq
  have hroot := Real.sqrt_nonneg (q : ℝ)
  have hsquare := Real.sq_sqrt hqR
  dsimp only [ceilSqrtQ]
  split_ifs with h
  · have hn : ((Nat.sqrt (ceilNatQ q) : ℕ) : ℝ)^2 < (q : ℝ) := by exact_mod_cast h
    have hn0 : (0 : ℝ)≤(Nat.sqrt (ceilNatQ q) : ℕ) := Nat.cast_nonneg _
    push_cast
    nlinarith
  · have hn : ((Nat.sqrt (ceilNatQ q) : ℕ) : ℝ)^2 ≤ (ceilNatQ q : ℝ) := by
      exact_mod_cast Nat.sqrt_le' (ceilNatQ q)
    have hc := (ceil_nat_bounds q hq).2
    have hn0 : (0 : ℝ)≤(Nat.sqrt (ceilNatQ q) : ℕ) := Nat.cast_nonneg _
    nlinarith

/-- For positive site count and tolerance and `0 < ρ < 1`, the saturated block count is at most
`2048 * ceilLog2Q (7/ρ) / (M * ε²) + 2`. -/
theorem saturated_blocks_upper (M : ℕ) (hM : 0<M) (ε ρ : ℚ) (hε : 0<ε)
    (hρ : 0<ρ) (hρ1 : ρ<1) :
    (saturatedBlocksQ M ε ρ : ℝ) ≤
      2048*(ceilLog2Q (7/ρ) : ℝ)/((M : ℝ)*(ε : ℝ)^2)+2 := by
  let q : ℚ := 2048*(ceilLog2Q (7/ρ) : ℚ)/((M : ℚ)*ε^2)
  have hL := confidence_log_count_pos ρ hρ hρ1
  have hq : 0<q := by dsimp [q]; positivity
  have hc := ceil_nat_bounds q hq.le
  have hcpos : 0<ceilNatQ q := by
    have hqR : (0 : ℝ)<q := Rat.cast_pos.mpr hq
    by_contra h
    have hz : ceilNatQ q=0 := by omega
    rw [hz] at hc
    norm_num at hc
    linarith
  have hmax : max 1 (ceilNatQ q)=ceilNatQ q := max_eq_right hcpos
  have hnum : (saturatedBlocksQ M ε ρ : ℝ) ≤ (ceilNatQ q : ℝ)+1 := by
    dsimp only [saturatedBlocksQ]
    change ((max 1 (ceilNatQ q)+(1-max 1 (ceilNatQ q)%2) : ℕ) : ℝ) ≤ _
    rw [hmax, Nat.cast_add]
    have hu : (1-ceilNatQ q%2 : ℕ)≤1 := Nat.sub_le _ _
    have huR : ((1-ceilNatQ q%2 : ℕ) : ℝ)≤1 := by exact_mod_cast hu
    linarith
  have hcR : (ceilNatQ q : ℝ) <
      2048*(ceilLog2Q (7/ρ) : ℝ)/((M : ℝ)*(ε : ℝ)^2)+1 := by
    simpa only [q, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast,
      Rat.cast_pow, Rat.cast_ofNat] using hc.2
  linarith

-- A rejected single cohort does not permit an arbitrary M-sized rounding
-- payment. The literal root bound makes that payment O(L/epsilon^2).
/-- If `M ≥ 2` and the matched count for positive tolerance exceeds `M`, the product `M * ε²` is
at most `1024 * ceilLog2Q (7/ρ)`. -/
theorem rejected_match_size_budget (M : ℕ) (hM : 2≤M) (ε ρ : ℚ) (hε : 0<ε)
    (hreject : M<matchedCountQ M ε ρ) :
    (M : ℝ)*(ε : ℝ)^2 ≤ 1024*(ceilLog2Q (7/ρ) : ℝ) := by
  let q : ℚ := 256*(M : ℚ)*(ceilLog2Q (7/ρ) : ℚ)/ε^2
  have hq : 0≤q := by dsimp [q]; positivity
  have hn := ceil_sqrt_q_upper q hq
  have hM : (2 : ℝ)≤M := by exact_mod_cast hM
  have hrejectR : (M : ℝ)<matchedCountQ M ε ρ := by exact_mod_cast hreject
  have hhalf : (M : ℝ)/2≤Real.sqrt (q : ℝ) := by
    change (ceilSqrtQ q : ℝ)≤_ at hn
    change (M : ℝ)<ceilSqrtQ q at hrejectR
    linarith
  have hsq := sq_le_sq₀ (by positivity : (0 : ℝ)≤(M : ℝ)/2)
    (Real.sqrt_nonneg (q : ℝ))
  have hM2 : (M : ℝ)^2/4 ≤ (q : ℝ) := by
    have hh := hsq.mpr hhalf
    rw [Real.sq_sqrt (Rat.cast_nonneg.mpr hq)] at hh
    nlinarith
  have hqR : (q : ℝ)=256*(M : ℝ)*(ceilLog2Q (7/ρ) : ℝ)/(ε : ℝ)^2 := by
    simp only [q, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat]
  rw [hqR] at hM2
  have he : (0 : ℝ)<(ε : ℝ)^2 := by
    have he0 : (0 : ℝ)<ε := Rat.cast_pos.mpr hε
    positivity
  have hb := (le_div_iff₀ he).mp hM2
  have hMpos : (0 : ℝ)<M := by linarith
  nlinarith only [hb, hMpos]

/-- If the requested matched count exceeds `M ≥ 2`, the saturated schedule uses at most
`8192 * ceilLog2Q (7/ρ) / ε²` copies for positive tolerance and `0 < ρ < 1`. -/
theorem planned_saturated_copy_bound (M : ℕ) (hM : 2≤M) (ε ρ : ℚ)
    (hε : 0<ε) (hρ : 0<ρ) (hρ1 : ρ<1) (hreject : M<matchedCountQ M ε ρ) :
    ((2*M*saturatedBlocksQ M ε ρ : ℕ) : ℝ) ≤
      8192*(ceilLog2Q (7/ρ) : ℝ)/(ε : ℝ)^2 := by
  have hM0 : 0<M := by omega
  have hK := saturated_blocks_upper M hM0 ε ρ hε hρ hρ1
  have hsize := rejected_match_size_budget M hM ε ρ hε hreject
  have he : (0 : ℝ)<(ε : ℝ)^2 := by
    have he0 : (0 : ℝ)<ε := Rat.cast_pos.mpr hε
    positivity
  have hMpos : (0 : ℝ)<M := by exact_mod_cast hM0
  have hK' := (le_div_iff₀ (mul_pos hMpos he)).mp
    (show (saturatedBlocksQ M ε ρ : ℝ)-2 ≤
      2048*(ceilLog2Q (7/ρ) : ℝ)/((M : ℝ)*(ε : ℝ)^2) by linarith)
  apply (le_div_iff₀ he).mpr
  push_cast
  nlinarith only [hK', hsize]


/-- For `0 < ρ < 1`, the base-two ceiling log at `1/ρ` is no larger than the one at `7/ρ`. -/
theorem confidence_log_count_dominates (ρ : ℚ) (hρ : 0<ρ) (hρ1 : ρ<1) :
    ceilLog2Q (1/ρ)≤ceilLog2Q (7/ρ) := by
  have harg : (1 : ℚ)<1/ρ := (lt_div_iff₀ hρ).mpr (by simpa using hρ1)
  by_contra h
  have hp : (2 : ℚ)^(ceilLog2Q (7/ρ)) ≤ (2 : ℚ)^(ceilLog2Q (1/ρ)) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hh := (ceil_log2_power (7/ρ)).trans hp
  have hu := ceil_log2_power_lt_twice (1/ρ) harg
  have hu' : (2 : ℚ)^(ceilLog2Q (1/ρ))<2/ρ := by
    simpa only [mul_one_div] using hu
  have hlt : (7 : ℚ)/ρ<2/ρ := hh.trans_lt hu'
  have hc := (div_lt_div_iff_of_pos_right hρ).mp hlt
  norm_num at hc

/-- For a nonnegative `rootM` and positive tolerance, a unit-norm fallback block takes at most
`3 + 32 / ε² + 8 * rootM / ε` records. -/
theorem fallback_block_count_upper (rootM ε : ℚ) (hroot : 0≤rootM) (hε : 0<ε) :
    (blockRecordsQ 1 rootM ε : ℝ) ≤
      3+32/(ε : ℝ)^2+8*(rootM : ℝ)/(ε : ℝ) := by
  let q := max 2 (max (32/ε^2) (8*rootM/ε))
  have hq : (0 : ℚ)≤q := (by norm_num : (0 : ℚ)≤2).trans (le_max_left _ _)
  have hc := (ceil_nat_bounds q hq).2
  have hupper : q≤2+32/ε^2+8*rootM/ε := by
    apply max_le
    · have h1 : (0 : ℚ)≤32/ε^2 := by positivity
      have h2 : (0 : ℚ)≤8*rootM/ε := by positivity
      linarith
    · apply max_le
      · have h2 : (0 : ℚ)≤8*rootM/ε := by positivity
        linarith
      · have h1 : (0 : ℚ)≤32/ε^2 := by positivity
        linarith
  have hur : (q : ℝ)≤2+32/(ε : ℝ)^2+8*(rootM : ℝ)/(ε : ℝ) := by exact_mod_cast hupper
  have heq : blockRecordsQ 1 rootM ε=ceilNatQ q := by simp only [blockRecordsQ, q, mul_one]
  rw [heq]
  linarith

/-- The fallback blocks cost at most `4376 * ceilLog2Q (7/ρ) / ε²` copies when `0 ≤ rootM`, its
square is at most `2 * M`, `0 < ε < 1`, `0 < ρ < 1`, and `M * ε² < 2048`. -/
theorem planned_fallback_copy_bound (M : ℕ) (rootM ε ρ : ℚ)
    (hroot : 0≤rootM) (hroot2 : (rootM : ℝ)^2≤2*(M : ℝ))
    (hε : 0<ε) (hε1 : ε<1) (hρ : 0<ρ) (hρ1 : ρ<1)
    (hx : (M : ℚ)*ε^2<2048) :
    ((blockRecordsQ 1 rootM ε*medianBlocksQ ρ : ℕ) : ℝ) ≤
      4376*(ceilLog2Q (7/ρ) : ℝ)/(ε : ℝ)^2 := by
  have he : (0 : ℝ)<ε := Rat.cast_pos.mpr hε
  have he1 : (ε : ℝ)<1 := by exact_mod_cast hε1
  have hxR : (M : ℝ)*(ε : ℝ)^2<2048 := by exact_mod_cast hx
  have hrootR : (0 : ℝ)≤rootM := Rat.cast_nonneg.mpr hroot
  have hrootε : (rootM : ℝ)*(ε : ℝ)≤64 := by
    have hp := mul_le_mul_of_nonneg_right hroot2 (sq_nonneg (ε : ℝ))
    nlinarith
  have hn := fallback_block_count_upper rootM ε hroot hε
  have hnB : (blockRecordsQ 1 rootM ε : ℝ)*(ε : ℝ)^2≤547 := by
    have hh := mul_le_mul_of_nonneg_right hn (sq_nonneg (ε : ℝ))
    have heq : (3+32/(ε : ℝ)^2+8*(rootM : ℝ)/(ε : ℝ))*(ε : ℝ)^2 =
        3*(ε : ℝ)^2+32+8*(rootM : ℝ)*(ε : ℝ) := by field_simp
    rw [heq] at hh
    nlinarith
  have hL := confidence_log_count_pos ρ hρ hρ1
  have hLR : (1 : ℝ)≤ceilLog2Q (7/ρ) := by exact_mod_cast hL
  have hdom : (ceilLog2Q (1/ρ) : ℝ)≤ceilLog2Q (7/ρ) := by
    exact_mod_cast confidence_log_count_dominates ρ hρ hρ1
  have hK := median_blocks_upper ρ
  have hKB : (medianBlocksQ ρ : ℝ)≤8*(ceilLog2Q (7/ρ) : ℝ) := by linarith
  have hp := mul_le_mul hnB hKB (Nat.cast_nonneg _) (by norm_num : (0 : ℝ)≤547)
  apply (le_div_iff₀ (show (0 : ℝ)<(ε : ℝ)^2 by positivity)).mpr
  push_cast
  nlinarith only [hp]

/-- Rounding the half exponent of `2^(d*r)` upward gives a dyadic root whose square is at most
twice the original power. -/
theorem dyadic_root_square_upper (d r : ℕ) :
    (((2^((d*r+1)/2) : ℕ) : ℝ))^2 ≤ 2*((2^(d*r) : ℕ) : ℝ) := by
  have hn : (2^((d*r+1)/2) : ℕ)^2≤2*2^(d*r) := by
    rw [← Nat.pow_mul, ← Nat.pow_succ']
    exact Nat.pow_le_pow_right (by decide : 1≤2) (by omega)
  exact_mod_cast hn


/-- For positive tolerance, the requested matched count is at most one plus `16 / ε` times the
square root of `M * ceilLog2Q (7/ρ)`. -/
theorem matched_count_upper (M : ℕ) (ε ρ : ℚ) (hε : 0<ε) :
    (matchedCountQ M ε ρ : ℝ) ≤
      16*Real.sqrt ((M : ℝ)*(ceilLog2Q (7/ρ) : ℝ))/(ε : ℝ)+1 := by
  have hq : (0 : ℚ)≤256*(M : ℚ)*(ceilLog2Q (7/ρ) : ℚ)/ε^2 := by positivity
  have hn := ceil_sqrt_q_upper _ hq
  have he : (0 : ℝ)<ε := Rat.cast_pos.mpr hε
  have hcast : ((256*(M : ℚ)*(ceilLog2Q (7/ρ) : ℚ)/ε^2 : ℚ) : ℝ)=
      256*((M : ℝ)*(ceilLog2Q (7/ρ) : ℝ))/(ε : ℝ)^2 := by push_cast; ring
  rw [hcast, Real.sqrt_div (by positivity :
    (0 : ℝ)≤256*((M : ℝ)*(ceilLog2Q (7/ρ) : ℝ))),
    Real.sqrt_mul (by norm_num : (0 : ℝ)≤256),
    Real.sqrt_sq_eq_abs, abs_of_pos he] at hn
  have hs256 : Real.sqrt (256 : ℝ)=16 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
  rw [hs256] at hn
  exact hn

/-- If `rootM` is nonnegative with square at most `2 * M`, the plan uses at most `16384` times
the sum of `ceilLog2Q (7/ρ) / ε²` and `sqrt (M * ceilLog2Q (7/ρ)) / ε` for `ε > 0` and
`0 < ρ < 1`. -/
theorem correlation_plan_copy_bound (M : ℕ) (rootM ε ρ : ℚ)
    (hroot : 0≤rootM) (hroot2 : (rootM : ℝ)^2≤2*(M : ℝ))
    (hε : 0<ε) (hρ : 0<ρ) (hρ1 : ρ<1) :
    ((correlationPlanQ M rootM ε ρ).copies : ℝ) ≤
      16384*((ceilLog2Q (7/ρ) : ℝ)/(ε : ℝ)^2+
        Real.sqrt ((M : ℝ)*(ceilLog2Q (7/ρ) : ℝ))/(ε : ℝ)) := by
  have he : (0 : ℝ)<ε := Rat.cast_pos.mpr hε
  have hL := confidence_log_count_pos ρ hρ hρ1
  have hLR : (1 : ℝ)≤ceilLog2Q (7/ρ) := by exact_mod_cast hL
  have hA : (0 : ℝ)≤(ceilLog2Q (7/ρ) : ℝ)/(ε : ℝ)^2 := by positivity
  have hB : (0 : ℝ)≤Real.sqrt ((M : ℝ)*(ceilLog2Q (7/ρ) : ℝ))/(ε : ℝ) := by positivity
  dsimp only [correlationPlanQ]
  split_ifs with hz hn hx
  · norm_num
    positivity
  · have hn' := matched_count_upper M ε ρ hε
    have he1 : (ε : ℝ)<1 := by exact_mod_cast lt_of_not_ge hz
    have hA1 : (1 : ℝ)≤(ceilLog2Q (7/ρ) : ℝ)/(ε : ℝ)^2 := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ)<(ε : ℝ)^2)).mpr
      nlinarith
    push_cast
    simp only [mul_div_assoc] at hn' ⊢
    nlinarith only [hn', hA1, hB]
  · have hM : 2≤M := by
      by_contra hh
      have hMq : (M : ℚ)≤1 := by exact_mod_cast (show M≤1 by omega)
      have he1 : ε<1 := lt_of_not_ge hz
      nlinarith [sq_nonneg ε]
    have hc := planned_saturated_copy_bound M hM ε ρ hε hρ hρ1 (by omega)
    exact hc.trans (by simp only [mul_div_assoc]; nlinarith only [hA,hB])
  · have hc := planned_fallback_copy_bound M rootM ε ρ hroot hroot2 hε
      (lt_of_not_ge hz) hρ hρ1 (lt_of_not_ge hx)
    exact hc.trans (by simp only [mul_div_assoc]; nlinarith only [hA,hB])

/-- For a grid with `2^(d*r)` cells and the dyadic root used by the planner, positive `ε` and
`0 < ρ < 1` give the copy bound `16384 * (L / ε² + sqrt (2^(d*r) * L) / ε)` with
`L = ceilLog2Q (7/ρ)`. -/
theorem grid_correlation_plan_copy_bound (d r : ℕ) (ε ρ : ℚ)
    (hε : 0<ε) (hρ : 0<ρ) (hρ1 : ρ<1) :
    let p := correlationPlanQ (2^(d*r)) ((2^((d*r+1)/2) : ℕ) : ℚ) ε ρ
    (p.copies : ℝ) ≤ 16384*((ceilLog2Q (7/ρ) : ℝ)/(ε : ℝ)^2+
      Real.sqrt (((2^(d*r) : ℕ) : ℝ)*(ceilLog2Q (7/ρ) : ℝ))/(ε : ℝ)) := by
  apply correlation_plan_copy_bound _ _ ε ρ (by positivity) _ hε hρ hρ1
  simpa only [Rat.cast_natCast] using dyadic_root_square_upper d r

end
end Qatlib.Concepts.SpinorSampling.Matching.Matched

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.ceil_sqrt_q_upper
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.saturated_blocks_upper
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.rejected_match_size_budget
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.planned_saturated_copy_bound

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.confidence_log_count_dominates
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.fallback_block_count_upper
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.planned_fallback_copy_bound
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.dyadic_root_square_upper

#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.matched_count_upper
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.correlation_plan_copy_bound
#print axioms Qatlib.Concepts.SpinorSampling.Matching.Matched.grid_correlation_plan_copy_bound
