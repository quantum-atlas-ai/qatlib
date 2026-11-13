/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonSparseHam09.MainResults.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Cast

set_option backward.isDefEq.respectTransparency false

/-!
# Promise-Set Probability Asymptotics for Uniform Sign Strings

This module formalizes Lemma 4 (Eq. (20)) of Childs and Kothari showing that for
a uniformly random sign string `s ∈ {-1, +1}^M`, the probability of lying in
`promiseSet M` (`∑ s_i = ±promiseB M` with `promiseB M ≈ √(M log M)`) satisfies
`c₁ / M ≤ Pr(s ∈ promiseSet M) ≤ c₂ / M` for all sufficiently large `M`.

## Main statements

* `lemma4_promise_probability`: Lemma 4, proving `Pr(b ∈ promiseSet M) = Θ(1 / M)`.

## References

* [Childs and Kothari, 2010][ChildsKothari2010], Section 4, Lemma 4, Eq. (20),
  p. 8 and Appendix, p. 13.
-/

set_option autoImplicit false
noncomputable section

open Matrix Finset Filter
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.NonSparseHam09.MainResults

private lemma sign_sum_count (M : ℕ) (b : Fin M → Bool) :
    (∑ i, signVec b i) =
      2 * ((univ.filter (fun i => b i = true)).card : ℝ) - (M : ℝ) := by
  classical
  calc
    (∑ i, signVec b i) = ∑ i, ((if b i = true then (2 : ℝ) else 0) - 1) := by
      apply sum_congr rfl
      intro i hi
      cases h : b i <;> norm_num [signVec, signOf, h]
    _ = _ := by
      rw [sum_sub_distrib]
      simp [sum_ite, mul_comm]

private lemma card_sign_level (M k : ℕ) :
    (univ.filter (fun b : Fin M → Bool =>
      ∑ i, signVec b i = 2 * (k : ℝ) - (M : ℝ))).card = Nat.choose M k := by
  classical
  let S (b : Fin M → Bool) := univ.filter (fun i => b i = true)
  have hs (b : Fin M → Bool) :
      (∑ i, signVec b i) = 2 * ((S b).card : ℝ) - (M : ℝ) := sign_sum_count M b
  have hc : (univ.filter (fun b : Fin M → Bool =>
      ∑ i, signVec b i = 2 * (k : ℝ) - (M : ℝ))).card =
      ((univ : Finset (Fin M)).powersetCard k).card := by
    refine card_bij (fun b _ => S b) ?_ ?_ ?_
    · intro b hb
      refine mem_powersetCard.mpr ⟨subset_univ _, ?_⟩
      have he := (mem_filter.mp hb).2
      rw [hs b] at he
      have he' : ((S b).card : ℝ) = (k : ℝ) := by linarith
      exact_mod_cast he'
    · intro b hb c hc h
      funext i
      have hi : (b i = true) ↔ (c i = true) := by
        simpa [S] using (Finset.ext_iff.mp h i)
      cases hbi : b i <;> cases hci : c i <;> simp_all
    · intro s hsk
      have hk : s.card = k := (mem_powersetCard.mp hsk).2
      let b : Fin M → Bool := fun i => decide (i ∈ s)
      have hb : S b = s := by ext i; simp [S, b]
      refine ⟨b, mem_filter.mpr ⟨mem_univ _, ?_⟩, hb⟩
      rw [hs b, hb, hk]
  simpa using hc

private lemma sign_sum_not (M : ℕ) (b : Fin M → Bool) :
    (∑ i, signVec (fun j => !(b j)) i) = -(∑ i, signVec b i) := by
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro i hi
  cases h : b i <;> simp [signVec, signOf, h]

private lemma card_sign_neg (M : ℕ) (B : ℝ) :
    (univ.filter (fun b : Fin M → Bool => ∑ i, signVec b i = B)).card =
      (univ.filter (fun b : Fin M → Bool => ∑ i, signVec b i = -B)).card := by
  classical
  let e (b : Fin M → Bool) : Fin M → Bool := fun i => !(b i)
  have he : Function.Involutive e := by intro b; funext i; simp [e]
  apply card_bijective e he.bijective
  intro b
  simp only [mem_filter, mem_univ, true_and]
  change (∑ i, signVec b i) = B ↔ (∑ i, signVec (fun j => !(b j)) i) = -B
  rw [sign_sum_not]
  simp

private lemma promiseB_error (M : ℕ) :
    |(promiseB M : ℝ) - Real.sqrt (M * Real.log M)| ≤ 2 := by
  have hf := Nat.floor_le (show 0 ≤ Real.sqrt (M * Real.log M) / 2 by positivity)
  have hg := Nat.lt_floor_add_one (Real.sqrt (M * Real.log M) / 2)
  have hm : ((M % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (show M % 2 ≤ 1 by omega)
  have hm0 : (0 : ℝ) ≤ ((M % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  simp only [promiseB, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [abs_le]
  constructor <;> linarith

private lemma promiseB_parity (M : ℕ) : 2 * ((M + promiseB M) / 2) = M + promiseB M := by
  unfold promiseB
  omega

private lemma probability_choose (M : ℕ) (hB : 0 < promiseB M) :
    probOf M (fun b => b ∈ promiseSet M) =
      2 * (Nat.choose M ((M + promiseB M) / 2) : ℝ) / (2 : ℝ) ^ M := by
  classical
  have hp : (promiseB M : ℝ) = 2 * (((M + promiseB M) / 2 : ℕ) : ℝ) - M := by
    have h := promiseB_parity M
    have h' : 2 * (((M + promiseB M) / 2 : ℕ) : ℝ) = M + (promiseB M : ℝ) := by
      exact_mod_cast h
    linarith
  have hd : Disjoint
      (univ.filter (fun b : Fin M → Bool => ∑ i, signVec b i = (promiseB M : ℝ)))
      (univ.filter (fun b : Fin M → Bool => ∑ i, signVec b i = -(promiseB M : ℝ))) := by
    apply disjoint_left.mpr
    intro b hb hc
    have hb' := (mem_filter.mp hb).2
    have hc' := (mem_filter.mp hc).2
    have hpos : (0 : ℝ) < promiseB M := by exact_mod_cast hB
    linarith
  unfold probOf promiseSet promiseStrings
  simp only [mem_filter, mem_univ, true_and]
  rw [filter_or, card_union_of_disjoint hd, ← card_sign_neg, hp, card_sign_level]
  push_cast
  ring

private def biasDelta (M : ℕ) : ℝ := (promiseB M : ℝ) / M

private lemma log_div_nat :
    Tendsto (fun M : ℕ => Real.log M / (M : ℝ)) atTop (nhds 0) := by
  simpa only [Function.comp_def, Real.rpow_one] using
    ((isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)

private lemma log_div_sqrt_nat :
    Tendsto (fun M : ℕ => Real.log M / Real.sqrt M) atTop (nhds 0) := by
  simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
    ((isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).tendsto_div_nhds_zero).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)

private lemma sqrt_log_ratio :
    Tendsto (fun M : ℕ => Real.sqrt (M * Real.log M) / (M : ℝ)) atTop (nhds 0) := by
  have h := log_div_nat.sqrt
  simp only [Real.sqrt_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  symm
  calc
    _ = Real.sqrt (M * Real.log M) / Real.sqrt ((M : ℝ) ^ 2) := by
      rw [Real.sqrt_sq hM0.le]
    _ = Real.sqrt ((M : ℝ) * Real.log M / (M : ℝ) ^ 2) :=
      (Real.sqrt_div (by positivity) _).symm
    _ = _ := by congr 1; field_simp

private lemma biasDelta_tendsto : Tendsto biasDelta atTop (nhds 0) := by
  have hi := tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
  have hz := sqrt_log_ratio.add hi
  rw [zero_add] at hz
  apply squeeze_zero_norm' _ hz
  filter_upwards [eventually_ge_atTop 1] with M hM
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have he := (abs_le.mp (promiseB_error M)).2
  rw [biasDelta, Real.norm_of_nonneg (by positivity)]
  simpa only [add_div] using (div_le_div_of_nonneg_right
    (show (promiseB M : ℝ) ≤ Real.sqrt (M * Real.log M) + 2 by linarith) hM0.le)

private lemma bias_square_error :
    Tendsto (fun M : ℕ => (promiseB M : ℝ) ^ 2 / M - Real.log M) atTop (nhds 0) := by
  have hz := (sqrt_log_ratio.const_mul 4).add (tendsto_const_div_atTop_nhds_zero_nat 4)
  simp only [mul_zero, zero_add] at hz
  apply squeeze_zero_norm' _ hz
  filter_upwards [eventually_ge_atTop 1] with M hM
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlog : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ M * Real.log M by positivity)
  have he := promiseB_error M
  have hp : (0 : ℝ) ≤ promiseB M := Nat.cast_nonneg _
  have hr := Real.sqrt_nonneg ((M : ℝ) * Real.log M)
  have heq : (promiseB M : ℝ) ^ 2 / M - Real.log M =
      ((promiseB M : ℝ) - Real.sqrt (M * Real.log M)) *
        ((promiseB M : ℝ) + Real.sqrt (M * Real.log M)) / M := by
    apply (eq_div_iff hM0.ne').2
    field_simp
    nlinarith
  rw [Real.norm_eq_abs, heq, abs_div, abs_mul, abs_of_pos hM0, abs_of_nonneg (by positivity :
      0 ≤ (promiseB M : ℝ) + Real.sqrt (M * Real.log M))]
  calc
    _ ≤ 2 * ((promiseB M : ℝ) + Real.sqrt (M * Real.log M)) / M := by
      gcongr
    _ ≤ 4 * (Real.sqrt (M * Real.log M) / M) + 4 / M := by
      apply (div_le_iff₀ hM0).2
      field_simp
      linarith [(abs_le.mp he).2]

private lemma bias_fourth_error :
    Tendsto (fun M : ℕ => (M : ℝ) * biasDelta M ^ 4) atTop (nhds 0) := by
  have hi : Tendsto (fun M : ℕ => 1 / Real.sqrt M) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have h := ((bias_square_error.mul hi).add log_div_sqrt_nat).pow 2
  simp only [zero_mul, zero_add, zero_pow (by decide : 2 ≠ 0)] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hs := Real.sq_sqrt hM0.le
  dsimp only [biasDelta]
  field_simp
  nlinarith

private lemma nonneg_from_deriv {f f' : ℝ → ℝ} {x : ℝ}
    (hd : ∀ y ∈ Set.Icc (0 : ℝ) (1 / 2), HasDerivAt f (f' y) y)
    (hn : ∀ y ∈ Set.Icc (0 : ℝ) (1 / 2), 0 ≤ f' y)
    (h0 : 0 ≤ f 0) (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2)) : 0 ≤ f x := by
  have hmono : MonotoneOn f (Set.Icc (0 : ℝ) (1 / 2)) :=
    monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (fun y hy => (hd y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt)
      (fun y hy => by
        rw [(hd y (interior_subset hy)).deriv]
        exact hn y (interior_subset hy))
  exact h0.trans (hmono (by norm_num) hx hx.1)

private def biasEntropy (x : ℝ) : ℝ :=
  (1 + x) * Real.log (1 + x) + (1 - x) * Real.log (1 - x)

private lemma entropy_sandwich (x : ℝ) (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    x ^ 2 ≤ biasEntropy x ∧ biasEntropy x ≤ x ^ 2 + x ^ 4 := by
  let L : ℝ → ℝ := fun y => Real.log (1 + y) - Real.log (1 - y)
  have hdL (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) (1 / 2)) :
      HasDerivAt L (1 / (1 + y) + 1 / (1 - y)) y := by
    have hp : 0 < 1 + y := by linarith [hy.1]
    have hm : 0 < 1 - y := by linarith [hy.2]
    dsimp only [L]
    convert (((hasDerivAt_id y).const_add 1).log hp.ne').sub
      (((hasDerivAt_id y).const_sub 1).log hm.ne') using 1 <;>
      (try funext t) <;> simp only [id_eq, Pi.sub_apply]
    ring
  have hdF (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) (1 / 2)) :
      HasDerivAt biasEntropy (L y) y := by
    have hp : 0 < 1 + y := by linarith [hy.1]
    have hm : 0 < 1 - y := by linarith [hy.2]
    dsimp only [biasEntropy, L]
    convert (((hasDerivAt_id y).const_add 1).mul
      (((hasDerivAt_id y).const_add 1).log hp.ne')).add
        (((hasDerivAt_id y).const_sub 1).mul
          (((hasDerivAt_id y).const_sub 1).log hm.ne')) using 1 <;>
      (try funext t) <;> simp only [id_eq, Pi.add_apply, Pi.mul_apply, biasEntropy]
    field_simp [hp.ne', hm.ne']
    ring
  have hlo (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) (1 / 2)) : 2 * y ≤ L y := by
    have h := nonneg_from_deriv
      (f := fun z => L z - 2 * z)
      (f' := fun z => 1 / (1 + z) + 1 / (1 - z) - 2)
      (fun z hz => by
        convert (hdL z hz).sub ((hasDerivAt_id z).const_mul 2) using 1 <;>
          (try funext t) <;> (try simp only [id_eq, Pi.sub_apply])
        ring)
      (fun z hz => by
        have hp : 0 < 1 + z := by linarith [hz.1]
        have hm : 0 < 1 - z := by linarith [hz.2]
        have heq : 1 / (1 + z) + 1 / (1 - z) - 2 =
            2 * z ^ 2 / ((1 + z) * (1 - z)) := by
          field_simp [hp.ne', hm.ne']
          ring
        rw [heq]
        exact div_nonneg (by positivity) (mul_pos hp hm).le)
      (by norm_num [L]) hy
    exact sub_nonneg.mp h
  have hhi (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) (1 / 2)) : L y ≤ 2 * y + 4 * y ^ 3 := by
    have h := nonneg_from_deriv
      (f := fun z => 2 * z + 4 * z ^ 3 - L z)
      (f' := fun z => 2 + 12 * z ^ 2 - (1 / (1 + z) + 1 / (1 - z)))
      (fun z hz => by
        convert (((hasDerivAt_id z).const_mul 2).add
          ((hasDerivAt_pow 3 z).const_mul 4)).sub (hdL z hz) using 1 <;>
          (try funext t) <;> (try simp only [id_eq, Pi.sub_apply, Pi.add_apply])
        norm_num
        ring)
      (fun z hz => by
        have hp : 0 < 1 + z := by linarith [hz.1]
        have hm : 0 < 1 - z := by linarith [hz.2]
        have hz2 : z ^ 2 ≤ 1 / 4 := by
          nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)]
        have hf : 0 ≤ 5 - 6 * z ^ 2 := by nlinarith
        have heq : 2 + 12 * z ^ 2 - (1 / (1 + z) + 1 / (1 - z)) =
            2 * z ^ 2 * (5 - 6 * z ^ 2) / ((1 + z) * (1 - z)) := by
          field_simp [hp.ne', hm.ne']
          ring
        rw [heq]
        exact div_nonneg (by positivity) (mul_pos hp hm).le)
      (by norm_num [L]) hy
    exact sub_nonneg.mp h
  constructor
  · have h := nonneg_from_deriv
      (f := fun z => biasEntropy z - z ^ 2)
      (f' := fun z => L z - 2 * z)
      (fun z hz => by
        convert (hdF z hz).sub (hasDerivAt_pow 2 z) using 1
        norm_num)
      (fun z hz => sub_nonneg.mpr (hlo z hz))
      (by norm_num [biasEntropy]) ⟨hx0, hxhalf⟩
    exact sub_nonneg.mp h
  · have h := nonneg_from_deriv
      (f := fun z => z ^ 2 + z ^ 4 - biasEntropy z)
      (f' := fun z => 2 * z + 4 * z ^ 3 - L z)
      (fun z hz => by
        convert ((hasDerivAt_pow 2 z).add (hasDerivAt_pow 4 z)).sub (hdF z hz)
          using 1
        norm_num)
      (fun z hz => sub_nonneg.mpr (hhi z hz))
      (by norm_num [biasEntropy]) ⟨hx0, hxhalf⟩
    exact sub_nonneg.mp h

private lemma entropy_centered :
    Tendsto (fun M : ℕ => (M : ℝ) * biasEntropy (biasDelta M) - Real.log M)
      atTop (nhds 0) := by
  have hr : Tendsto (fun M : ℕ => (M : ℝ) *
      (biasEntropy (biasDelta M) - biasDelta M ^ 2)) atTop (nhds 0) := by
    apply squeeze_zero_norm' _ bias_fourth_error
    filter_upwards [biasDelta_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with M hM
    have hd : 0 ≤ biasDelta M := by unfold biasDelta; positivity
    have he := entropy_sandwich (biasDelta M) hd hM.le
    rw [Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr he.1))]
    exact mul_le_mul_of_nonneg_left (by linarith [he.2]) (Nat.cast_nonneg _)
  have h := hr.add bias_square_error
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  dsimp only [biasDelta]
  field_simp
  ring

private lemma bias_eventually :
    ∀ᶠ M : ℕ in atTop, 0 < M ∧ 0 < promiseB M ∧ promiseB M < M ∧ biasDelta M < 1 / 2 := by
  have hlog : ∀ᶠ M : ℕ in atTop, 1 ≤ Real.log M :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [eventually_ge_atTop 16, hlog,
    biasDelta_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
    with M hM hlog hd
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM16 : (16 : ℝ) ≤ M := by exact_mod_cast hM
  have hprod : (16 : ℝ) ≤ M * Real.log M := by nlinarith
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ M * Real.log M by positivity)
  have he := abs_le.mp (promiseB_error M)
  have hB : 0 < promiseB M := by
    by_contra h
    have hz : promiseB M = 0 := by omega
    simp only [hz, Nat.cast_zero, zero_sub] at he
    have hr := Real.sqrt_nonneg ((M : ℝ) * Real.log M)
    nlinarith
  refine ⟨by omega, hB, ?_, hd⟩
  have hlt : (promiseB M : ℝ) < M := by
    have h := (div_lt_iff₀ hM0).mp hd
    linarith
  exact_mod_cast hlt

private def biasK (M : ℕ) : ℕ := (M + promiseB M) / 2

private def biasL (M : ℕ) : ℕ := M - biasK M

private lemma bias_indices (M : ℕ) (hM : 0 < M) (hB : promiseB M < M) :
    (biasK M : ℝ) = M * (1 + biasDelta M) / 2 ∧
      (biasL M : ℝ) = M * (1 - biasDelta M) / 2 ∧ biasK M ≤ M := by
  have hk : 2 * biasK M = M + promiseB M := promiseB_parity M
  have hkn : biasK M ≤ M := by omega
  have hkr : 2 * (biasK M : ℝ) = M + (promiseB M : ℝ) := by exact_mod_cast hk
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  refine ⟨?_, ?_, hkn⟩
  · unfold biasDelta
    field_simp
    nlinarith
  · rw [biasL, Nat.cast_sub hkn]
    unfold biasDelta
    field_simp
    nlinarith

private lemma bias_indices_tendsto :
    Tendsto biasK atTop atTop ∧ Tendsto biasL atTop atTop := by
  have hm : Tendsto (fun M : ℕ => (M : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hk : Tendsto (fun M : ℕ => (M : ℝ) * ((1 + biasDelta M) / 2)) atTop atTop :=
    hm.atTop_mul_pos (by norm_num : (0 : ℝ) < (1 + 0) / 2)
      ((tendsto_const_nhds.add biasDelta_tendsto).div_const 2)
  have hl : Tendsto (fun M : ℕ => (M : ℝ) * ((1 - biasDelta M) / 2)) atTop atTop :=
    hm.atTop_mul_pos (by norm_num : (0 : ℝ) < (1 - 0) / 2)
      ((tendsto_const_nhds.sub biasDelta_tendsto).div_const 2)
  constructor
  · apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
    apply hk.congr'
    filter_upwards [bias_eventually] with M hM
    rw [(bias_indices M hM.1 hM.2.2.1).1]
    ring
  · apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
    apply hl.congr'
    filter_upwards [bias_eventually] with M hM
    rw [(bias_indices M hM.1 hM.2.2.1).2.1]
    ring

private lemma log_factorial_stirling (n : ℕ) (hn : 0 < n) :
    Real.log (n.factorial : ℝ) = Real.log (Stirling.stirlingSeq n) +
      (Real.log 2 + Real.log n) / 2 + (n : ℝ) * Real.log n - n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have h := Stirling.log_stirlingSeq_formula n
  rw [Real.log_mul (by norm_num) hn0, Real.log_div hn0 (Real.exp_ne_zero 1), Real.log_exp] at h
  linarith

private lemma log_scaled_probability (M : ℕ) (hM : 0 < M) (hB : 0 < promiseB M)
    (hBM : promiseB M < M) (hd : biasDelta M < 1 / 2)
    (hk : 0 < biasK M) (hl : 0 < biasL M) :
    Real.log ((M : ℝ) * probOf M (fun b => b ∈ promiseSet M)) =
      3 / 2 * Real.log 2 + Real.log (Stirling.stirlingSeq M) -
        Real.log (Stirling.stirlingSeq (biasK M)) - Real.log (Stirling.stirlingSeq (biasL M)) -
        (Real.log (1 + biasDelta M) + Real.log (1 - biasDelta M)) / 2 -
        ((M : ℝ) * biasEntropy (biasDelta M) - Real.log M) / 2 := by
  have hMn : (0 : ℝ) < M := by exact_mod_cast hM
  have hkn : (0 : ℝ) < biasK M := by exact_mod_cast hk
  have hln : (0 : ℝ) < biasL M := by exact_mod_cast hl
  have hi := bias_indices M hM hBM
  have hp : 0 < 1 + biasDelta M := by
    have hδ : 0 ≤ biasDelta M := by unfold biasDelta; positivity
    linarith
  have hm : 0 < 1 - biasDelta M := by linarith
  have hlogk : Real.log (biasK M) = Real.log M + Real.log (1 + biasDelta M) - Real.log 2 := by
    rw [hi.1, Real.log_div (by positivity) (by norm_num), Real.log_mul hMn.ne' hp.ne']
  have hlogl : Real.log (biasL M) = Real.log M + Real.log (1 - biasDelta M) - Real.log 2 := by
    rw [hi.2.1, Real.log_div (by positivity) (by norm_num), Real.log_mul hMn.ne' hm.ne']
  have hchoose : (0 : ℝ) < Nat.choose M (biasK M) := by
    exact_mod_cast (Nat.choose_pos hi.2.2)
  have hfact (n : ℕ) : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [probability_choose M hB]
  change Real.log ((M : ℝ) * (2 * (Nat.choose M (biasK M) : ℝ) / 2 ^ M)) = _
  rw [Real.log_mul hMn.ne' (by positivity), Real.log_div (by positivity) (by positivity),
    Real.log_mul (by norm_num) hchoose.ne', Real.log_pow, Nat.cast_choose ℝ hi.2.2,
    Real.log_div (hfact M).ne' (by positivity), Real.log_mul (hfact (biasK M)).ne'
      (hfact (M - biasK M)).ne']
  change Real.log M + (Real.log 2 +
    (Real.log (M.factorial : ℝ) -
      (Real.log ((biasK M).factorial : ℝ) + Real.log ((biasL M).factorial : ℝ))) -
      M * Real.log 2) = _
  rw [log_factorial_stirling M hM, log_factorial_stirling (biasK M) hk,
    log_factorial_stirling (biasL M) hl, hlogk, hlogl, hi.1, hi.2.1]
  unfold biasEntropy
  ring

private lemma log_scaled_probability_tendsto :
    Tendsto (fun M : ℕ => Real.log ((M : ℝ) * probOf M (fun b => b ∈ promiseSet M)))
      atTop (nhds (3 / 2 * Real.log 2 - Real.log (Real.sqrt Real.pi))) := by
  have hs := Stirling.tendsto_stirlingSeq_sqrt_pi
  have hslog := hs.log (show Real.sqrt Real.pi ≠ 0 by positivity)
  have hk := hslog.comp bias_indices_tendsto.1
  have hl := hslog.comp bias_indices_tendsto.2
  have hp : Tendsto (fun M => Real.log (1 + biasDelta M)) atTop (nhds 0) := by
    have h := (tendsto_const_nhds.add biasDelta_tendsto).log
      (by norm_num : (1 : ℝ) + 0 ≠ 0)
    simpa only [add_zero, Real.log_one] using h
  have hm : Tendsto (fun M => Real.log (1 - biasDelta M)) atTop (nhds 0) := by
    have h := (tendsto_const_nhds.sub biasDelta_tendsto).log
      (by norm_num : (1 : ℝ) - 0 ≠ 0)
    simpa only [sub_zero, Real.log_one] using h
  have h := ((((((tendsto_const_nhds (x := (3 / 2 * Real.log 2 : ℝ))).add hslog).sub hk).sub hl).sub
    ((hp.add hm).div_const 2)).sub (entropy_centered.div_const 2))
  have h' : Tendsto (fun M : ℕ => 3 / 2 * Real.log 2 + Real.log (Stirling.stirlingSeq M) -
      Real.log (Stirling.stirlingSeq (biasK M)) - Real.log (Stirling.stirlingSeq (biasL M)) -
      (Real.log (1 + biasDelta M) + Real.log (1 - biasDelta M)) / 2 -
      ((M : ℝ) * biasEntropy (biasDelta M) - Real.log M) / 2) atTop
      (nhds (3 / 2 * Real.log 2 - Real.log (Real.sqrt Real.pi))) := by
    have hlim : 3 / 2 * Real.log 2 + Real.log (Real.sqrt Real.pi) -
        Real.log (Real.sqrt Real.pi) - Real.log (Real.sqrt Real.pi) -
        (0 + 0) / 2 - 0 / 2 = 3 / 2 * Real.log 2 - Real.log (Real.sqrt Real.pi) := by ring
    simpa only [Function.comp_apply, hlim] using h
  apply h'.congr'
  filter_upwards [bias_eventually, bias_indices_tendsto.1.eventually_gt_atTop 0,
    bias_indices_tendsto.2.eventually_gt_atTop 0] with M hM hk hl
  exact (log_scaled_probability M hM.1 hM.2.1 hM.2.2.1 hM.2.2.2 hk hl).symm

/-- Lemma 4: the uniform sign-string promise set `promiseSet M` has probability
`Θ(1 / M)` as `M → ∞`. -/
theorem lemma4_promise_probability :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ M : ℕ in Filter.atTop,
      c₁ / (M : ℝ) ≤ probOf M (fun b => b ∈ promiseSet M) ∧
      probOf M (fun b => b ∈ promiseSet M) ≤ c₂ / (M : ℝ) := by
  let a : ℝ := 3 / 2 * Real.log 2 - Real.log (Real.sqrt Real.pi)
  let L : ℝ := Real.exp a
  have hL : 0 < L := Real.exp_pos a
  refine ⟨L / 2, 2 * L, by positivity, by positivity, ?_⟩
  have hexp : Tendsto (fun M : ℕ => Real.exp (Real.log ((M : ℝ) * probOf M (fun b => b ∈ promiseSet M))))
      atTop (nhds L) :=
    (Real.continuous_exp.tendsto a).comp log_scaled_probability_tendsto
  have hmem : Set.Icc (L / 2) (2 * L) ∈ nhds L :=
    Icc_mem_nhds (by linarith) (by linarith)
  filter_upwards [bias_eventually, hexp.eventually hmem] with M hM hbd
  have hMn : (0 : ℝ) < M := by exact_mod_cast hM.1
  have hi := bias_indices M hM.1 hM.2.2.1
  have hchoose : (0 : ℝ) < Nat.choose M (biasK M) := by exact_mod_cast Nat.choose_pos hi.2.2
  have hp_pos : 0 < (M : ℝ) * probOf M (fun b => b ∈ promiseSet M) := by
    rw [probability_choose M hM.2.1]
    exact mul_pos hMn (div_pos (mul_pos (by norm_num) hchoose) (by positivity))
  rw [Real.exp_log hp_pos] at hbd
  exact ⟨(div_le_iff₀ hMn).mpr (by linarith [hbd.1]),
    (le_div_iff₀ hMn).mpr (by linarith [hbd.2])⟩

end Qatlib.Papers.NonSparseHam09.MainResults
