/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSearchAdvice09.MainResults.AmpLaw
import Qatlib.Papers.QSearchAdvice09.MainResults.AmplifyCost
import Qatlib.Papers.QSearchAdvice09.MainResults.Basic
import Qatlib.Papers.QSearchAdvice09.MainResults.Prop32
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Pointwise Query Upper Bound for Quantum Search with Advice (Algorithm 3)

This module proves Proposition 3.2 of Montanaro: for growth factor $k = 1.162$, every domain
size $n > 0$, and every advice weight $0 < p_x < 1$, the expected query budget of Algorithm 3
is bounded simultaneously by the advice estimate $83/\sqrt{p_x} + 4/3$ and the worst-case
uniform-search estimate $53\sqrt{n}$.

## Main statements

* `prop_3_2`: Unconditional proof of `alg3QueryModel 1.162 px n ≤ min (83 / √px + 4 / 3) (53 * √n)`
  for all `0 < n` and `0 < px < 1`.

## References

* [Montanaro, 2011][Montanaro2011]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QSearchAdvice09.MainResults

open scoped BigOperators

private lemma amp_average (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (m : ℕ)
    (hm : 0 < m) :
    ampAvgSuccessProb p m = (1 / (m : ℝ)) *
      ∑ r ∈ Finset.range m,
        Real.sin ((2 * (r : ℝ) + 1) * Real.arcsin (Real.sqrt p)) ^ 2 := by
  have hs0 := Real.sqrt_pos.mpr hp0
  have hs1 : Real.sqrt p < 1 := by simpa using Real.sqrt_lt_sqrt hp0.le hp1
  have hsin : Real.sin (Real.arcsin (Real.sqrt p)) = Real.sqrt p :=
    Real.sin_arcsin (by linarith) hs1.le
  have hcos : Real.cos (Real.arcsin (Real.sqrt p)) = Real.sqrt (1 - p) := by
    rw [Real.cos_arcsin, Real.sq_sqrt hp0.le]
  have hc0 : 0 < Real.sqrt (1 - p) := Real.sqrt_pos.mpr (by linarith)
  have hprod : Real.sin (Real.arcsin (Real.sqrt p)) *
      Real.cos (Real.arcsin (Real.sqrt p)) = Real.sqrt (p * (1 - p)) := by
    rw [hsin, hcos, Real.sqrt_mul hp0.le]
  rw [average_amp_success _ m hm (by rw [hsin, hcos]; positivity)]
  unfold ampAvgSuccessProb
  rw [mul_assoc (8 * (m : ℝ)), hprod]

private lemma amp_probability (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (m : ℕ)
    (hm : 0 < m) : 0 ≤ ampAvgSuccessProb p m ∧ ampAvgSuccessProb p m ≤ 1 := by
  rw [amp_average p hp0 hp1 m hm]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · positivity
  · have hsum : (∑ r ∈ Finset.range m,
        Real.sin ((2 * (r : ℝ) + 1) * Real.arcsin (Real.sqrt p)) ^ 2) ≤ (m : ℝ) := by
      calc
        _ ≤ ∑ _r ∈ Finset.range m, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro r _
          nlinarith [Real.sin_sq_add_cos_sq
            ((2 * (r : ℝ) + 1) * Real.arcsin (Real.sqrt p)),
            sq_nonneg (Real.cos ((2 * (r : ℝ) + 1) * Real.arcsin (Real.sqrt p)))]
        _ = (m : ℝ) := by simp
    calc
      _ ≤ (1 / (m : ℝ)) * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 1 := by field_simp

private lemma amp_quarter (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (a : ℝ)
    (ha : 1 / Real.sqrt p ≤ a) (hm : 0 < ⌊a⌋₊) :
    1 / 4 ≤ ampAvgSuccessProb p ⌊a⌋₊ := by
  let θ := Real.arcsin (Real.sqrt p)
  let m := ⌊a⌋₊
  have hs0 := Real.sqrt_pos.mpr hp0
  have hs1 : Real.sqrt p < 1 := by simpa using Real.sqrt_lt_sqrt hp0.le hp1
  have hsin : Real.sin θ = Real.sqrt p := Real.sin_arcsin (by linarith) hs1.le
  have hθ0 : 0 < θ := Real.arcsin_pos.mpr hs0
  have hθ1 : θ < Real.pi / 2 := Real.arcsin_lt_pi_div_two.mpr hs1
  have hcos : Real.cos θ = Real.sqrt (1 - p) := by
    dsimp [θ]
    rw [Real.cos_arcsin, Real.sq_sqrt hp0.le]
  have hc0 : 0 < Real.cos θ := by rw [hcos]; positivity
  have hs : 0 < Real.sin θ := by rw [hsin]; exact hs0
  have hsc : 0 < Real.sin θ * Real.cos θ := mul_pos hs hc0
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hformula : ampAvgSuccessProb p m =
      1 / 2 - Real.sin (4 * (m : ℝ) * θ) /
        (8 * (m : ℝ) * Real.sin θ * Real.cos θ) := by
    rw [amp_average p hp0 hp1 m hm, average_amp_success θ m hm hsc.ne']
  by_cases hlarge : 1 ≤ 2 * (m : ℝ) * (Real.sin θ * Real.cos θ)
  · rw [amp_average p hp0 hp1 m hm]
    exact average_amp_success_ge_quarter θ m hm hsc hlarge
  have hsmall : 2 * (m : ℝ) * (Real.sin θ * Real.cos θ) < 1 := lt_of_not_ge hlarge
  have hfloor : a < (m : ℝ) + 1 := Nat.lt_floor_add_one a
  by_cases hm1 : m = 1
  · have ha2 : 1 / Real.sqrt p < 2 := by
      simpa only [hm1, Nat.cast_one, one_add_one_eq_two] using ha.trans_lt hfloor
    have hs2 : 1 / 2 < Real.sqrt p := by
      have := (div_lt_iff₀ hs0).mp ha2
      linarith only [this]
    rw [amp_average p hp0 hp1 m hm]
    simp only [hm1, Finset.sum_range_one, Nat.cast_zero, mul_zero, zero_add, one_mul,
      Nat.cast_one, div_one]
    change 1 / 4 ≤ Real.sin θ ^ 2
    rw [hsin, Real.sq_sqrt hp0.le]
    nlinarith only [Real.sq_sqrt hp0.le, hs2]
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
  have has : 1 ≤ a * Real.sin θ := by
    rw [hsin]
    exact (div_le_iff₀ hs0).mp ha
  have hms : 2 / 3 < (m : ℝ) * Real.sin θ := by
    have hmul := mul_lt_mul_of_pos_right hfloor hs
    nlinarith only [has, hmul, mul_le_mul_of_nonneg_right hm2 hs.le]
  have hc34 : Real.cos θ < 3 / 4 := by
    nlinarith only [hsmall, mul_lt_mul_of_pos_right hms hc0]
  have hsq := Real.sin_sq_add_cos_sq θ
  have hs35 : 3 / 5 < Real.sin θ := by
    nlinarith only [hsq, hs, mul_self_lt_mul_self hc0.le hc34]
  have hmc56 : (m : ℝ) * Real.cos θ < 5 / 6 := by
    nlinarith only [hsmall, mul_lt_mul_of_pos_right hs35 (mul_pos hm0 hc0)]
  have hc512 : Real.cos θ < 5 / 12 := by
    nlinarith only [hmc56, mul_le_mul_of_nonneg_right hm2 hc0.le]
  have hs910 : 9 / 10 < Real.sin θ := by
    nlinarith only [hsq, hs, mul_self_lt_mul_self hc0.le hc512]
  have hmc59 : (m : ℝ) * Real.cos θ < 5 / 9 := by
    nlinarith only [hsmall, mul_lt_mul_of_pos_right hs910 (mul_pos hm0 hc0)]
  let φ := Real.pi / 2 - θ
  have hφ0 : 0 < φ := by dsimp [φ]; linarith
  have hφpi : φ < Real.pi / 2 := by dsimp [φ]; linarith
  have hφsin : Real.sin φ = Real.cos θ := Real.sin_pi_div_two_sub θ
  have hφhalf : φ < 1 / 2 := by
    by_contra! h
    have hmono := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ (1 / 2 : ℝ)) hφpi.le h
    have hbound := Real.sin_gt_sub_cube (by norm_num : (0 : ℝ) < 1 / 2)
    rw [hφsin] at hmono
    norm_num at hbound
    linarith only [hbound, hmono, hc512]
  have hφlower : (15 / 16) * φ < Real.sin φ := by
    have hcube : φ ^ 3 < φ / 4 := by
      have hsqφ := mul_self_lt_mul_self hφ0.le hφhalf
      nlinarith only [mul_lt_mul_of_pos_right hsqφ hφ0]
    linarith only [hφ0, hcube, Real.sin_gt_sub_cube hφ0]
  have hangle0 : 0 < 4 * (m : ℝ) * φ := by positivity
  have hanglepi : 4 * (m : ℝ) * φ < Real.pi := by
    have hmul := mul_lt_mul_of_pos_left hφlower hm0
    rw [hφsin] at hmul
    nlinarith only [hmul, hmc59, Real.pi_gt_three]
  have hneg : Real.sin (4 * (m : ℝ) * θ) < 0 := by
    have heq : 4 * (m : ℝ) * θ =
        ((2 * m : ℕ) : ℝ) * Real.pi - 4 * (m : ℝ) * φ := by
      dsimp [φ]
      push_cast
      ring
    rw [heq, Real.sin_nat_mul_pi_sub, pow_mul]
    norm_num
    exact Real.sin_pos_of_pos_of_lt_pi hangle0 hanglepi
  rw [hformula]
  have hden : 0 < 8 * (m : ℝ) * Real.sin θ * Real.cos θ := by positivity
  have := div_neg_of_neg_of_pos hneg hden
  linarith

private lemma round_nonneg (j : ℕ) : 0 ≤ roundCost algThreeK j := by
  unfold roundCost
  exact Finset.sum_nonneg fun _ _ => by positivity

private lemma round_mono : Monotone (roundCost algThreeK) := by
  intro a b hab
  unfold roundCost
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab)
    (fun _ _ _ => by positivity)

private def finiteBudget (P : ℕ → ℝ) (M : ℕ) (b : ℝ) : ℝ :=
  (∑ j ∈ Finset.range M, (∏ i ∈ Finset.range j, (1 - P i)) * P j *
      roundCost algThreeK (j + 1)) +
    (∏ i ∈ Finset.range M, (1 - P i)) * (roundCost algThreeK M + b)

private lemma first_success_total (P : ℕ → ℝ) (M : ℕ) :
    (∑ j ∈ Finset.range M, (∏ i ∈ Finset.range j, (1 - P i)) * P j) +
      (∏ i ∈ Finset.range M, (1 - P i)) = 1 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.prod_range_succ]
    nlinarith [ih]

private lemma finite_budget_le (P : ℕ → ℝ) (hP0 : ∀ i, 0 ≤ P i)
    (hP1 : ∀ i, P i ≤ 1) (M : ℕ) (b : ℝ) (hb : 0 ≤ b) :
    finiteBudget P M b ≤ roundCost algThreeK M + b := by
  have hterm : ∀ j ∈ Finset.range M,
      (∏ i ∈ Finset.range j, (1 - P i)) * P j * roundCost algThreeK (j + 1) ≤
        (∏ i ∈ Finset.range j, (1 - P i)) * P j * (roundCost algThreeK M + b) := by
    intro j hj
    apply mul_le_mul_of_nonneg_left
    · exact (round_mono (Finset.mem_range.mp hj)).trans (le_add_of_nonneg_right hb)
    · exact mul_nonneg (Finset.prod_nonneg fun i _ => sub_nonneg.mpr (hP1 i)) (hP0 j)
  unfold finiteBudget
  calc
    _ ≤ (∑ j ∈ Finset.range M, (∏ i ∈ Finset.range j, (1 - P i)) * P j *
        (roundCost algThreeK M + b)) +
        (∏ i ∈ Finset.range M, (1 - P i)) * (roundCost algThreeK M + b) :=
      add_le_add (Finset.sum_le_sum hterm) le_rfl
    _ = 1 * (roundCost algThreeK M + b) := by
      rw [← Finset.sum_mul, ← add_mul, first_success_total]
    _ = _ := one_mul _

private lemma finite_budget_tail (P : ℕ → ℝ) (hP0 : ∀ i, 0 ≤ P i)
    (hP1 : ∀ i, P i ≤ 1) (j0 M : ℕ) (hj : j0 ≤ M)
    (hquarter : ∀ i, j0 ≤ i → 1 / 4 ≤ P i) (b : ℝ)
    (hb : b ≤ Real.pi / 4 * algThreeK ^ M) :
    finiteBudget P M b ≤
      (1 / (algThreeK - 1) +
        4 * algThreeK / ((algThreeK - 1) * (4 - 3 * algThreeK)) +
        (1 / (algThreeK - 1) + Real.pi / 4)) * algThreeK ^ j0 := by
  have hk0 : 0 < algThreeK := by norm_num [algThreeK]
  have hd : 0 < algThreeK - 1 := sub_pos.mpr algThreeK_bounds.1
  let s := M - j0
  have hM : M = j0 + s := (Nat.add_sub_of_le hj).symm
  let C := algThreeK * algThreeK ^ j0 / (algThreeK - 1)
  let q := (3 / 4 : ℝ) * algThreeK
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by dsimp [q]; nlinarith [algThreeK_bounds.2]
  have hprod0 (j : ℕ) : 0 ≤ ∏ i ∈ Finset.range j, (1 - P i) :=
    Finset.prod_nonneg fun i _ => sub_nonneg.mpr (hP1 i)
  have hprefix : (∑ j ∈ Finset.range j0,
      (∏ i ∈ Finset.range j, (1 - P i)) * P j * roundCost algThreeK (j + 1)) ≤
        algThreeK ^ j0 / (algThreeK - 1) := by
    calc
      _ ≤ ∑ j ∈ Finset.range j0, (∏ i ∈ Finset.range j, (1 - P i)) * P j *
          (algThreeK ^ j0 / (algThreeK - 1)) := by
        apply Finset.sum_le_sum
        intro j hj'
        exact mul_le_mul_of_nonneg_left
          ((round_mono (Finset.mem_range.mp hj')).trans (roundCost_le j0))
          (mul_nonneg (hprod0 j) (hP0 j))
      _ = (∑ j ∈ Finset.range j0, (∏ i ∈ Finset.range j, (1 - P i)) * P j) *
          (algThreeK ^ j0 / (algThreeK - 1)) := (Finset.sum_mul ..).symm
      _ ≤ 1 * (algThreeK ^ j0 / (algThreeK - 1)) :=
        mul_le_mul_of_nonneg_right (first_success_sum_le_one P hP0 hP1 j0) (by positivity)
      _ = _ := one_mul _
  have htailterm (t : ℕ) :
      (∏ i ∈ Finset.range (j0 + t), (1 - P i)) * P (j0 + t) *
        roundCost algThreeK (j0 + t + 1) ≤ C * q ^ t := by
    have hprod := prod_decay P hP0 hP1 j0 hquarter (j0 + t) (by omega)
    rw [Nat.add_sub_cancel_left] at hprod
    calc
      _ ≤ (3 / 4 : ℝ) ^ t * 1 * roundCost algThreeK (j0 + t + 1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul hprod (hP1 _) (hP0 _) (by positivity)) (round_nonneg _)
      _ ≤ (3 / 4 : ℝ) ^ t * 1 *
          (algThreeK ^ (j0 + t + 1) / (algThreeK - 1)) :=
        mul_le_mul_of_nonneg_left (roundCost_le _) (by positivity)
      _ = C * q ^ t := by dsimp [C, q]; rw [pow_succ, pow_add, mul_pow]; ring
  have hgeom : (∑ t ∈ Finset.range s, q ^ t) ≤ 4 / (4 - 3 * algThreeK) := by
    rw [geom_sum_eq (ne_of_lt hq1)]
    have heq : (q ^ s - 1) / (q - 1) = (1 - q ^ s) / (1 - q) := by
      field_simp [sub_ne_zero.mpr hq1.ne, sub_ne_zero.mpr hq1.ne']
      ring
    rw [heq]
    calc
      _ ≤ 1 / (1 - q) :=
        (div_le_div_iff_of_pos_right (sub_pos.mpr hq1)).mpr
          (by linarith only [pow_nonneg hq0 s])
      _ = _ := by norm_num [q, algThreeK]
  have htail : (∑ t ∈ Finset.range s,
      (∏ i ∈ Finset.range (j0 + t), (1 - P i)) * P (j0 + t) *
        roundCost algThreeK (j0 + t + 1)) ≤ C * (4 / (4 - 3 * algThreeK)) := by
    calc
      _ ≤ ∑ t ∈ Finset.range s, C * q ^ t :=
        Finset.sum_le_sum fun t _ => htailterm t
      _ = C * ∑ t ∈ Finset.range s, q ^ t := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hgeom hC
  have hres : (∏ i ∈ Finset.range M, (1 - P i)) * (roundCost algThreeK M + b) ≤
      (1 / (algThreeK - 1) + Real.pi / 4) * algThreeK ^ j0 := by
    have hcost : roundCost algThreeK M + b ≤
        (1 / (algThreeK - 1) + Real.pi / 4) * algThreeK ^ M := by
      have := add_le_add (roundCost_le M) hb
      convert this using 1
      ring
    have hdecay := prod_decay P hP0 hP1 j0 hquarter M hj
    calc
      _ ≤ (∏ i ∈ Finset.range M, (1 - P i)) *
          ((1 / (algThreeK - 1) + Real.pi / 4) * algThreeK ^ M) :=
        mul_le_mul_of_nonneg_left hcost (hprod0 M)
      _ ≤ (3 / 4 : ℝ) ^ s *
          ((1 / (algThreeK - 1) + Real.pi / 4) * algThreeK ^ M) :=
        mul_le_mul_of_nonneg_right hdecay (by positivity)
      _ = ((1 / (algThreeK - 1) + Real.pi / 4) * algThreeK ^ j0) * q ^ s := by
        rw [hM, pow_add]
        dsimp [q]
        rw [mul_pow]
        ring
      _ ≤ ((1 / (algThreeK - 1) + Real.pi / 4) * algThreeK ^ j0) * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hq0 hq1.le) (by positivity)
      _ = _ := mul_one _
  unfold finiteBudget
  rw [hM, Finset.sum_range_add]
  rw [← hM]
  have := add_le_add (add_le_add hprefix htail) hres
  convert this using 1
  dsimp [C]
  field_simp

/-- **Proposition 3.2** [Montanaro2011]: the expected Algorithm 3 query budget with growth factor
`1.162` is bounded by `min (83 / √px + 4 / 3) (53 * √n)` for all `n > 0` and `0 < px < 1`. -/
theorem prop_3_2 (n : ℕ) (hn : 0 < n) (px : ℝ) (hpx0 : 0 < px) (hpx1 : px < 1) :
    alg3QueryModel 1.162 px n ≤ min (83 / Real.sqrt px + 4 / 3) (53 * Real.sqrt (n : ℝ)) := by
  have hknum : (1.162 : ℝ) = algThreeK := by norm_num [algThreeK]
  rw [hknum]
  have hk1 := algThreeK_bounds.1
  have hk0 : 0 < algThreeK := by linarith
  have hd : 0 < algThreeK - 1 := sub_pos.mpr hk1
  have hs0 : 0 < Real.sqrt px := Real.sqrt_pos.mpr hpx0
  have hs1 : Real.sqrt px < 1 := by simpa using Real.sqrt_lt_sqrt hpx0.le hpx1
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnS1 : 1 ≤ Real.sqrt (n : ℝ) := by simpa using Real.sqrt_le_sqrt hn1
  have hnS0 : 0 < Real.sqrt (n : ℝ) := by linarith
  let J := ⌊Real.logb algThreeK (Real.sqrt (n : ℝ))⌋₊
  let P := fun i : ℕ => ampAvgSuccessProb px ⌊algThreeK ^ i⌋₊
  have hm (i : ℕ) : 0 < ⌊algThreeK ^ i⌋₊ :=
    Nat.floor_pos.mpr (one_le_pow₀ hk1.le)
  have hP0 (i : ℕ) : 0 ≤ P i := (amp_probability px hpx0 hpx1 _ (hm i)).1
  have hP1 (i : ℕ) : P i ≤ 1 := (amp_probability px hpx0 hpx1 _ (hm i)).2
  have hlog0 : 0 ≤ Real.logb algThreeK (Real.sqrt (n : ℝ)) :=
    Real.logb_nonneg hk1 hnS1
  have hlogpow : algThreeK ^ Real.logb algThreeK (Real.sqrt (n : ℝ)) =
      Real.sqrt (n : ℝ) := Real.rpow_logb hk0 hk1.ne' hnS0
  have hJ : algThreeK ^ J ≤ Real.sqrt (n : ℝ) := by
    calc
      _ = algThreeK ^ (J : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ algThreeK ^ Real.logb algThreeK (Real.sqrt (n : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hk1.le (Nat.floor_le hlog0)
      _ = _ := hlogpow
  have hJnext : Real.sqrt (n : ℝ) < algThreeK ^ (J + 1) := by
    calc
      _ = algThreeK ^ Real.logb algThreeK (Real.sqrt (n : ℝ)) := hlogpow.symm
      _ < algThreeK ^ ((J : ℝ) + 1) :=
        Real.rpow_lt_rpow_of_exponent_lt hk1 (Nat.lt_floor_add_one _)
      _ = _ := by rw [← Nat.cast_one, ← Nat.cast_add, Real.rpow_natCast]
  change finiteBudget P (J + 1) (Real.pi / 4 * Real.sqrt (n : ℝ)) ≤ _
  have hbasic := finite_budget_le P hP0 hP1 (J + 1)
    (Real.pi / 4 * Real.sqrt (n : ℝ)) (by positivity)
  apply le_min
  · have hx : 1 ≤ 1 / Real.sqrt px := (le_div_iff₀ hs0).mpr (by linarith)
    obtain ⟨l, hl0, hl1⟩ := exists_nat_pow_near hx hk1
    let j0 := l + 1
    have hj0 : algThreeK ^ j0 ≤ algThreeK / Real.sqrt px := by
      calc
        _ = algThreeK ^ l * algThreeK := pow_succ _ _
        _ ≤ (1 / Real.sqrt px) * algThreeK := mul_le_mul_of_nonneg_right hl0 hk0.le
        _ = _ := by ring
    have hquarter (i : ℕ) (hi : j0 ≤ i) : 1 / 4 ≤ P i := by
      apply amp_quarter px hpx0 hpx1 (algThreeK ^ i) _ (hm i)
      exact hl1.le.trans (pow_le_pow_right₀ hk1.le hi)
    by_cases hbefore : J + 1 ≤ j0
    · have hpow : algThreeK ^ (J + 1) ≤ algThreeK / Real.sqrt px :=
        (pow_le_pow_right₀ hk1.le hbefore).trans hj0
      have hb : Real.pi / 4 * Real.sqrt (n : ℝ) ≤
          Real.pi / 4 * (algThreeK / Real.sqrt px) :=
        mul_le_mul_of_nonneg_left (hJnext.le.trans hpow) (by positivity)
      have hcost : roundCost algThreeK (J + 1) ≤
          (algThreeK / Real.sqrt px) / (algThreeK - 1) :=
        (roundCost_le _).trans (div_le_div_of_nonneg_right hpow hd.le)
      have hcoef : algThreeK / (algThreeK - 1) + algThreeK * Real.pi / 4 ≤ 83 := by
        norm_num [algThreeK]
        nlinarith only [Real.pi_lt_d4]
      calc
        _ ≤ (algThreeK / Real.sqrt px) / (algThreeK - 1) +
            Real.pi / 4 * (algThreeK / Real.sqrt px) := hbasic.trans (add_le_add hcost hb)
        _ = (algThreeK / (algThreeK - 1) + algThreeK * Real.pi / 4) / Real.sqrt px := by ring
        _ ≤ 83 / Real.sqrt px := div_le_div_of_nonneg_right hcoef hs0.le
        _ ≤ _ := by linarith
    · have hj : j0 ≤ J + 1 := by omega
      have htail := finite_budget_tail P hP0 hP1 j0 (J + 1) hj hquarter
        (Real.pi / 4 * Real.sqrt (n : ℝ))
        (mul_le_mul_of_nonneg_left hJnext.le (by positivity))
      let A := 1 / (algThreeK - 1) +
        4 * algThreeK / ((algThreeK - 1) * (4 - 3 * algThreeK)) +
        (1 / (algThreeK - 1) + Real.pi / 4)
      have hA : 0 ≤ A := by dsimp [A]; norm_num [algThreeK]; positivity
      have hcoef : A * algThreeK ≤ 83 := by
        dsimp [A]
        norm_num [algThreeK]
        nlinarith only [Real.pi_lt_d4]
      calc
        _ ≤ A * algThreeK ^ j0 := htail
        _ ≤ A * (algThreeK / Real.sqrt px) := mul_le_mul_of_nonneg_left hj0 hA
        _ = (A * algThreeK) / Real.sqrt px := by ring
        _ ≤ 83 / Real.sqrt px := div_le_div_of_nonneg_right hcoef hs0.le
        _ ≤ _ := by linarith
  · have hsum : roundCost algThreeK (J + 1) ≤
        ∑ j ∈ Finset.range (J + 1), roundCost algThreeK (j + 1) :=
      Finset.single_le_sum (fun j _ => round_nonneg (j + 1))
        (Finset.mem_range.mpr (Nat.lt_succ_self J))
    exact hbasic.trans ((add_le_add hsum le_rfl).trans (worstCase_const53 n J hJ))

end Qatlib.Papers.QSearchAdvice09.MainResults
