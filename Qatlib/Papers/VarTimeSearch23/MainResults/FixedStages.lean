/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.VarTimeSearch23.MainResults.VtsStageModel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section


/-!
# Fixed-stage amplitude estimates

These conditional estimates preserve the analytical core of arXiv:2302.06749v3,
Eqs. (3.2)--(3.4). The hypotheses include the stage bookkeeping and the
Lemma 3 schedule inequalities. No checking-time algorithm or amplification
cost is asserted by this module.
-/

set_option autoImplicit false
noncomputable section
open Finset
open scoped BigOperators
namespace Qatlib.Papers.VarTimeSearch23.MainResults
open Qatlib.Papers.VarTimeSearch23.MainResults
open VtsStageRun
variable {n : ℕ}

/-- Source Eq. (3.2) trigonometric identity:
`sin(3α)/sin α = 3 − 4 sin² α` (for `sin α ≠ 0`). -/
theorem ratio_eq (R : VtsStageRun n) (j : ℕ) (h : Real.sin (R.alpha j) ≠ 0) :
    R.ratio j = 3 - 4 * (Real.sin (R.alpha j)) ^ 2 := by
  unfold VtsStageRun.ratio
  rw [Real.sin_three_mul]
  field_simp

/-- Source Eq. (3.2): the stage gain `sin(3α_j)/sin α_j` is at most `3`. -/
theorem ratio_le_three (R : VtsStageRun n) (j : ℕ)
    (h : Real.sin (R.alpha j) ≠ 0) :
    R.ratio j ≤ 3 := by
  rw [ratio_eq R j h]
  nlinarith [sq_nonneg (Real.sin (R.alpha j))]

/-- Source Eq. (3.2) used in (3.3): `(sin(3α_j)/sin α_j)² ≤ 9`. -/
theorem ratio_sq_le9 (R : VtsStageRun n) (j : ℕ)
    (h : Real.sin (R.alpha j) ≠ 0) :
    (R.ratio j) ^ 2 ≤ 9 := by
  rw [ratio_eq R j h]
  have h0 : 0 ≤ (Real.sin (R.alpha j)) ^ 2 := sq_nonneg _
  have h1 : (Real.sin (R.alpha j)) ^ 2 ≤ 1 := Real.sin_sq_le_one _
  have hs : (Real.sin (R.alpha j)) ^ 2 * (Real.sin (R.alpha j)) ^ 2
      ≤ (Real.sin (R.alpha j)) ^ 2 := by
    nlinarith [mul_nonneg h0 (show (0 : ℝ) ≤ 1 - (Real.sin (R.alpha j)) ^ 2 by linarith)]
  nlinarith

/-- Bound on the Lemma 2 product used in (3.3):
`∏_{k=1}^{j−1} (sin(3α_k)/sin α_k)² ≤ 9^{j−1}`. -/
theorem prod_sq_le9 (R : VtsStageRun n) (j : ℕ) (hj : 1 ≤ j)
    (hsin : ∀ k : ℕ, 1 ≤ k → Real.sin (R.alpha k) ≠ 0) :
    (R.paperProd j) ^ 2 ≤ (9 : ℝ) ^ (j - 1) := by
  induction j, hj using Nat.le_induction with
  | base =>
      rw [paperProd_one R]
      norm_num
  | succ j hj ih =>
      rw [paperProd_succ R j hj]
      have hsq : (R.ratio j) ^ 2 ≤ 9 := ratio_sq_le9 R j (hsin j hj)
      have hgoal : (9 : ℝ) ^ ((j + 1) - 1) = (9 : ℝ) ^ j := by
        rw [show j + 1 - 1 = j by omega]
      rw [hgoal]
      calc (R.paperProd j * R.ratio j) ^ 2
          = (R.paperProd j) ^ 2 * (R.ratio j) ^ 2 := by ring
        _ ≤ (9 : ℝ) ^ (j - 1) * 9 :=
              mul_le_mul ih hsq (sq_nonneg _) (by positivity)
        _ = (9 : ℝ) ^ j := by rw [← pow_succ, Nat.sub_add_cancel hj]

/-- Source Eq. (3.2) consequence used to expand (3.3):
`sin² α_j ≤ (s_j / n) · 9^{j−1}`. -/
theorem sin_sq_bound (R : VtsStageRun n) (j : ℕ) (hj : 1 ≤ j) (hn : 0 < n)
    (hsin : ∀ k : ℕ, 1 ≤ k → Real.sin (R.alpha k) ≠ 0) :
    (Real.sin (R.alpha j)) ^ 2
      ≤ ((R.S j).card : ℝ) / (n : ℝ) * (9 : ℝ) ^ (j - 1) := by
  rw [R.lemma2_angle_identity j hj]
  have hp := prod_sq_le9 R j hj hsin
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hc : (0 : ℝ) ≤ ((R.S j).card : ℝ) / (n : ℝ) :=
    div_nonneg (by positivity) (le_of_lt hn')
  exact mul_le_mul_of_nonneg_left hp hc

/-- Source Eq. (3.2)/(3.3) lower bound on the stage gain:
`sin(3α_j)/sin α_j ≥ 3 (1 − 4 s_j 9^j / (27 n))`. -/
theorem ratio_ge_C1 (R : VtsStageRun n) (j : ℕ) (hj : 1 ≤ j) (hn : 0 < n)
    (hsin : ∀ k : ℕ, 1 ≤ k → Real.sin (R.alpha k) ≠ 0) :
    R.ratio j
      ≥ 3 * (1 - 4 * ((R.S j).card : ℝ) / (27 * (n : ℝ)) * (9 : ℝ) ^ j) := by
  have hsinle := sin_sq_bound R j hj hn hsin
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h9 : (9 : ℝ) ^ j = (9 : ℝ) ^ (j - 1) * 9 := by
    rw [← pow_succ, Nat.sub_add_cancel hj]
  calc R.ratio j = 3 - 4 * (Real.sin (R.alpha j)) ^ 2 := ratio_eq R j (hsin j hj)
    _ ≥ 3 - 4 * (((R.S j).card : ℝ) / (n : ℝ) * (9 : ℝ) ^ (j - 1)) := by
          linarith [hsinle]
    _ = 3 * (1 - 4 * ((R.S j).card : ℝ) / (27 * (n : ℝ)) * (9 : ℝ) ^ j) := by
          rw [h9]
          field_simp [ne_of_gt hn']
          ring

/-- Monotone product inequality for nonnegative factors, used to compare the
lower-bound product of (3.3) with `∏_{j=1}^{ℓ−1} sin(3α_j)/sin α_j`.  This is
`Finset.prod_le_prod'` specialised to `ℝ`, where the bundled
`MulLeftMono ℝ` instance is not available in this Mathlib snapshot. -/
private lemma prod_mono {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f g : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hfa : f a ≤ g a := hfg a (Finset.mem_insert_self a s)
      have hft : ∀ i ∈ s, f i ≤ g i := fun i hi => hfg i (Finset.mem_insert_of_mem hi)
      have hf0 : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have ih' : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := ih hf0 hft
      have hp : (0 : ℝ) ≤ ∏ i ∈ s, f i := Finset.prod_nonneg hf0
      have hga : (0 : ℝ) ≤ g a := le_trans (hf a (Finset.mem_insert_self a s)) hfa
      exact mul_le_mul hfa ih' hp hga

/-- Source Eq. (3.3): the Lemma 2 product is bounded below by
`3^{ℓ−1} ∏_{j=1}^{ℓ−1} (1 − 4 s_j 9^j / (27 n))`, hence its square by
`9^{ℓ−1} (∏ (1 − ...))²`. -/
theorem prod_sq_lower (R : VtsStageRun n) (ell : ℕ)
    (hn : 0 < n) (hsin : ∀ k : ℕ, 1 ≤ k → Real.sin (R.alpha k) ≠ 0)
    (hC1 : ∀ j ∈ Finset.Icc 1 (ell - 1),
      (9 : ℝ) ^ j * ((R.S j).card : ℝ) / (n : ℝ) ≤ 9 / 4) :
    (R.paperProd ell) ^ 2
      ≥ (9 : ℝ) ^ (ell - 1) *
        (∏ j ∈ Finset.Icc 1 (ell - 1),
          (1 - 4 * ((R.S j).card : ℝ) / (27 * (n : ℝ)) * (9 : ℝ) ^ j)) ^ 2 := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set t : Finset ℕ := Finset.Icc 1 (ell - 1) with ht
  set Q : ℝ := ∏ j ∈ t,
    (1 - 4 * ((R.S j).card : ℝ) / (27 * (n : ℝ)) * (9 : ℝ) ^ j) with hQ
  have hxle : ∀ j ∈ t,
      4 * ((R.S j).card : ℝ) / (27 * (n : ℝ)) * (9 : ℝ) ^ j ≤ 1 / 3 := by
    intro j hj
    have hj' : j ∈ Finset.Icc 1 (ell - 1) := hj
    have h := hC1 j hj'
    have heq : 4 * ((R.S j).card : ℝ) / (27 * (n : ℝ)) * (9 : ℝ) ^ j
        = (4 / 27) * ((9 : ℝ) ^ j * ((R.S j).card : ℝ) / (n : ℝ)) := by
      field_simp [ne_of_gt hn']
    rw [heq]
    nlinarith
  have hf0 : ∀ j ∈ t, 0 ≤ 3 * (1 - 4 * ((R.S j).card : ℝ) / (27 * (n : ℝ))
      * (9 : ℝ) ^ j) := by
    intro j hj
    have := hxle j hj
    nlinarith
  have hfg : ∀ j ∈ t, 3 * (1 - 4 * ((R.S j).card : ℝ) / (27 * (n : ℝ))
      * (9 : ℝ) ^ j) ≤ R.ratio j := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    exact ratio_ge_C1 R j hj1 hn hsin
  have hprod_le : ∏ j ∈ t,
      3 * (1 - 4 * ((R.S j).card : ℝ) / (27 * (n : ℝ)) * (9 : ℝ) ^ j)
      ≤ ∏ j ∈ t, R.ratio j :=
    prod_mono t _ _ hf0 hfg
  have hprodratio : ∏ j ∈ t, R.ratio j = R.paperProd ell := by
    rw [show t = Finset.Icc 1 (ell - 1) from ht]
    rfl
  have hf_eq : ∏ j ∈ t,
      3 * (1 - 4 * ((R.S j).card : ℝ) / (27 * (n : ℝ)) * (9 : ℝ) ^ j)
      = (3 : ℝ) ^ (ell - 1) * Q := by
    have h3prod : (3 : ℝ) ^ (ell - 1) = ∏ j ∈ t, (3 : ℝ) := by
      rw [show t = Finset.Icc 1 (ell - 1) from ht, Finset.prod_const, Nat.card_Icc]
      congr 1
    rw [hQ, h3prod, ← Finset.prod_mul_distrib]
  have hQ0 : 0 ≤ Q := by
    rw [hQ]
    apply Finset.prod_nonneg
    intro j hj
    have := hxle j hj
    linarith
  have hnonneg : 0 ≤ ∏ j ∈ t,
      3 * (1 - 4 * ((R.S j).card : ℝ) / (27 * (n : ℝ)) * (9 : ℝ) ^ j) :=
    Finset.prod_nonneg hf0
  have hsq_le : (∏ j ∈ t,
      3 * (1 - 4 * ((R.S j).card : ℝ) / (27 * (n : ℝ)) * (9 : ℝ) ^ j)) ^ 2
      ≤ (R.paperProd ell) ^ 2 := by
    have := mul_self_le_mul_self hnonneg hprod_le
    simpa [pow_two, hprodratio] using this
  have hpow : ((3 : ℝ) ^ (ell - 1)) ^ 2 = (9 : ℝ) ^ (ell - 1) := by
    rw [← pow_mul, show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul,
      Nat.mul_comm (ell - 1) 2]
  calc (9 : ℝ) ^ (ell - 1) * Q ^ 2
      = ((3 : ℝ) ^ (ell - 1)) ^ 2 * Q ^ 2 := by rw [hpow]
    _ = (∏ j ∈ t,
          3 * (1 - 4 * ((R.S j).card : ℝ) / (27 * (n : ℝ)) * (9 : ℝ) ^ j)) ^ 2 := by
          rw [hf_eq]
          ring
    _ ≤ (R.paperProd ell) ^ 2 := hsq_le

/-- Eq. (3.4) of the source (p.6), the analytical core of Lemma 1: with
`ℓ = ⌈log₉(n/m)⌉` (encoded by `n ≤ 9^ℓ m`), C-1/C-2 of Lemma 3 and the
stage model of Lemma 2, the readout probability of the unaugmented procedure
`A` is at least `(8/9)(2/9)² = 32/729 > 0.04`. -/
theorem base_prob (R : VtsStageRun n) (ell m : ℕ) (hn : 0 < n)
    (hell : 1 ≤ ell)
    (hchoice : (n : ℝ) ≤ (9 : ℝ) ^ ell * (m : ℝ))
    (hsin : ∀ k : ℕ, 1 ≤ k → Real.sin (R.alpha k) ≠ 0)
    (hC1 : ∀ j ∈ Finset.Icc 1 (ell - 1),
      (9 : ℝ) ^ j * ((R.S j).card : ℝ) / (n : ℝ) ≤ 9 / 4)
    (hC2 : (2 : ℝ) / 3 ≤
      ∏ j ∈ Finset.Icc 1 (ell - 1),
        (1 - 4 * ((R.S j).card : ℝ) / (27 * (n : ℝ)) * (9 : ℝ) ^ j)) :
    (8 * (m : ℝ) / 9) * (Real.sin (R.alpha ell)) ^ 2
        / ((R.S ell).card : ℝ) ≥ 32 / 729 := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set s : ℝ := ((R.S ell).card : ℝ) with hs_def
  set P : ℝ := R.paperProd ell with hP_def
  set Q : ℝ := ∏ j ∈ Finset.Icc 1 (ell - 1),
    (1 - 4 * ((R.S j).card : ℝ) / (27 * (n : ℝ)) * (9 : ℝ) ^ j) with hQ_def
  have hs : 0 < s := by
    rw [hs_def]
    exact_mod_cast R.S_pos ell hell
  have hid' : (Real.sin (R.alpha ell)) ^ 2 = s / (n : ℝ) * P ^ 2 := by
    simpa [hs_def, hP_def] using R.lemma2_angle_identity ell hell
  have hP2' : (9 : ℝ) ^ (ell - 1) * Q ^ 2 ≤ P ^ 2 := by
    simpa [hP_def, hQ_def] using prod_sq_lower R ell hn hsin hC1
  have hQ0 : 0 ≤ Q := by
    rw [hQ_def]
    apply Finset.prod_nonneg
    intro j hj
    have hj' : j ∈ Finset.Icc 1 (ell - 1) := hj
    have h := hC1 j hj'
    have heq : 4 * ((R.S j).card : ℝ) / (27 * (n : ℝ)) * (9 : ℝ) ^ j
        = (4 / 27) * ((9 : ℝ) ^ j * ((R.S j).card : ℝ) / (n : ℝ)) := by
      field_simp [ne_of_gt hn']
    rw [heq]
    nlinarith
  have hQ2 : (4 : ℝ) / 9 ≤ Q ^ 2 := by
    have hQge : (2 : ℝ) / 3 ≤ Q := by
      rw [hQ_def]
      exact hC2
    nlinarith [hQ0, hQge, sq_nonneg (Q - 2 / 3)]
  have hm9 : (n : ℝ) ≤ (m : ℝ) * (9 : ℝ) ^ ell := by
    nlinarith [hchoice]
  have hmP : (4 : ℝ) / 81 * (n : ℝ) ≤ (m : ℝ) * P ^ 2 := by
    have h9e : (9 : ℝ) ^ (ell - 1) * 9 = (9 : ℝ) ^ ell := by
      rw [← pow_succ, Nat.sub_add_cancel hell]
    have hmul1 : (m : ℝ) * ((9 : ℝ) ^ (ell - 1) * Q ^ 2) ≤ (m : ℝ) * P ^ 2 :=
      mul_le_mul_of_nonneg_left hP2' (by positivity)
    have hrew : (m : ℝ) * ((9 : ℝ) ^ (ell - 1) * Q ^ 2)
        = ((m : ℝ) * (9 : ℝ) ^ ell / 9) * Q ^ 2 := by
      rw [← h9e]
      field_simp
    have hge1 : (n : ℝ) / 9 * Q ^ 2
        ≤ (m : ℝ) * ((9 : ℝ) ^ (ell - 1) * Q ^ 2) := by
      rw [hrew]
      have hcoef : (n : ℝ) / 9 ≤ (m : ℝ) * (9 : ℝ) ^ ell / 9 := by
        nlinarith [hm9]
      exact mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)
    have hge2 : (n : ℝ) / 9 * ((4 : ℝ) / 9)
        ≤ (n : ℝ) / 9 * Q ^ 2 :=
      mul_le_mul_of_nonneg_left hQ2 (by positivity)
    calc (4 : ℝ) / 81 * (n : ℝ) = (n : ℝ) / 9 * ((4 : ℝ) / 9) := by
          field_simp; ring
      _ ≤ (n : ℝ) / 9 * Q ^ 2 := hge2
      _ ≤ (m : ℝ) * ((9 : ℝ) ^ (ell - 1) * Q ^ 2) := hge1
      _ ≤ (m : ℝ) * P ^ 2 := hmul1
  have htarget : (32 : ℝ) / 729
      ≤ (8 * (m : ℝ) / 9) * (P ^ 2 / (n : ℝ)) := by
    have hdiv : (4 : ℝ) / 81 ≤ (m : ℝ) * P ^ 2 / (n : ℝ) := by
      rw [le_div_iff₀ hn']
      calc (4 : ℝ) / 81 * (n : ℝ) ≤ (m : ℝ) * P ^ 2 := hmP
        _ = (m : ℝ) * P ^ 2 := rfl
    have hmul2 : (8 : ℝ) / 9 * ((4 : ℝ) / 81)
        ≤ (8 : ℝ) / 9 * ((m : ℝ) * P ^ 2 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hdiv (by norm_num)
    have hconst : (8 : ℝ) / 9 * ((4 : ℝ) / 81) = 32 / 729 := by norm_num
    calc (32 : ℝ) / 729 = (8 : ℝ) / 9 * ((4 : ℝ) / 81) := hconst.symm
      _ ≤ (8 : ℝ) / 9 * ((m : ℝ) * P ^ 2 / (n : ℝ)) := hmul2
      _ = (8 * (m : ℝ) / 9) * (P ^ 2 / (n : ℝ)) := by
          field_simp
  have hstep1 : (8 * (m : ℝ) / 9) * (Real.sin (R.alpha ell)) ^ 2 / s
      = (8 * (m : ℝ) / 9) * (P ^ 2 / (n : ℝ)) := by
    rw [hid']
    field_simp [ne_of_gt hs, ne_of_gt hn']
  rw [hstep1]
  exact htarget

end Qatlib.Papers.VarTimeSearch23.MainResults
