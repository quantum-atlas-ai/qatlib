/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem5AltAux
import Mathlib.Analysis.Complex.ExponentialBounds
import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem6Aux2
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option backward.isDefEq.respectTransparency false


namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis

open Set MeasureTheory
set_option warningAsError false

theorem taylorExp_iteratedDeriv (z : ℂ) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => Complex.exp (t * z)) =
      fun t : ℝ => z ^ n * Complex.exp (t * z) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have hd : HasDerivAt (fun t : ℝ => Complex.exp (t * z))
        (Complex.exp (t * z) * z) t := by
      simpa using! ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const z).cexp
    rw [(hd.const_mul (z ^ n)).deriv]
    simp only [pow_succ]
    ring

theorem taylorExp_within (z : ℂ) (k : ℕ) :
    taylorWithinEval (fun t : ℝ => Complex.exp (t * z)) k (Icc 0 1) 0 1 =
      taylorPoly k z := by
  rw [taylor_within_apply, taylorPoly]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : ContDiff ℝ j (fun t : ℝ => Complex.exp (t * z)) :=
    Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
    hc.contDiffAt (by simp), taylorExp_iteratedDeriv]
  simp [Complex.real_smul, div_eq_mul_inv, mul_comm]

theorem taylorPoly_defect_halfPlane (k : ℕ) (z : ℂ) (hre : z.re ≤ 0) :
    ‖Complex.exp z - taylorPoly k z‖ ≤
      ‖z‖ ^ (k + 1) / (Nat.factorial (k + 1) : ℝ) := by
  have hc : ContDiff ℝ (k + 1) (fun t : ℝ => Complex.exp (t * z)) :=
    Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.mul contDiff_const)
  have heq := taylor_integral_remainder (x₀ := 0) (x := 1) hc.contDiffOn
  rw [show Set.uIcc (0 : ℝ) 1 = Icc 0 1 from Set.uIcc_of_le (by norm_num),
    taylorExp_within] at heq
  simp only [Complex.ofReal_one, one_mul] at heq
  rw [heq]
  refine le_trans (intervalIntegral.norm_integral_le_of_norm_le (a := (0 : ℝ)) (b := 1)
    (f := fun t : ℝ => ((1 - t) ^ k / (Nat.factorial k : ℝ)) •
      iteratedDerivWithin (k + 1) (fun u : ℝ => Complex.exp (u * z)) (Icc 0 1) t)
    (g := fun t : ℝ => ((1 - t) ^ k / (Nat.factorial k : ℝ)) * ‖z‖ ^ (k + 1))
    (by norm_num) ?_ ?_) ?_
  · filter_upwards [] with t ht
    have ht1 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num))
      hc.contDiffAt ⟨ht.1.le, ht.2⟩, taylorExp_iteratedDeriv,
      norm_smul, norm_mul, norm_pow, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (1 - t) ^ k / (Nat.factorial k : ℝ))]
    have hexp : ‖Complex.exp ((t : ℂ) * z)‖ ≤ 1 := by
      apply complex_norm_exp_le_one
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_nonpos_of_nonneg_of_nonpos ht.1.le hre
    exact mul_le_mul_of_nonneg_left
      (by simpa using! mul_le_mul_of_nonneg_left hexp (pow_nonneg (norm_nonneg z) (k + 1)))
      (by positivity)
  · exact ((continuous_const.sub continuous_id).pow k |>.div_const _ |>.mul continuous_const).intervalIntegrable _ _
  · apply le_of_eq
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_div,
      intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ k) 1]
    simp only [sub_self, sub_zero, integral_pow, zero_pow (by omega : k + 1 ≠ 0),
      one_pow, sub_zero]
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp

theorem taylorPoly_le (k : ℕ) (z : ℂ) (h1 : ‖z‖ ≤ 1) (hre : z.re ≤ 0) :
    ‖taylorPoly k z‖ ≤ 1 + 1 / (Nat.factorial (k + 1) : ℝ) := by
  have hdef := taylorPoly_defect_halfPlane k z hre
  have hp : ‖z‖ ^ (k + 1) ≤ 1 := pow_le_one₀ (norm_nonneg z) h1
  have hexp := complex_norm_exp_le_one z hre
  have htri := norm_sub_le (Complex.exp z) (Complex.exp z - taylorPoly k z)
  rw [sub_sub_cancel] at htri
  have htail : ‖Complex.exp z - taylorPoly k z‖ ≤ 1 / (Nat.factorial (k + 1) : ℝ) :=
    hdef.trans (div_le_div_of_nonneg_right hp (by positivity))
  linarith

theorem taylorTransPoly_mul_pow {k b : ℕ} (hb : 1 ≤ b) (hbk : b ≤ k) (z : ℂ) :
    z ^ b * taylorTransPoly k b z =
      (Nat.factorial b : ℂ) * (taylorPoly k z - taylorPoly (b - 1) z) := by
  have hset : Finset.Icc b k = Finset.Ico b (k + 1) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hsum : taylorPoly k z - taylorPoly (b - 1) z =
      ∑ j ∈ Finset.Icc b k, z ^ j / (Nat.factorial j : ℂ) := by
    rw [taylorPoly, taylorPoly, show b - 1 + 1 = b from by omega, hset,
      Finset.sum_Ico_eq_sub _ (by omega)]
  rw [hsum, taylorTransPoly, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjb : b ≤ j := (Finset.mem_Icc.mp hj).1
  have hp : z ^ b * z ^ (j - b) = z ^ j := by
    rw [← pow_add, Nat.add_sub_of_le hjb]
  calc z ^ b * ((Nat.factorial b : ℂ) * z ^ (j - b) / (Nat.factorial j : ℂ))
      = (Nat.factorial b : ℂ) * (z ^ b * z ^ (j - b)) / (Nat.factorial j : ℂ) := by ring
    _ = (Nat.factorial b : ℂ) * (z ^ j / (Nat.factorial j : ℂ)) := by rw [hp]; ring

theorem taylorTransPoly_le {k b : ℕ} (hb : 1 ≤ b) (hbk : b ≤ k)
    (z : ℂ) (h1 : ‖z‖ ≤ 1) (hre : z.re ≤ 0) :
    ‖taylorTransPoly k b z‖ ≤ 1 + (Nat.factorial b : ℝ) / (Nat.factorial (k + 1) : ℝ) := by
  by_cases hz : z = 0
  · subst z
    have heq : taylorTransPoly k b 0 = 1 := by
      rw [taylorTransPoly]
      rw [Finset.sum_eq_single b]
      · simp [Nat.factorial_ne_zero]
      · intro j hj hne
        have hjb : b < j := by have := (Finset.mem_Icc.mp hj).1; omega
        simp [zero_pow (by omega : j - b ≠ 0)]
      · simp [hbk]
    rw [heq]
    simp only [norm_one]
    exact le_add_of_nonneg_right (by positivity)
  have hzpos : 0 < ‖z‖ ^ b := pow_pos (norm_pos_iff.mpr hz) b
  have hF : (0 : ℝ) < (Nat.factorial (k + 1) : ℝ) := by positivity
  have hFb : (0 : ℝ) < (Nat.factorial b : ℝ) := by positivity
  have hsmall := taylorPoly_defect_halfPlane (b - 1) z hre
  rw [show b - 1 + 1 = b from by omega] at hsmall
  have hbig := taylorPoly_defect_halfPlane k z hre
  have hp : ‖z‖ ^ (k + 1) ≤ ‖z‖ ^ b := by
    rw [show k + 1 = b + (k + 1 - b) from by omega, pow_add]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg z) h1)
  have hnorm : ‖z‖ ^ b * ‖taylorTransPoly k b z‖ =
      (Nat.factorial b : ℝ) * ‖taylorPoly k z - taylorPoly (b - 1) z‖ := by
    have := congrArg norm (taylorTransPoly_mul_pow hb hbk z)
    simpa only [norm_mul, norm_pow, Complex.norm_natCast] using! this
  have htri : ‖taylorPoly k z - taylorPoly (b - 1) z‖ ≤
      ‖Complex.exp z - taylorPoly k z‖ + ‖Complex.exp z - taylorPoly (b - 1) z‖ := by
    have := norm_sub_le (Complex.exp z - taylorPoly (b - 1) z)
      (Complex.exp z - taylorPoly k z)
    convert! this using 1 <;> abel
  have hle : ‖z‖ ^ b * ‖taylorTransPoly k b z‖ ≤
      ‖z‖ ^ b * (1 + (Nat.factorial b : ℝ) / (Nat.factorial (k + 1) : ℝ)) := by
    rw [hnorm]
    calc (Nat.factorial b : ℝ) * ‖taylorPoly k z - taylorPoly (b - 1) z‖
        ≤ (Nat.factorial b : ℝ) * (‖z‖ ^ b / (Nat.factorial (k + 1) : ℝ) +
          ‖z‖ ^ b / (Nat.factorial b : ℝ)) := by
          gcongr
          exact htri.trans (add_le_add (hbig.trans (div_le_div_of_nonneg_right hp hF.le)) hsmall)
      _ = _ := by field_simp; ring
  nlinarith [hle]

theorem taylorTransPoly_uniform {k b : ℕ} (hk : 5 ≤ k) (hb : 1 ≤ b) (hbk : b ≤ k)
    (z : ℂ) (h1 : ‖z‖ ≤ 1) (hre : z.re ≤ 0) :
    ‖taylorTransPoly k b z‖ ≤ 31 / 30 := by
  by_cases he : b = k
  · subst b
    norm_num [taylorTransPoly, Nat.factorial_ne_zero]
  have hbprev : b ≤ k - 1 := by omega
  have hstep : Nat.factorial (k + 1) = (k + 1) * k * Nat.factorial (k - 1) := by
    have hf : Nat.factorial k = k * Nat.factorial (k - 1) := by
      have := Nat.factorial_succ (k - 1)
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using! this
    rw [Nat.factorial_succ, hf]
    ring
  have hf : (Nat.factorial b : ℝ) ≤ (Nat.factorial (k - 1) : ℝ) := by
    exact_mod_cast Nat.factorial_le hbprev
  have hkR : (5 : ℝ) ≤ k := by exact_mod_cast hk
  have hratio : (Nat.factorial b : ℝ) / (Nat.factorial (k + 1) : ℝ) ≤ 1 / 30 := by
    rw [div_le_div_iff₀ (by positivity : 0 < (Nat.factorial (k + 1) : ℝ)) (by norm_num)]
    rw [hstep, Nat.cast_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hprod : (30 : ℝ) ≤ ((k : ℝ) + 1) * k := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hprod
      (by positivity : 0 ≤ (Nat.factorial (k - 1) : ℝ))
    nlinarith
  have hbound := taylorTransPoly_le hb hbk z h1 hre
  linarith

theorem factorial_tail_growth (n i : ℕ) :
    Nat.factorial n * (n + 1) ^ i ≤ Nat.factorial (n + i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [show n + (i + 1) = (n + i) + 1 from by omega, Nat.factorial_succ, pow_succ]
    calc Nat.factorial n * ((n + 1) ^ i * (n + 1))
        = (Nat.factorial n * (n + 1) ^ i) * (n + 1) := by ring
      _ ≤ Nat.factorial (n + i) * (n + 1) := Nat.mul_le_mul_right _ ih
      _ ≤ (n + i + 1) * Nat.factorial (n + i) := by
          nlinarith

theorem factorial_recip_sq_sum_le (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), ((Nat.factorial j : ℝ)⁻¹ ^ 2) ≤ 57 / 25 := by
  by_cases hk : k < 2
  · interval_cases k <;> norm_num [Finset.sum_range_succ]
  have hterm : ∀ i : ℕ, (Nat.factorial (3 + i) : ℝ)⁻¹ ^ 2 ≤
      (1 / 36 : ℝ) * (1 / 16 : ℝ) ^ i := by
    intro i
    have hf : (6 : ℝ) * 4 ^ i ≤ (Nat.factorial (3 + i) : ℝ) := by
      exact_mod_cast factorial_tail_growth 3 i
    have hpos : (0 : ℝ) < (Nat.factorial (3 + i) : ℝ) := by positivity
    have hi : (Nat.factorial (3 + i) : ℝ)⁻¹ ≤ (6 * (4 : ℝ) ^ i)⁻¹ := by
      apply (inv_le_inv₀ hpos (by positivity)).mpr hf
    have heq : ((6 * (4 : ℝ) ^ i)⁻¹)^2 = (1 / 36 : ℝ) * (1 / 16 : ℝ) ^ i := by
      rw [mul_inv, mul_pow, ← inv_pow, ← pow_mul, mul_comm i 2, pow_mul]
      norm_num
    rw [← heq]
    exact pow_le_pow_left₀ (by positivity) hi 2
  have hs : Summable (fun i : ℕ => (1 / 36 : ℝ) * (1 / 16 : ℝ) ^ i) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 16) (by norm_num)).mul_left _
  have htail : ∑ i ∈ Finset.range (k - 2), (Nat.factorial (3 + i) : ℝ)⁻¹ ^ 2 ≤ 4 / 135 := by
    calc ∑ i ∈ Finset.range (k - 2), (Nat.factorial (3 + i) : ℝ)⁻¹ ^ 2
        ≤ ∑ i ∈ Finset.range (k - 2), (1 / 36 : ℝ) * (1 / 16 : ℝ) ^ i :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ ≤ ∑' i : ℕ, (1 / 36 : ℝ) * (1 / 16 : ℝ) ^ i :=
          hs.sum_le_tsum _ (fun _ _ => by positivity)
      _ = 4 / 135 := by
          rw [tsum_mul_left,
              tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 16) (by norm_num)]
          norm_num
  rw [show k + 1 = 3 + (k - 2) from by omega, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ] at ⊢
  simp only [inv_pow] at htail
  linarith

theorem exp_one_le : Real.exp 1 ≤ 87 / 32 := by
  linarith [Real.exp_one_lt_d9]

theorem one_add_pow_le_exp_one {x : ℝ} {n : ℕ} (hx : 0 ≤ x) (hxn : x * n ≤ 1) :
    (1 + x) ^ n ≤ Real.exp 1 := by
  calc (1 + x) ^ n ≤ (Real.exp x) ^ n := by
         gcongr
         linarith [Real.add_one_le_exp x]
    _ = Real.exp (x * n) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hxn

theorem taylorPow_le {k m d : ℕ} (hfac : 2 * m ≤ Nat.factorial (k + 1)) (hd : d ≤ m)
    (z : ℂ) (h1 : ‖z‖ ≤ 1) (hre : z.re ≤ 0) :
    ‖taylorPoly k z‖ ^ (2 * d) ≤ 87 / 32 := by
  have hF : (0 : ℝ) < (Nat.factorial (k + 1) : ℝ) := by positivity
  have hn : (2 * d : ℝ) ≤ (Nat.factorial (k + 1) : ℝ) := by
    exact_mod_cast (le_trans (Nat.mul_le_mul_left 2 hd) hfac)
  calc ‖taylorPoly k z‖ ^ (2 * d)
      ≤ (1 + 1 / (Nat.factorial (k + 1) : ℝ)) ^ (2 * d) := by
          gcongr
          exact taylorPoly_le k z h1 hre
    _ ≤ Real.exp 1 := one_add_pow_le_exp_one (by positivity) (by
          rw [one_div, inv_mul_le_iff₀ hF]
          simpa only [Nat.cast_mul, Nat.cast_ofNat, one_mul, mul_one] using! hn)
    _ ≤ 87 / 32 := exp_one_le

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
