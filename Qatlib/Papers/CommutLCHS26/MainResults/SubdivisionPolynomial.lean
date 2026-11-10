/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.MPFRemainder
import Qatlib.Papers.CommutLCHS26.MainResults.FormalPowers
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Inverse
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.SubdivisionPolynomial
open Qatlib.Papers.CommutLCHS26.MainResults.FormalPowers

open scoped BigOperators Matrix.Norms.L2Operator
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Papers.CommutLCHS26.MainResults.MPFRemainder

variable {I : Type} [Fintype I] [DecidableEq I]

def wordSeries (ws : List (Matrix I I ℂ)) : PowerSeries (Matrix I I ℂ) :=
  PowerSeries.mk (suzukiSeries ws)

private theorem wordSeries_nil : wordSeries ([] : List (Matrix I I ℂ)) = 1 := by
  apply PowerSeries.ext
  intro n
  cases n <;> simp [wordSeries, suzukiSeries]

theorem wordSeries_append (xs ys : List (Matrix I I ℂ)) :
    wordSeries (xs ++ ys) = wordSeries xs * wordSeries ys := by
  induction xs with
  | nil => simp only [List.nil_append, wordSeries_nil, one_mul]
  | cons X xs ih =>
    have hc (zs : List (Matrix I I ℂ)) :
        wordSeries (X :: zs) = wordSeries [X] * wordSeries zs := by
      apply PowerSeries.ext
      intro n
      simp only [wordSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mul]
      rw [suzukiSeries]
      apply Finset.sum_congr rfl
      intro p _
      rw [suzukiSeries_singleton]
    calc
      _ = wordSeries [X] * wordSeries (xs ++ ys) := hc _
      _ = wordSeries [X] * (wordSeries xs * wordSeries ys) := by rw [ih]
      _ = (wordSeries [X] * wordSeries xs) * wordSeries ys := (mul_assoc _ _ _).symm
      _ = _ := by rw [← hc xs]

theorem wordSeries_replicate (ws : List (Matrix I I ℂ)) (q : ℕ) :
    wordSeries (List.replicate q ws).flatten = wordSeries ws ^ q := by
  induction q with
  | zero => simp only [List.replicate_zero, List.flatten_nil, wordSeries_nil, pow_zero]
  | succ q ih =>
    simp only [List.replicate_succ, List.flatten_cons, wordSeries_append, ih, pow_succ']

theorem word_coefficient_scale (ws : List (Matrix I I ℂ)) (a : ℝ) (n : ℕ) :
    suzukiSeries (ws.map (fun X => a • X)) n = a ^ n • suzukiSeries ws n := by
  induction ws generalizing n with
  | nil => cases n <;> simp [suzukiSeries]
  | cons X xs ih =>
    simp only [List.map_cons, suzukiSeries, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [smul_pow, ih, smul_smul, mul_comm ((p.1.factorial : ℝ)⁻¹), ← smul_smul,
      smul_mul_smul_comm, ← pow_add, Finset.HasAntidiagonal.mem_antidiagonal.mp hp]

def choosePolynomial (j : ℕ) : Polynomial ℂ :=
  (j.factorial : ℂ)⁻¹ • descPochhammer ℂ j

theorem choosePolynomial_eval (j q : ℕ) :
    (choosePolynomial j).eval (q : ℂ) = (q.choose j : ℂ) := by
  rw [choosePolynomial, Polynomial.eval_smul, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, smul_eq_mul]
  have hj : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  field_simp

theorem choosePolynomial_degree (j : ℕ) : (choosePolynomial j).natDegree ≤ j := by
  exact (Polynomial.natDegree_smul_le _ _).trans_eq (descPochhammer_natDegree ℂ j)

theorem choosePolynomial_leading (j : ℕ) :
    (choosePolynomial j).coeff j = (j.factorial : ℂ)⁻¹ := by
  rw [choosePolynomial, Polynomial.coeff_smul]
  have h := (monic_descPochhammer ℂ j).coeff_natDegree
  rw [descPochhammer_natDegree] at h
  simp only [h, smul_eq_mul, mul_one]

def powerPolynomial (f : PowerSeries (Matrix I I ℂ)) (n : ℕ) (i j : I) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (n + 1), ((PowerSeries.coeff n ((f - 1) ^ k) : Matrix I I ℂ) i j) • choosePolynomial k

theorem powerPolynomial_eval (f : PowerSeries (Matrix I I ℂ)) (hf : f.constantCoeff = 1)
    (n q : ℕ) (i j : I) :
    (powerPolynomial f n i j).eval (q : ℂ) = PowerSeries.coeff n (f ^ q) i j := by
  rw [power_coefficient_newton f hf n q]
  simp only [powerPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_smul,
    choosePolynomial_eval, Matrix.sum_apply, Matrix.smul_apply]
  simp only [smul_eq_mul, nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem powerPolynomial_degree (f : PowerSeries (Matrix I I ℂ)) (n : ℕ) (i j : I) :
    (powerPolynomial f n i j).natDegree ≤ n := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro N hN
  rw [powerPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Polynomial.coeff_smul]
  have hk' : k ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using! hk
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((choosePolynomial_degree k).trans_lt (hk'.trans_lt hN))]
  simp

private theorem power_coeff_leading {A : Type} [Ring A] (f : PowerSeries A)
    (hf : f.constantCoeff = 0) (n : ℕ) :
    PowerSeries.coeff n (f ^ n) = (PowerSeries.coeff 1 f) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, PowerSeries.coeff_mul]
    calc
      _ = PowerSeries.coeff n (f ^ n) * PowerSeries.coeff 1 f := by
        apply Finset.sum_eq_single (n, 1)
        · intro p hp hne
          have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
          by_cases hl : p.1 < n
          · rw [power_coeff_vanish f hf _ _ hl, zero_mul]
          · have hz : p.2 = 0 := by
              by_contra hh
              have he : p = (n, 1) := by ext <;> omega
              exact hne he
            rw [hz, PowerSeries.coeff_zero_eq_constantCoeff, hf, mul_zero]
        · intro h
          exact (h (by simp)).elim
      _ = _ := by rw [ih, pow_succ]

theorem powerPolynomial_leading (f : PowerSeries (Matrix I I ℂ)) (hf : f.constantCoeff = 1)
    (n : ℕ) (i j : I) :
    (powerPolynomial f n i j).coeff n =
      (n.factorial : ℂ)⁻¹ * ((PowerSeries.coeff 1 f) ^ n) i j := by
  rw [powerPolynomial, Polynomial.finsetSum_coeff]
  have hz : (f - 1).constantCoeff = 0 := by simp [hf]
  have hfirst : PowerSeries.coeff 1 (f - 1) = PowerSeries.coeff 1 f := by simp
  rw [Finset.sum_eq_single n]
  · rw [Polynomial.coeff_smul, choosePolynomial_leading, power_coeff_leading (f - 1) hz n, hfirst]
    simp only [smul_eq_mul, mul_comm]
  · intro k hk hkn
    have hk' : k < n := by simp only [Finset.mem_range] at hk; omega
    rw [Polynomial.coeff_smul,
      Polynomial.coeff_eq_zero_of_natDegree_lt ((choosePolynomial_degree k).trans_lt hk')]
    simp
  · intro h
    exact (h (by simp)).elim

theorem powerPolynomial_zero (f : PowerSeries (Matrix I I ℂ)) (hf : f.constantCoeff = 1)
    (n : ℕ) (hn : 0 < n) (i j : I) : (powerPolynomial f n i j).coeff 0 = 0 := by
  have h := powerPolynomial_eval f hf n 0 i j
  simpa only [Nat.cast_zero, Polynomial.coeff_zero_eq_eval_zero, pow_zero, PowerSeries.coeff_one,
    if_neg (by omega : n ≠ 0), Matrix.zero_apply] using! h

def strangSeries (X Y : Matrix I I ℂ) : PowerSeries (Matrix I I ℂ) :=
  wordSeries [(1 / 2 : ℝ) • X, Y, (1 / 2 : ℝ) • X]

theorem strangSeries_first (X Y : Matrix I I ℂ) :
    PowerSeries.coeff 1 (strangSeries X Y) = X + Y := by
  simp only [strangSeries, wordSeries, PowerSeries.coeff_mk, suzukiSeries_cons_one,
    suzukiSeries_nil_succ]
  module

theorem strangSeries_constant (X Y : Matrix I I ℂ) :
    (strangSeries X Y).constantCoeff = 1 := by
  simp [strangSeries, wordSeries]

omit [Fintype I] [DecidableEq I] in

theorem strangRepeats_scale (X Y : Matrix I I ℂ) (q : ℕ) :
    strangRepeats X Y q =
      ((List.replicate q [(1 / 2 : ℝ) • X, Y, (1 / 2 : ℝ) • X]).flatten).map
        (fun A => (q : ℝ)⁻¹ • A) := by
  simp [strangRepeats, List.map_flatten, List.map_replicate, smul_smul,
    div_eq_mul_inv, mul_inv_rev, mul_comm]

theorem strangRepeats_coefficient (X Y : Matrix I I ℂ) (q n : ℕ) :
    suzukiSeries (strangRepeats X Y q) n =
      ((q : ℝ)⁻¹) ^ n • PowerSeries.coeff n (strangSeries X Y ^ q) := by
  rw [strangRepeats_scale, word_coefficient_scale]
  congr 1
  have h := congrArg (PowerSeries.coeff n)
    (wordSeries_replicate [(1 / 2 : ℝ) • X, Y, (1 / 2 : ℝ) • X] q)
  simpa only [wordSeries, strangSeries, PowerSeries.coeff_mk] using! h

def subdivisionPolynomial (X Y : Matrix I I ℂ) (n : ℕ) (i j : I) : Polynomial ℂ :=
  (powerPolynomial (strangSeries X Y) n i j).reflect n

theorem subdivisionPolynomial_eval (X Y : Matrix I I ℂ) (n q : ℕ) (hq : 0 < q) (i j : I) :
    (subdivisionPolynomial X Y n i j).eval ((q : ℂ)⁻¹) =
      suzukiSeries (strangRepeats X Y q) n i j := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  letI : Invertible (q : ℂ) := invertibleOfNonzero hq0
  have hp := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) (q : ℂ) n
    (powerPolynomial (strangSeries X Y) n i j) (powerPolynomial_degree _ _ _ _)
  simp only [Polynomial.eval₂_id, invOf_eq_inv] at hp
  rw [powerPolynomial_eval _ (strangSeries_constant X Y)] at hp
  rw [strangRepeats_coefficient, Matrix.smul_apply, Complex.real_smul]
  change (subdivisionPolynomial X Y n i j).eval ((q : ℂ)⁻¹) =
    (((q : ℝ)⁻¹) ^ n : ℝ) * PowerSeries.coeff n (strangSeries X Y ^ q) i j
  have hr : ((((q : ℝ)⁻¹) ^ n : ℝ) : ℂ) = ((q : ℂ) ^ n)⁻¹ := by
    push_cast; rw [inv_pow]
  rw [hr]
  apply (mul_left_cancel₀ (pow_ne_zero n hq0))
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero n hq0), one_mul]
  simpa only [subdivisionPolynomial, mul_comm] using! hp

theorem subdivisionPolynomial_degree (X Y : Matrix I I ℂ) (n : ℕ) (i j : I) :
    (subdivisionPolynomial X Y n i j).natDegree ≤ n := by
  exact Polynomial.natDegree_reflect_le.trans (max_le le_rfl (powerPolynomial_degree _ _ _ _))

theorem subdivisionPolynomial_constant (X Y : Matrix I I ℂ) (n : ℕ) (i j : I) :
    (subdivisionPolynomial X Y n i j).coeff 0 =
      (n.factorial : ℂ)⁻¹ * ((X + Y) ^ n) i j := by
  rw [subdivisionPolynomial, Polynomial.coeff_reflect, Polynomial.revAt_zero,
    powerPolynomial_leading _ (strangSeries_constant X Y), strangSeries_first]

theorem subdivisionPolynomial_degree_pred (X Y : Matrix I I ℂ) (n : ℕ) (hn : 0 < n) (i j : I) :
    (subdivisionPolynomial X Y n i j).natDegree ≤ n - 1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro N hN
  rcases lt_or_ge N n with h | h
  · omega
  · rcases eq_or_lt_of_le h with rfl | hlt
    · rw [subdivisionPolynomial, Polynomial.coeff_reflect, Polynomial.revAt_le le_rfl,
        Nat.sub_self]
      exact powerPolynomial_zero _ (strangSeries_constant X Y) n hn i j
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt
        ((subdivisionPolynomial_degree X Y n i j).trans_lt hlt)

private theorem polynomial_eq_of_nat_eval (p q : Polynomial ℂ)
    (h : ∀ n : ℕ, p.eval (n : ℂ) = q.eval (n : ℂ)) : p = q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective : Function.Injective (fun n : ℕ => (n : ℂ)))).mono
  rintro _ ⟨n, rfl⟩
  exact h n

theorem powerPolynomial_shift (f : PowerSeries (Matrix I I ℂ)) (hf : f.constantCoeff = 1)
    (n q : ℕ) (i j : I) :
    (powerPolynomial f n i j).comp (Polynomial.X + Polynomial.C (q : ℂ)) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ∑ l : I,
        powerPolynomial f p.1 i l * Polynomial.C (PowerSeries.coeff p.2 (f ^ q) l j) := by
  apply polynomial_eq_of_nat_eval
  intro s
  simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_finsetSum, Polynomial.eval_mul]
  rw [← Nat.cast_add, powerPolynomial_eval f hf n (s + q) i j, pow_add,
    PowerSeries.coeff_mul, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Matrix.mul_apply, powerPolynomial_eval f hf]

def continuedPower (f : PowerSeries (Matrix I I ℂ)) (z : ℂ) : PowerSeries (Matrix I I ℂ) :=
  PowerSeries.mk fun n => fun i j => (powerPolynomial f n i j).eval z

theorem continuedPower_nat (f : PowerSeries (Matrix I I ℂ)) (hf : f.constantCoeff = 1) (q : ℕ) :
    continuedPower f (q : ℂ) = f ^ q := by
  apply PowerSeries.ext
  intro n
  ext i j
  simpa only [continuedPower, PowerSeries.coeff_mk] using! powerPolynomial_eval f hf n q i j

theorem continuedPower_add_nat (f : PowerSeries (Matrix I I ℂ)) (hf : f.constantCoeff = 1)
    (z : ℂ) (q : ℕ) : continuedPower f (z + q) = continuedPower f z * f ^ q := by
  apply PowerSeries.ext
  intro n
  ext i j
  have h := congrArg (Polynomial.eval z) (powerPolynomial_shift f hf n q i j)
  simpa only [continuedPower, PowerSeries.coeff_mk, PowerSeries.coeff_mul,
    Matrix.sum_apply, Matrix.mul_apply, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_finsetSum, Polynomial.eval_mul] using! h

theorem continuedPower_neg_mul (f : PowerSeries (Matrix I I ℂ)) (hf : f.constantCoeff = 1)
    (q : ℕ) : continuedPower f (-(q : ℂ)) * f ^ q = 1 := by
  rw [← continuedPower_add_nat f hf]
  simpa only [neg_add_cancel, Nat.cast_zero, pow_zero] using! continuedPower_nat f hf 0

private theorem scalar_exp_convolution (a b : ℝ) (n : ℕ) :
    (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
      (a ^ p.1 / (p.1.factorial : ℝ)) * (b ^ p.2 / (p.2.factorial : ℝ))) =
        (a + b) ^ n / (n.factorial : ℝ) := by
  have h := congrArg (PowerSeries.coeff n) (PowerSeries.exp_mul_exp_eq_exp_add a b)
  simpa only [PowerSeries.coeff_mul, PowerSeries.coeff_rescale, PowerSeries.coeff_exp,
    map_div₀, map_mul, map_inv₀, map_one, map_natCast, div_eq_mul_inv, one_mul] using! h

theorem wordSeries_singleton_mul (X : Matrix I I ℂ) (a b : ℝ) :
    wordSeries [a • X] * wordSeries [b • X] = wordSeries [(a + b) • X] := by
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_mul, wordSeries, PowerSeries.coeff_mk, suzukiSeries_singleton,
    smul_pow]
  calc
    _ = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        ((a ^ p.1 / (p.1.factorial : ℝ)) * (b ^ p.2 / (p.2.factorial : ℝ))) • X ^ n := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [smul_smul, smul_smul, smul_mul_smul_comm, ← pow_add,
        Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
      congr 1; ring
    _ = _ := by rw [← Finset.sum_smul, scalar_exp_convolution, smul_smul]; congr 1; ring

private theorem wordSeries_zero : wordSeries [(0 : Matrix I I ℂ)] = 1 := by
  apply PowerSeries.ext
  intro n
  cases n <;> simp [wordSeries, suzukiSeries_singleton]

theorem wordSeries_reverse_inverse (ws : List (Matrix I I ℂ)) :
    wordSeries (ws.reverse.map (fun X => -X)) * wordSeries ws = 1 := by
  induction ws with
  | nil => simp only [List.reverse_nil, List.map_nil, wordSeries_nil, one_mul]
  | cons X xs ih =>
    have he : wordSeries [-X] * wordSeries [X] = 1 := by
      simpa only [neg_one_smul, one_smul, neg_add_cancel, zero_smul, wordSeries_zero] using!
        wordSeries_singleton_mul X (-1) 1
    have hc : wordSeries (X :: xs) = wordSeries [X] * wordSeries xs := by
      simpa only [List.singleton_append] using! wordSeries_append [X] xs
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      wordSeries_append, hc]
    calc
      _ = wordSeries (xs.reverse.map (fun X => -X)) *
          (wordSeries [-X] * wordSeries [X]) * wordSeries xs := by noncomm_ring
      _ = 1 := by rw [he, mul_one, ih]

theorem word_power_scaled_coefficient (ws : List (Matrix I I ℂ)) (a : ℝ) (n q : ℕ) :
    PowerSeries.coeff n (wordSeries (ws.map (fun X => a • X)) ^ q) =
      a ^ n • PowerSeries.coeff n (wordSeries ws ^ q) := by
  rw [← wordSeries_replicate, ← wordSeries_replicate]
  have he : (List.replicate q (ws.map (fun X => a • X))).flatten =
      ((List.replicate q ws).flatten).map (fun X => a • X) := by
    simp only [List.map_flatten, List.map_replicate]
  simp only [he, wordSeries, PowerSeries.coeff_mk, word_coefficient_scale]

theorem symmetric_powerPolynomial_neg (ws : List (Matrix I I ℂ)) (hws : ws.reverse = ws)
    (n q : ℕ) (i j : I) :
    (powerPolynomial (wordSeries ws) n i j).eval (-(q : ℂ)) =
      (-1 : ℂ) ^ n * (powerPolynomial (wordSeries ws) n i j).eval (q : ℂ) := by
  let f := wordSeries ws
  let g := wordSeries (ws.map (fun X => (-1 : ℝ) • X))
  have hf : f.constantCoeff = 1 := by simp [f, wordSeries]
  have hgf : g * f = 1 := by
    simpa only [g, f, neg_one_smul, hws] using! wordSeries_reverse_inverse ws
  have hp : ∀ q : ℕ, g ^ q * f ^ q = 1 := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      calc
        _ = g ^ q * (g * f) * f ^ q := by rw [pow_succ g, pow_succ' f]; noncomm_ring
        _ = 1 := by rw [hgf, mul_one, ih]
  have hu : IsUnit (f ^ q) :=
    (PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hf]; exact isUnit_one)).pow q
  have he : continuedPower f (-(q : ℂ)) = g ^ q :=
    hu.mul_right_cancel ((continuedPower_neg_mul f hf q).trans (hp q).symm)
  have hc := congrArg (fun F => (PowerSeries.coeff n F : Matrix I I ℂ) i j) he
  simp only [continuedPower, PowerSeries.coeff_mk] at hc
  dsimp only [g] at hc
  rw [word_power_scaled_coefficient, Matrix.smul_apply, Complex.real_smul] at hc
  rw [← powerPolynomial_eval f hf n q i j] at hc
  simpa only [f, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one] using! hc

theorem symmetric_powerPolynomial_parity (ws : List (Matrix I I ℂ)) (hws : ws.reverse = ws)
    (n : ℕ) (i j : I) :
    (powerPolynomial (wordSeries ws) n i j).comp (-Polynomial.X) =
      (-1 : ℂ) ^ n • powerPolynomial (wordSeries ws) n i j := by
  apply polynomial_eq_of_nat_eval
  intro q
  simp only [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X,
    Polynomial.eval_smul, smul_eq_mul]
  exact symmetric_powerPolynomial_neg ws hws n q i j

theorem subdivisionPolynomial_odd (X Y : Matrix I I ℂ) (n r : ℕ) (hr : Odd r) (i j : I) :
    (subdivisionPolynomial X Y n i j).coeff r = 0 := by
  by_cases hle : r ≤ n
  · rw [subdivisionPolynomial, Polynomial.coeff_reflect, Polynomial.revAt_le hle]
    have hp := congrArg (fun p : Polynomial ℂ => p.coeff (n - r))
      (symmetric_powerPolynomial_parity [(1 / 2 : ℝ) • X, Y, (1 / 2 : ℝ) • X]
        (by rfl) n i j)
    have he : (-Polynomial.X : Polynomial ℂ) = Polynomial.C (-1) * Polynomial.X := by simp
    simp only [he, Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_smul, smul_eq_mul] at hp
    change (powerPolynomial (strangSeries X Y) n i j).coeff (n - r) * (-1 : ℂ) ^ (n - r) =
      (-1 : ℂ) ^ n * (powerPolynomial (strangSeries X Y) n i j).coeff (n - r) at hp
    have hpow : (-1 : ℂ) ^ n = -(-1 : ℂ) ^ (n - r) := by
      conv_lhs => rw [← Nat.sub_add_cancel hle, pow_add, hr.neg_one_pow, mul_neg_one]
    rw [hpow] at hp
    have hz : (powerPolynomial (strangSeries X Y) n i j).coeff (n - r) * (-1 : ℂ) ^ (n - r) = 0 := by
      linear_combination (1 / 2 : ℂ) * hp
    exact (mul_eq_zero.mp hz).resolve_right (pow_ne_zero _ (by norm_num))
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt
      ((subdivisionPolynomial_degree X Y n i j).trans_lt (Nat.lt_of_not_ge hle))

private theorem sum_range_pairs (f : ℕ → ℂ) (m : ℕ) :
    (∑ r ∈ Finset.range (2 * m), f r) =
      ∑ r ∈ Finset.range m, (f (2 * r) + f (2 * r + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.mul_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

theorem polynomial_moment_evaluation {J : Type} [Fintype J]
    (p : Polynomial ℂ) (a x : J → ℂ) (m : ℕ) (hm : 0 < m)
    (hdegree : p.natDegree < 2 * m) (hodd : ∀ r : ℕ, Odd r → p.coeff r = 0)
    (hmom : ∀ r : ℕ, r < m → (∑ l, a l * (x l) ^ (2 * r)) = (0 : ℂ) ^ r) :
    (∑ l, a l * p.eval (x l)) = p.coeff 0 := by
  have he (z : ℂ) : p.eval z = ∑ r ∈ Finset.range m, p.coeff (2 * r) * z ^ (2 * r) := by
    have h := Polynomial.eval₂_eq_sum_range' (RingHom.id ℂ) hdegree z
    rw [Polynomial.eval₂_id] at h
    rw [h, sum_range_pairs]
    apply Finset.sum_congr rfl
    intro r _
    simp only [RingHom.id_apply, hodd (2 * r + 1) ⟨r, rfl⟩, zero_mul, add_zero]
  simp_rw [he, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ r ∈ Finset.range m, p.coeff (2 * r) * (0 : ℂ) ^ r := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [← hmom r (Finset.mem_range.mp hr), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = _ := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro r _ hr
        simp [zero_pow hr]
      · intro h
        exact (h (Finset.mem_range.mpr hm)).elim

theorem coefficients_from_scalar_moments {J : Type} [Fintype J]
    (X Y : Matrix I I ℂ) (q : J → ℕ) (a : J → ℝ) (m : ℕ) (hm : 0 < m)
    (hq : ∀ l, 0 < q l)
    (hmom : ∀ r : ℕ, r < m → (∑ l, a l / (q l : ℝ) ^ (2 * r)) = (0 : ℝ) ^ r)
    (n : ℕ) (hn : n < 2 * m + 1) :
    coefficient (fun l => strangRepeats X Y (q l)) a n =
      ((n.factorial : ℝ)⁻¹) • (X + Y) ^ n := by
  have hcomplex (r : ℕ) (hr : r < m) :
      (∑ l, (a l : ℂ) * ((q l : ℂ)⁻¹) ^ (2 * r)) = (0 : ℂ) ^ r := by
    have h := congrArg Complex.ofReal (hmom r hr)
    push_cast at h
    simpa only [div_eq_mul_inv, inv_pow] using! h
  by_cases hn0 : n = 0
  · subst n
    have ha := hmom 0 hm
    simp only [Nat.mul_zero, pow_zero, div_one] at ha
    simp only [coefficient, suzukiSeries_zero, ← Finset.sum_smul, ha, one_smul,
      Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero]
  · ext i j
    have hd : (subdivisionPolynomial X Y n i j).natDegree < 2 * m :=
      (subdivisionPolynomial_degree_pred X Y n (Nat.pos_of_ne_zero hn0) i j).trans_lt (by omega)
    have he := polynomial_moment_evaluation (subdivisionPolynomial X Y n i j)
      (fun l => (a l : ℂ)) (fun l => (q l : ℂ)⁻¹) m hm hd
      (fun r hr => subdivisionPolynomial_odd X Y n r hr i j) hcomplex
    simp only [coefficient, Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul]
    simp_rw [← subdivisionPolynomial_eval X Y n _ (hq _) i j]
    rw [he, subdivisionPolynomial_constant]
    push_cast
    rfl

end Qatlib.Papers.CommutLCHS26.MainResults.SubdivisionPolynomial
