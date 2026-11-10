/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Basic.IsEmpty.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.MonteCarloInt20.QaeLaw.TrigonometricBias

def qaeQuotient (θtilde θ : ℝ) (M : ℕ) : ℝ :=
  Real.sin ((M : ℝ) * (θtilde - θ) * Real.pi) ^ 2 /
    ((M : ℝ) ^ 2 * Real.sin ((θtilde - θ) * Real.pi) ^ 2)

def innerQAEBias (θ : ℝ) (M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range M,
    qaeQuotient ((k : ℝ) / (M : ℝ)) θ M *
      (Real.sin (((k : ℝ) / (M : ℝ)) * Real.pi) ^ 2 - Real.sin (θ * Real.pi) ^ 2)

def innerQAELeading (θ M : ℝ) : ℝ :=
  Real.sin (M * θ * Real.pi) ^ 2 * Real.cos (2 * θ * Real.pi) / M

theorem inner_leading_bound (θ M : ℝ) (hM : 0 < M) :
    |innerQAELeading θ M| ≤ 1 / M := by
  unfold innerQAELeading
  rw [abs_div, abs_of_pos hM]
  apply div_le_div_of_nonneg_right _ (le_of_lt hM)
  have hsin : |Real.sin (M * θ * Real.pi) ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact Real.sin_sq_le_one _
  have hcos : |Real.cos (2 * θ * Real.pi)| ≤ 1 := Real.abs_cos_le_one _
  calc |Real.sin (M * θ * Real.pi) ^ 2 * Real.cos (2 * θ * Real.pi)|
      = |Real.sin (M * θ * Real.pi) ^ 2| * |Real.cos (2 * θ * Real.pi)| := abs_mul _ _
    _ ≤ 1 * 1 := mul_le_mul hsin hcos (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

lemma sin_sq_sub_sin_sq (a b : ℝ) :
    Real.sin a ^ 2 - Real.sin b ^ 2 = Real.sin (a + b) * Real.sin (a - b) := by
  rw [Real.sin_sq_eq_half_sub, Real.sin_sq_eq_half_sub]
  have h := Real.cos_sub_cos (2 * b) (2 * a)
  have h' : Real.cos (2 * b) - Real.cos (2 * a) = 2 * Real.sin (a + b) * Real.sin (a - b) := by
    rw [h]
    have e1 : (2 * b + 2 * a) / 2 = a + b := by ring
    have e2 : (2 * b - 2 * a) / 2 = -(a - b) := by ring
    rw [e1, e2, Real.sin_neg]
    ring
  linarith

lemma sin_sq_nat_mul_pi_sub (x : ℝ) (k : ℕ) :
    Real.sin ((k:ℝ) * Real.pi - x) ^ 2 = Real.sin x ^ 2 := by
  rw [Real.sin_nat_mul_pi_sub]
  have h : ((-1:ℝ)^k)^2 = 1 := by
    rw [← pow_mul]
    exact Even.neg_one_pow ⟨k, by ring⟩
  calc (-((-1:ℝ)^k * Real.sin x))^2 = ((-1:ℝ)^k)^2 * Real.sin x^2 := by ring
    _ = Real.sin x^2 := by rw [h, one_mul]

lemma qaeQuotient_grid (θ : ℝ) (M : ℕ) (hM : 0 < M) (k : ℕ) :
    qaeQuotient ((k:ℝ)/(M:ℝ)) θ M =
      Real.sin ((M:ℝ)*θ*Real.pi)^2 /
        ((M:ℝ)^2 * Real.sin (Real.pi * ((k:ℝ) - (M:ℝ)*θ) / (M:ℝ))^2) := by
  unfold qaeQuotient
  have hM' : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hnum : (M:ℝ) * ((k:ℝ)/(M:ℝ) - θ) * Real.pi = (k:ℝ)*Real.pi - (M:ℝ)*θ*Real.pi := by
    field_simp
  have hden : ((k:ℝ)/(M:ℝ) - θ) * Real.pi = Real.pi * ((k:ℝ) - (M:ℝ)*θ) / (M:ℝ) := by
    field_simp
  rw [hnum, hden, sin_sq_nat_mul_pi_sub]

lemma sin_y_ne_zero (θ : ℝ) (M : ℕ) (hM : 0 < M) (k : ℕ)
    (h : Real.sin ((M:ℝ)*θ*Real.pi) ≠ 0) :
    Real.sin (Real.pi * ((k:ℝ) - (M:ℝ)*θ) / (M:ℝ)) ≠ 0 := by
  intro hy
  rw [Real.sin_eq_zero_iff] at hy
  obtain ⟨n, hn⟩ := hy
  have hM' : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp [hM'] at hn
  have h2 : (M:ℝ)*θ = (k:ℝ) - (n:ℝ)*(M:ℝ) := by linarith
  apply h
  have h4 : (M:ℝ)*θ*Real.pi = ((k:ℝ) - (n:ℝ)*(M:ℝ))*Real.pi := by rw [h2]
  rw [h4]
  have h5 : (k:ℝ) - (n:ℝ)*(M:ℝ) = (((k:ℤ) - n*(M:ℤ) : ℤ) : ℝ) := by push_cast; ring
  rw [h5]
  exact Real.sin_int_mul_pi _

lemma term_eq (θ : ℝ) (M : ℕ) (hM : 0 < M) (k : ℕ)
    (h : Real.sin ((M:ℝ)*θ*Real.pi) ≠ 0) :
    qaeQuotient ((k:ℝ)/(M:ℝ)) θ M *
      (Real.sin (((k:ℝ)/(M:ℝ))*Real.pi)^2 - Real.sin (θ*Real.pi)^2)
    = Real.sin ((M:ℝ)*θ*Real.pi)^2 / (M:ℝ)^2 *
        (Real.sin (Real.pi * ((k:ℝ) - (M:ℝ)*θ) / (M:ℝ) + 2*θ*Real.pi) /
         Real.sin (Real.pi * ((k:ℝ) - (M:ℝ)*θ) / (M:ℝ))) := by
  rw [qaeQuotient_grid θ M hM k]
  set y : ℝ := Real.pi * ((k:ℝ) - (M:ℝ)*θ) / (M:ℝ) with hy
  have hyne : Real.sin y ≠ 0 := by
    rw [hy]
    exact sin_y_ne_zero θ M hM k h
  have hk : ((k:ℝ)/(M:ℝ))*Real.pi = y + θ*Real.pi := by
    rw [hy]; field_simp; ring
  have htrig : Real.sin (((k:ℝ)/(M:ℝ))*Real.pi)^2 - Real.sin (θ*Real.pi)^2
      = Real.sin y * Real.sin (y + 2*θ*Real.pi) := by
    rw [hk]
    have hh := sin_sq_sub_sin_sq (y + θ*Real.pi) (θ*Real.pi)
    rw [hh]
    have e1 : y + θ*Real.pi + θ*Real.pi = y + 2*θ*Real.pi := by ring
    have e2 : y + θ*Real.pi - θ*Real.pi = y := by ring
    rw [e1, e2, mul_comm]
  rw [htrig]
  have hM' : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp [hyne, hM']

lemma bias_eq_zero_of_sin (θ : ℝ) (M : ℕ) (hM : 0 < M)
    (h : Real.sin ((M:ℝ)*θ*Real.pi) = 0) :
    innerQAEBias θ M = 0 := by
  unfold innerQAEBias
  apply Finset.sum_eq_zero
  intro k hk
  have hnum : Real.sin ((M:ℝ) * ((k:ℝ)/(M:ℝ) - θ) * Real.pi) = 0 := by
    have h1 : (M:ℝ) * ((k:ℝ)/(M:ℝ) - θ) * Real.pi = (k:ℝ)*Real.pi - (M:ℝ)*θ*Real.pi := by
      field_simp
    rw [h1, Real.sin_nat_mul_pi_sub, h, mul_zero, neg_zero]
  simp [qaeQuotient, hnum]

lemma exp_neg_two_pi_I_phi_ne_one (φ : ℝ) (h : Real.sin (Real.pi*φ) ≠ 0) :
    Complex.exp (2 * Complex.I * (-(Real.pi * φ))) ≠ 1 := by
  intro h1
  rw [Complex.exp_eq_one_iff] at h1
  obtain ⟨n, hn⟩ := h1
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : (φ : ℂ) = -(n : ℂ) := by
    have := hn
    field_simp [hI, hπ] at this
    rw [neg_eq_iff_eq_neg] at this
    exact this
  apply h
  have h3 : φ = -(n:ℝ) := by
    apply Complex.ofReal_injective
    have h4 : ((φ:ℂ)) = ((-(n:ℝ) : ℝ) : ℂ) := by
      push_cast
      exact h2
    exact h4
  rw [h3]
  have h5 : Real.pi * (-(n:ℝ)) = ((-n:ℤ) : ℝ) * Real.pi := by push_cast; ring
  rw [h5]
  exact Real.sin_int_mul_pi (-n)

lemma exp_pow_eq_neg_exp (φ : ℝ) (M : ℕ) (hM : 0 < M) (k : ℕ) :
    (Complex.exp (2 * Complex.I * ((Real.pi:ℂ) * ((k:ℝ) - φ) / (M:ℝ)))) ^ M
      = Complex.exp (2 * Complex.I * (-(Real.pi * φ))) := by
  rw [← Complex.exp_nat_mul]
  have hM' : (M:ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have harg : (M:ℂ) * (2 * Complex.I * ((Real.pi:ℂ) * ((k:ℝ) - φ) / (M:ℝ)))
      = (2 * Complex.I * (-(Real.pi * φ))) + (k:ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    field_simp
    ring
  rw [harg, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

lemma z_pow_eq (φ : ℝ) (M : ℕ) (hM : 0 < M) (k j : ℕ) :
    (Complex.exp (2 * Complex.I * ((Real.pi:ℂ) * ((k:ℝ) - φ) / (M:ℝ)))) ^ j
      = Complex.exp (-(2 * Real.pi * Complex.I * (j:ℂ) * (φ:ℂ) / (M:ℂ))) *
        (Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) / (M:ℂ))) ^ k := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  have hM' : (M:ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  push_cast
  field_simp
  ring

lemma cot_sum_eq (φ : ℝ) (M : ℕ) (hM : 0 < M) (h : Real.sin (Real.pi*φ) ≠ 0) :
    ∑ k ∈ Finset.range M, Real.cot (Real.pi * ((k:ℝ) - φ) / (M:ℝ))
      = -(M:ℝ) * Real.cot (Real.pi*φ) := by
  let z : ℕ → ℂ := fun k => Complex.exp (2 * Complex.I * ((Real.pi:ℂ) * ((k:ℝ) - φ) / (M:ℝ)))
  let a : ℂ := Complex.exp (2 * Complex.I * (-(Real.pi * φ)))
  have ha : a ≠ 1 := exp_neg_two_pi_I_phi_ne_one φ h
  have hM' : (M:ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hzM : ∀ k, z k ^ M = a := fun k => exp_pow_eq_neg_exp φ M hM k
  have hz_ne_one : ∀ k, z k ≠ 1 := by
    intro k hz
    apply ha
    rw [← hzM k, hz, one_pow]
  have hgeom : ∀ k, 1 / (z k - 1) = (∑ j ∈ Finset.range M, (z k)^j) / (a - 1) := by
    intro k
    have hz1 : z k - 1 ≠ 0 := sub_ne_zero.mpr (hz_ne_one k)
    have ha1 : a - 1 ≠ 0 := sub_ne_zero.mpr ha
    have h1 : (∑ j ∈ Finset.range M, (z k)^j) * (z k - 1) = a - 1 := by
      rw [geom_sum_mul, hzM k]
    rw [div_eq_div_iff hz1 ha1, one_mul, h1]
  have hsum1 : ∑ k ∈ Finset.range M, (1 / (z k - 1)) = (M:ℂ) / (a - 1) := by
    calc ∑ k ∈ Finset.range M, 1 / (z k - 1)
        = ∑ k ∈ Finset.range M, (∑ j ∈ Finset.range M, (z k)^j) / (a - 1) := by
            apply Finset.sum_congr rfl
            intro k hk
            exact hgeom k
      _ = (∑ k ∈ Finset.range M, ∑ j ∈ Finset.range M, (z k)^j) / (a - 1) := by
            rw [Finset.sum_div]
      _ = (M:ℂ) / (a - 1) := by
            congr 1
            calc ∑ k ∈ Finset.range M, ∑ j ∈ Finset.range M, (z k)^j
                = ∑ j ∈ Finset.range M, ∑ k ∈ Finset.range M, (z k)^j := by
                    rw [Finset.sum_comm]
              _ = ∑ j ∈ Finset.range M, (if j = 0 then (M:ℂ) else 0) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    rw [Finset.mem_range] at hj
                    by_cases hj0 : j = 0
                    · subst hj0; simp
                    · rw [if_neg hj0]
                      have hzj : ∀ k, (z k)^j =
                          Complex.exp (-(2 * Real.pi * Complex.I * (j:ℂ) * (φ:ℂ) / (M:ℂ))) *
                          (Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) / (M:ℂ))) ^ k :=
                        fun k => z_pow_eq φ M hM k j
                      simp_rw [hzj]
                      rw [← Finset.mul_sum]
                      have hζ_ne_one : Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) / (M:ℂ)) ≠ 1 := by
                        intro hcon
                        rw [Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (by exact_mod_cast hM.ne')] at hcon
                        have hle : M ≤ j := Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) hcon
                        omega
                      have hζM : (Complex.exp (2 * Real.pi * Complex.I * (j:ℂ) / (M:ℂ)))^M = 1 := by
                        rw [← Complex.exp_nat_mul]
                        have harg : (M:ℂ) * (2 * Real.pi * Complex.I * (j:ℂ) / (M:ℂ))
                            = (j:ℂ) * (2 * Real.pi * Complex.I) := by
                          field_simp [hM']
                        rw [harg, Complex.exp_nat_mul_two_pi_mul_I]
                      rw [geom_sum_eq hζ_ne_one, hζM]
                      simp
              _ = (M:ℂ) := by
                    rw [Finset.sum_ite_eq']
                    simp [Finset.mem_range, hM.ne']
  have hcot : ∀ k : ℕ, (Real.cot (Real.pi * ((k:ℝ) - φ) / (M:ℝ)) : ℂ)
      = Complex.I * ((z k + 1) / (z k - 1)) := by
    intro k
    rw [Complex.ofReal_cot, Complex.cot_eq_exp_ratio]
    push_cast
    have hz : Complex.exp (2 * Complex.I * ((Real.pi:ℂ) * ((k:ℂ) - (φ:ℂ)) / (M:ℂ))) = z k := by
      simp only [z]
      congr 1
    rw [hz]
    have hz1 : z k - 1 ≠ 0 := sub_ne_zero.mpr (hz_ne_one k)
    have h1z : 1 - z k ≠ 0 := by intro h; apply hz1; linear_combination -h
    field_simp [hz1, h1z, Complex.I_ne_zero]
    rw [Complex.I_sq]
    ring
  have hsum_cot_complex :
      (∑ k ∈ Finset.range M, (Real.cot (Real.pi * ((k:ℝ) - φ) / (M:ℝ)) : ℂ))
        = Complex.I * (M:ℂ) * ((a + 1) / (a - 1)) := by
    calc ∑ k ∈ Finset.range M, (Real.cot (Real.pi * ((k:ℝ) - φ) / (M:ℝ)) : ℂ)
        = ∑ k ∈ Finset.range M, Complex.I * ((z k + 1) / (z k - 1)) := by
            exact Finset.sum_congr rfl (fun k hk => hcot k)
      _ = Complex.I * ∑ k ∈ Finset.range M, (z k + 1) / (z k - 1) := by
            rw [Finset.mul_sum]
      _ = Complex.I * ∑ k ∈ Finset.range M, (1 + 2 / (z k - 1)) := by
            congr 1
            apply Finset.sum_congr rfl
            intro k hk
            have hz1 : z k - 1 ≠ 0 := sub_ne_zero.mpr (hz_ne_one k)
            field_simp [hz1]
            ring
      _ = Complex.I * ((M:ℂ) + 2 * ∑ k ∈ Finset.range M, 1 / (z k - 1)) := by
            congr 1
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
            simp only [nsmul_eq_mul, mul_one]
            congr 1
            simp_rw [div_eq_mul_inv]
            rw [Finset.mul_sum]
            simp
      _ = Complex.I * ((M:ℂ) + 2 * ((M:ℂ) / (a - 1))) := by rw [hsum1]
      _ = Complex.I * (M:ℂ) * ((a + 1) / (a - 1)) := by
            have ha1 : a - 1 ≠ 0 := sub_ne_zero.mpr ha
            field_simp [ha1]
            ring
  have hcot_odd : Complex.cot (-(Real.pi * φ)) = -Complex.cot (Real.pi * φ) := by
    simp only [Complex.cot, Complex.cos_neg, Complex.sin_neg]
    rw [div_neg]
  have hexp_cot : Complex.I * ((a + 1) / (a - 1)) = Complex.cot (-(Real.pi * φ)) := by
    rw [Complex.cot_eq_exp_ratio]
    have hE : Complex.exp (2 * Complex.I * (-((Real.pi:ℂ) * (φ:ℂ)))) = a := by
      simp only [a]
    rw [hE]
    have ha1 : a - 1 ≠ 0 := sub_ne_zero.mpr ha
    have h1a : 1 - a ≠ 0 := by intro h; apply ha1; linear_combination -h
    field_simp [ha1, h1a, Complex.I_ne_zero]
    rw [Complex.I_sq]
    ring
  apply Complex.ofReal_injective
  calc (((∑ k ∈ Finset.range M, Real.cot (Real.pi * ((k:ℝ) - φ) / (M:ℝ))) : ℝ) : ℂ)
      = ∑ k ∈ Finset.range M, (Real.cot (Real.pi * ((k:ℝ) - φ) / (M:ℝ)) : ℂ) := by
          rw [Complex.ofReal_sum]
    _ = Complex.I * (M:ℂ) * ((a + 1) / (a - 1)) := hsum_cot_complex
    _ = (M:ℂ) * (Complex.I * ((a + 1) / (a - 1))) := by ring
    _ = (M:ℂ) * (-Complex.cot (Real.pi * φ)) := by rw [hexp_cot, hcot_odd]
    _ = (((-(M:ℝ) * Real.cot (Real.pi * φ)) : ℝ) : ℂ) := by push_cast; ring

lemma innerQAEBias_closed (θ : ℝ) (M : ℕ) (hM : 0 < M) :
    innerQAEBias θ M =
      Real.sin ((M:ℝ)*θ*Real.pi) * Real.sin (((M:ℝ) - 2)*θ*Real.pi) / (M:ℝ) := by
  by_cases hsin : Real.sin ((M:ℝ)*θ*Real.pi) = 0
  · rw [bias_eq_zero_of_sin θ M hM hsin, hsin]
    ring
  · have hsin_ne : Real.sin ((M:ℝ)*θ*Real.pi) ≠ 0 := hsin
    have hM' : (M:ℝ) ≠ 0 := by exact_mod_cast hM.ne'
    have hcongr : ∑ k ∈ Finset.range M,
          qaeQuotient ((k:ℝ)/(M:ℝ)) θ M *
            (Real.sin (((k:ℝ)/(M:ℝ))*Real.pi)^2 - Real.sin (θ*Real.pi)^2)
        = ∑ k ∈ Finset.range M,
          (Real.sin ((M:ℝ)*θ*Real.pi)^2 / (M:ℝ)^2 *
            (Real.sin (Real.pi * ((k:ℝ) - (M:ℝ)*θ) / (M:ℝ) + 2*θ*Real.pi) /
             Real.sin (Real.pi * ((k:ℝ) - (M:ℝ)*θ) / (M:ℝ)))) := by
      exact Finset.sum_congr rfl (fun k hk => term_eq θ M hM k hsin_ne)
    unfold innerQAEBias
    rw [hcongr, ← Finset.mul_sum]
    have hconst : (M:ℝ) * Real.cos (2*θ*Real.pi)
        = ∑ k ∈ Finset.range M, Real.cos (2*θ*Real.pi) := by
      rw [Finset.sum_const, Finset.card_range]
      simp
    have htrig_sum : ∑ k ∈ Finset.range M,
          Real.sin (Real.pi * ((k:ℝ) - (M:ℝ)*θ) / (M:ℝ) + 2*θ*Real.pi) /
          Real.sin (Real.pi * ((k:ℝ) - (M:ℝ)*θ) / (M:ℝ))
        = (M:ℝ) * Real.cos (2*θ*Real.pi) + Real.sin (2*θ*Real.pi) *
            ∑ k ∈ Finset.range M, Real.cot (Real.pi * ((k:ℝ) - (M:ℝ)*θ) / (M:ℝ)) := by
      rw [hconst, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      have hy : Real.sin (Real.pi * ((k:ℝ) - (M:ℝ)*θ) / (M:ℝ)) ≠ 0 :=
        sin_y_ne_zero θ M hM k hsin_ne
      rw [Real.sin_add, Real.cot_eq_cos_div_sin]
      field_simp [hy]
    rw [htrig_sum]
    have hsin_ne' : Real.sin (Real.pi * ((M:ℝ)*θ)) ≠ 0 := by
      have harg : Real.pi * ((M:ℝ)*θ) = (M:ℝ)*θ*Real.pi := by ring
      rw [harg]
      exact hsin_ne
    rw [cot_sum_eq ((M:ℝ)*θ) M hM hsin_ne']
    rw [Real.cot_eq_cos_div_sin]
    have harg2 : Real.pi * ((M:ℝ)*θ) = (M:ℝ)*θ*Real.pi := by ring
    rw [harg2]
    have hsub : ((M:ℝ) - 2)*θ*Real.pi = (M:ℝ)*θ*Real.pi - 2*θ*Real.pi := by ring
    rw [hsub, Real.sin_sub]
    field_simp [hsin_ne, hM']
    ring

theorem inner_qae_error_bound (θ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, 1 ≤ M →
      |innerQAEBias θ M| ≤ 1 / (M : ℝ) + C / (M : ℝ) ^ 2 := by
  refine ⟨0, le_refl 0, ?_⟩
  intro M hM
  have hMpos : 0 < M := hM
  have hM' : (0:ℝ) < (M:ℝ) := by exact_mod_cast hMpos
  rw [innerQAEBias_closed θ M hMpos, abs_div, abs_of_pos hM']
  have h1 : |Real.sin ((M:ℝ)*θ*Real.pi)| ≤ 1 := Real.abs_sin_le_one _
  have h2 : |Real.sin (((M:ℝ) - 2)*θ*Real.pi)| ≤ 1 := Real.abs_sin_le_one _
  have hmul : |Real.sin ((M:ℝ)*θ*Real.pi) * Real.sin (((M:ℝ) - 2)*θ*Real.pi)|
      ≤ 1 * 1 := by
    rw [abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
  calc |Real.sin ((M:ℝ)*θ*Real.pi) * Real.sin (((M:ℝ) - 2)*θ*Real.pi)| / (M:ℝ)
      ≤ 1 * 1 / (M:ℝ) := by
        exact div_le_div_of_nonneg_right hmul (le_of_lt hM')
    _ = 1 / (M:ℝ) + 0 / (M:ℝ)^2 := by ring

end Qatlib.Papers.MonteCarloInt20.QaeLaw.TrigonometricBias
