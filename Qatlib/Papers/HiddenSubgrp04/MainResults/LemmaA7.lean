/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Qatlib.Papers.HiddenSubgrp04.MainResults.Defs
import Qatlib.Papers.HiddenSubgrp04.MainResults.AppendixASets
import Qatlib.Papers.HiddenSubgrp04.MainResults.AppendixAAmplitudes

/-!
# Geometric sums and Fourier coefficient bounds

This module bounds geometric sums on the unit circle and relates complex exponential separation
to nearest-integer distance. These estimates yield `lemma_A7`, a bound on `Acoef` by the
reciprocal modular distance from the corresponding scaled frequency.

The development follows [Lomont2004].

## Main statements

* `norm_geom_sum_le`: For a unit-norm complex number z different from one, the norm of its first
  n geometric terms is at most 2/‖1 − z‖.
* `pi_mul_dist_le_norm`: The distance from one to exp(2πix) is at least π times the distance
  from x to its rounded integer.
* `lemma_A7`: For positive L, M, and N and nonintegral phase difference k/M − i/N, bounds
  `Acoef` by √(M/(LN)) times 2/π divided by the modular distance of k − Mi/N, under the supplied
  index hypotheses.

## References

* [Lomont, 2004][Lomont2004]
-/

set_option warningAsError false

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.HiddenSubgrp04.MainResults

noncomputable section

/-- For a unit-norm complex number z different from one, the norm of its first n geometric terms
is at most 2/‖1 − z‖. -/
theorem norm_geom_sum_le (z : ℂ) (n : ℕ) (hz : z ≠ 1) (hz1 : ‖z‖ = 1) :
    ‖∑ a ∈ Finset.range n, z ^ a‖ ≤ 2 / ‖1 - z‖ := by
  have hden : 0 < ‖1 - z‖ := by
    rw [norm_pos_iff]
    intro h
    exact hz (by linear_combination -h)
  rw [geom_sum_eq hz, norm_div]
  have hnum : ‖z ^ n - 1‖ ≤ 2 := by
    calc ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz1, one_pow, norm_one]; norm_num
  have hd : ‖z - 1‖ = ‖1 - z‖ := norm_sub_rev z 1
  rw [hd, div_le_div_iff_of_pos_right hden]
  exact hnum

/-- The distance from one to exp(2πix) equals 2|sin(πx)|. -/
theorem norm_one_sub_exp_two_pi_I_mul (x : ℝ) :
    ‖(1 : ℂ) - Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)‖ =
      2 * |Real.sin (Real.pi * x)| := by
  rw [norm_sub_rev]
  have h := Complex.norm_exp_I_mul_ofReal_sub_one (2 * Real.pi * x)
  rw [show 2 * Real.pi * x / 2 = Real.pi * x by ring] at h
  have harg :
      Complex.exp (Complex.I * ((2 * Real.pi * x : ℝ) : ℂ)) =
        Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by rw [mul_comm]
  rw [harg] at h
  rw [h, Real.norm_eq_abs, abs_mul]
  norm_num

/-- For |y| ≤ π/2, one has |y| ≤ 2|sin(y)|. -/
theorem abs_le_two_mul_abs_sin {y : ℝ} (hy : |y| ≤ Real.pi / 2) :
    |y| ≤ 2 * |Real.sin y| := by
  have h := Real.mul_abs_le_abs_sin hy
  have hconst : (1 : ℝ) / 2 ≤ 2 / Real.pi := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) Real.pi_pos]
    norm_num
    linarith [Real.pi_lt_four]
  have hy0 : 0 ≤ |y| := abs_nonneg y
  have hstep : (1 / 2) * |y| ≤ (2 / Real.pi) * |y| :=
    mul_le_mul_of_nonneg_right hconst hy0
  calc |y| = 2 * ((1 / 2) * |y|) := by ring
    _ ≤ 2 * ((2 / Real.pi) * |y|) := mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ ≤ 2 * |Real.sin y| := mul_le_mul_of_nonneg_left h (by norm_num)

/-- The distance from one to exp(2πix) is at least π times the distance from x to its rounded
integer. -/
theorem pi_mul_dist_le_norm (x : ℝ) :
    Real.pi * |x - (nearInt x : ℝ)| ≤
      ‖(1 : ℂ) - Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)‖ := by
  rw [norm_one_sub_exp_two_pi_I_mul]
  set n : ℤ := nearInt x with hn
  have hmem : |Real.pi * (x - (n : ℝ))| ≤ Real.pi / 2 := by
    have h := abs_nearInt_sub_le x
    rw [← hn] at h
    rw [abs_mul, abs_of_pos Real.pi_pos]
    rw [abs_sub_comm (x : ℝ) (n : ℝ)]
    nlinarith [Real.pi_pos, h]
  have hsin_eq : |Real.sin (Real.pi * x)| = |Real.sin (Real.pi * (x - (n : ℝ)))| := by
    have harg : Real.pi * x = Real.pi * (x - (n : ℝ)) + (n : ℝ) * Real.pi := by ring
    rw [harg, Real.sin_add_int_mul_pi, abs_mul]
    have h1 : |((-1 : ℝ) ^ n)| = 1 := abs_neg_one_zpow n
    rw [h1, one_mul]
  rw [hsin_eq]
  have hyle : Real.pi * |x - (n : ℝ)| = |Real.pi * (x - (n : ℝ))| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
  rw [hyle]
  exact abs_le_two_mul_abs_sin hmem

/-- Expresses `omega n` as the complex exponential with imaginary argument 2π/n. -/
theorem omega_eq (n : ℕ) :
    omega n = Complex.exp (((2 * Real.pi / (n : ℝ)) : ℝ) * Complex.I) := by
  unfold omega
  congr 1
  push_cast
  ring

/-- For nonzero M and N, the ratio of the Fourier phases equals exp(2πi(k/M − i/N)). -/
theorem omega_ratio_eq (M N i k : ℕ) (hM : M ≠ 0) (hN : N ≠ 0) :
    (omega N ^ i)⁻¹ * omega M ^ k =
      Complex.exp (((2 * Real.pi * ((k : ℝ) / (M : ℝ) - (i : ℝ) / (N : ℝ)) : ℝ) : ℂ) *
        Complex.I) := by
  rw [omega_eq N, omega_eq M]
  rw [← Complex.exp_nat_mul]
  rw [← Complex.exp_nat_mul]
  rw [← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  push_cast
  have hMc : ((M : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have hNc : ((N : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hN
  field_simp [hMc, hNc]
  ring

/-- For nonzero M and N, the ratio of the specified Fourier phases has norm one. -/
theorem norm_omega_ratio (M N i k : ℕ) (hM : M ≠ 0) (hN : N ≠ 0) :
    ‖(omega N ^ i)⁻¹ * omega M ^ k‖ = 1 := by
  rw [omega_ratio_eq M N i k hM hN]
  exact Complex.norm_exp_ofReal_mul_I _

/-- If M and N are nonzero and k/M − i/N is not an integer, the specified ratio of Fourier
phases is different from one. -/
theorem omega_ratio_ne_one (M N i k : ℕ) (hM : M ≠ 0) (hN : N ≠ 0)
    (hnotint : ¬ ∃ z : ℤ, (k : ℝ) / (M : ℝ) - (i : ℝ) / (N : ℝ) = (z : ℝ)) :
    (omega N ^ i)⁻¹ * omega M ^ k ≠ 1 := by
  rw [omega_ratio_eq M N i k hM hN]
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  apply hnotint
  refine ⟨n, ?_⟩
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
  have hL : (((2 * Real.pi * ((k : ℝ) / (M : ℝ) - (i : ℝ) / (N : ℝ)) : ℝ) : ℂ)) * Complex.I
      = (((k : ℝ) / (M : ℝ) - (i : ℝ) / (N : ℝ) : ℝ) : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hL] at hn
  have h1 := mul_right_cancel₀ hc hn
  rw [← Complex.ofReal_intCast n] at h1
  exact Complex.ofReal_injective h1

/-- For positive L, M, and N and nonintegral phase difference k/M − i/N, bounds `Acoef` by
√(M/(LN)) times 2/π divided by the modular distance of k − Mi/N, under the supplied index
hypotheses ([Lemma A.7][Lomont2004]). -/
theorem lemma_A7 (L M N i k : ℕ) (hL : 0 < L) (hM : 0 < M) (hN : 0 < N)
    (_hi : i < N) (_hk : k < M)
    (hnotint : ¬ ∃ z : ℤ, (k : ℝ) / (M : ℝ) - (i : ℝ) / (N : ℝ) = (z : ℝ)) :
    ‖Acoef L M N i k‖ ≤
      Real.sqrt ((M : ℝ) / ((L : ℝ) * (N : ℝ))) * (2 / Real.pi) *
        (1 / distMod (M : ℝ) ((k : ℝ) - (M : ℝ) / (N : ℝ) * (i : ℝ))) := by
  set w : ℂ := (omega N ^ i)⁻¹ * omega M ^ k with hw
  set t : ℝ := (k : ℝ) / (M : ℝ) - (i : ℝ) / (N : ℝ) with ht
  set y : ℝ := (k : ℝ) - (M : ℝ) / (N : ℝ) * (i : ℝ) with hy
  set n : ℤ := nearInt t with hn
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hLMN : (0 : ℝ) < ((L * M * N : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.mul_pos hL hM) hN

  have hterm : ∀ a : ℕ, (omega N ^ (a * i))⁻¹ * (omega M ^ (a * k)) = w ^ a := by
    intro a
    have h1 : ((omega N ^ i)⁻¹) ^ a = (omega N ^ (a * i))⁻¹ := by
      rw [inv_pow, ← pow_mul, Nat.mul_comm i a]
    have h2 : (omega M ^ k) ^ a = omega M ^ (a * k) := by
      rw [← pow_mul, Nat.mul_comm k a]
    rw [hw, mul_pow, h1, h2]
  have hsum : ∑ a ∈ Finset.range (L * N), (omega N ^ (a * i))⁻¹ * (omega M ^ (a * k))
      = ∑ a ∈ Finset.range (L * N), w ^ a := by
    apply Finset.sum_congr rfl
    intro a _
    exact hterm a
  have hA : Acoef L M N i k = ((Real.sqrt ((L * M * N : ℕ) : ℝ) : ℂ))⁻¹ *
      ∑ a ∈ Finset.range (L * N), w ^ a := by
    simp only [Acoef, hsum]

  have hw1 : ‖w‖ = 1 :=
    norm_omega_ratio M N i k (Nat.pos_iff_ne_zero.mp hM) (Nat.pos_iff_ne_zero.mp hN)
  have hwne : w ≠ 1 := omega_ratio_ne_one M N i k (Nat.pos_iff_ne_zero.mp hM)
    (Nat.pos_iff_ne_zero.mp hN) hnotint
  have hS : ‖∑ a ∈ Finset.range (L * N), w ^ a‖ ≤ 2 / ‖1 - w‖ :=
    norm_geom_sum_le w (L * N) hwne hw1
  have hratio : w = Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
    rw [hw, ht]
    exact omega_ratio_eq M N i k (Nat.pos_iff_ne_zero.mp hM) (Nat.pos_iff_ne_zero.mp hN)
  have hwlower : Real.pi * |t - (n : ℝ)| ≤ ‖1 - w‖ := by
    rw [hratio]
    have h := pi_mul_dist_le_norm t
    rwa [← hn] at h

  have harg : y / (M : ℝ) = t := by
    rw [hy, ht]
    field_simp
  have hyM : y = (M : ℝ) * t := by
    rw [hy, ht]
    field_simp
  have hd_eq : distMod (M : ℝ) y = (M : ℝ) * |t - (n : ℝ)| := by
    unfold distMod
    rw [harg, hyM, ← hn]
    rw [show (M : ℝ) * t - (M : ℝ) * (nearInt t : ℝ) =
      (M : ℝ) * (t - (nearInt t : ℝ)) by ring]
    rw [abs_mul, abs_of_pos hMpos]
  have hdne : distMod (M : ℝ) y ≠ 0 := by
    rw [hd_eq]
    intro h0
    apply hnotint
    have habs : |t - (n : ℝ)| = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h (ne_of_gt hMpos)
      · exact h
    have htn : t = (n : ℝ) := by
      have := abs_eq_zero.mp habs
      linarith
    exact ⟨n, htn⟩
  have hdpos : 0 < Real.pi * |t - (n : ℝ)| := by
    have hne : |t - (n : ℝ)| ≠ 0 := by
      intro h
      apply hdne
      rw [hd_eq, h, mul_zero]
    have hpos : 0 < |t - (n : ℝ)| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
    exact mul_pos Real.pi_pos hpos
  have hc : 0 < Real.sqrt ((L * M * N : ℕ) : ℝ) := Real.sqrt_pos.mpr hLMN

  have hcn : ‖((Real.sqrt ((L * M * N : ℕ) : ℝ) : ℂ))⁻¹‖
      = (Real.sqrt ((L * M * N : ℕ) : ℝ))⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have step1 : ‖Acoef L M N i k‖
      = (Real.sqrt ((L * M * N : ℕ) : ℝ))⁻¹ * ‖∑ a ∈ Finset.range (L * N), w ^ a‖ := by
    rw [hA, norm_mul, hcn]
  have step2 : (Real.sqrt ((L * M * N : ℕ) : ℝ))⁻¹ * ‖∑ a ∈ Finset.range (L * N), w ^ a‖
      ≤ (Real.sqrt ((L * M * N : ℕ) : ℝ))⁻¹ * (2 / ‖1 - w‖) := by
    have h0 : (0 : ℝ) ≤ (Real.sqrt ((L * M * N : ℕ) : ℝ))⁻¹ :=
      inv_nonneg.mpr (Real.sqrt_nonneg _)
    exact mul_le_mul_of_nonneg_left hS h0
  have step3 : (Real.sqrt ((L * M * N : ℕ) : ℝ))⁻¹ * (2 / ‖1 - w‖)
      ≤ (Real.sqrt ((L * M * N : ℕ) : ℝ))⁻¹ * (2 / (Real.pi * |t - (n : ℝ)|)) := by
    have h0 : (0 : ℝ) ≤ (Real.sqrt ((L * M * N : ℕ) : ℝ))⁻¹ :=
      inv_nonneg.mpr (Real.sqrt_nonneg _)
    refine mul_le_mul_of_nonneg_left ?_ h0
    exact div_le_div_of_nonneg_left (by norm_num) hdpos hwlower
  have hsq : Real.sqrt ((M : ℝ) / ((L : ℝ) * (N : ℝ))) *
      Real.sqrt ((L * M * N : ℕ) : ℝ) = (M : ℝ) := by
    rw [← Real.sqrt_mul (le_of_lt (div_pos hMpos (mul_pos hLpos hNpos)))]
    have hprod : ((M : ℝ) / ((L : ℝ) * (N : ℝ))) * ((L * M * N : ℕ) : ℝ) = (M : ℝ) ^ 2 := by
      have hLN : (L : ℝ) * (N : ℝ) ≠ 0 := ne_of_gt (mul_pos hLpos hNpos)
      push_cast
      field_simp
    rw [hprod]
    exact Real.sqrt_sq (le_of_lt hMpos)
  have hsqrt_eq : Real.sqrt ((M : ℝ) / ((L : ℝ) * (N : ℝ)))
      = (M : ℝ) / Real.sqrt ((L * M * N : ℕ) : ℝ) := by
    rw [eq_div_iff (ne_of_gt hc)]
    exact hsq
  have step4 : (Real.sqrt ((L * M * N : ℕ) : ℝ))⁻¹ * (2 / (Real.pi * |t - (n : ℝ)|))
      = Real.sqrt ((M : ℝ) / ((L : ℝ) * (N : ℝ))) * (2 / Real.pi) *
        (1 / distMod (M : ℝ) y) := by
    rw [hd_eq, hsqrt_eq]
    have hcne : Real.sqrt ((L * M * N : ℕ) : ℝ) ≠ 0 := ne_of_gt hc
    have hpne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have htne : |t - (n : ℝ)| ≠ 0 := by
      intro h
      apply hdne
      rw [hd_eq, h, mul_zero]
    field_simp [hMne, hcne, hpne, htne]
  calc ‖Acoef L M N i k‖
      = (Real.sqrt ((L * M * N : ℕ) : ℝ))⁻¹ * ‖∑ a ∈ Finset.range (L * N), w ^ a‖ := step1
    _ ≤ (Real.sqrt ((L * M * N : ℕ) : ℝ))⁻¹ * (2 / ‖1 - w‖) := step2
    _ ≤ (Real.sqrt ((L * M * N : ℕ) : ℝ))⁻¹ * (2 / (Real.pi * |t - (n : ℝ)|)) := step3
    _ = Real.sqrt ((M : ℝ) / ((L : ℝ) * (N : ℝ))) * (2 / Real.pi) *
        (1 / distMod (M : ℝ) y) := step4

/-- Establishes `lemma_A7Statement` under its positive-size, index, and nonintegral
phase-difference hypotheses. -/
theorem lemma_A7_statement (L M N i k : ℕ) (hL : 0 < L) (hM : 0 < M) (hN : 0 < N)
    (hi : i < N) (hk : k < M)
    (hnotint : ¬ ∃ z : ℤ, (k : ℝ) / (M : ℝ) - (i : ℝ) / (N : ℝ) = (z : ℝ)) :
    lemma_A7Statement L M N i k hL hM hN hi hk hnotint := by
  unfold lemma_A7Statement
  exact lemma_A7 L M N i k hL hM hN hi hk hnotint

end

end Qatlib.Papers.HiddenSubgrp04.MainResults
