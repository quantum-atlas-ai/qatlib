/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.ENNReal.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.NNReal.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Lattice
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Binomial
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Binomial Chernoff bounds with binary relative entropy

This module defines `binaryKL`, explicit binomial masses, and upper tails beginning at the
natural ceiling of ΔN. It proves the relative-entropy Chernoff bound for `0 < p < Δ < 1` and
transfers it to Mathlib's `PMF.binomial`; such concentration estimates and relative entropy are
standard tools in quantum information [NielsenChuang2010].

## Main statements

* `binomial_chernoff_tail`: The explicit tail is at most exp(-N binaryKL(Δ,p)).
* `nativeTail_eq`: The native PMF tail agrees with the explicit finite sum.
* `native_chernoff`: The native tail satisfies the same bound with a positive rate.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators NNReal ENNReal
open Finset
namespace Qatlib.Foundations.ProbabilityCore.SharpBinomial

/-- The binary relative-entropy expression Δ log(Δ/p) + (1 - Δ) log((1 - Δ)/(1 - p)), using real
logarithms. -/
def binaryKL (Δ p : ℝ) : ℝ :=
  Δ*Real.log (Δ/p)+(1-Δ)*Real.log ((1-Δ)/(1-p))

/-- The real binomial mass expression `N.choose x * p ^ x * (1 - p) ^ (N - x)`. -/
def binomPMF (N : ℕ) (p : ℝ) (x : ℕ) : ℝ :=
  (N.choose x : ℝ) * p ^ x * (1 - p) ^ (N - x)

/-- The sum of binomial mass expressions over natural counts from `Nat.ceil (Δ * N)` through
`N`. -/
def binomTail (N : ℕ) (p Δ : ℝ) : ℝ :=
  ∑ x ∈ Finset.Icc (Nat.ceil (Δ * (N : ℝ))) N, binomPMF N p x

/-- The binary relative entropy `binaryKL Δ p` is strictly positive when `0 < p < Δ < 1`. -/
theorem binaryKL_pos (p Δ : ℝ) (hp : 0 < p) (hpΔ : p < Δ) (hΔ1 : Δ < 1) :
    0 < binaryKL Δ p := by
  have hΔp : 0 < Δ := lt_trans hp hpΔ
  have h1p : 0 < 1 - p := by linarith
  have h1Δ : 0 < 1 - Δ := by linarith
  have hpΔ1 : p / Δ ≠ 1 := by
    intro h
    rw [div_eq_iff (ne_of_gt hΔp)] at h
    linarith

  have hneglog : Real.log (Δ / p) = -Real.log (p / Δ) := by
    rw [Real.log_div (ne_of_gt hΔp) (ne_of_gt hp),
        Real.log_div (ne_of_gt hp) (ne_of_gt hΔp)]
    ring
  have hlt : Real.log (p / Δ) < p / Δ - 1 :=
    Real.log_lt_sub_one_of_pos (div_pos hp hΔp) hpΔ1
  have hstrict1 : Δ - p < Δ * Real.log (Δ / p) := by
    have hloglb : Real.log (Δ / p) > 1 - p / Δ := by
      rw [hneglog]
      have : -(p / Δ - 1) = 1 - p / Δ := by ring
      linarith
    have hfield : Δ * (1 - p / Δ) = Δ - p := by
      field_simp [ne_of_gt hΔp]
    nlinarith

  have hneg2 : Real.log ((1 - Δ) / (1 - p)) = -Real.log ((1 - p) / (1 - Δ)) := by
    rw [Real.log_div (ne_of_gt h1Δ) (ne_of_gt h1p),
        Real.log_div (ne_of_gt h1p) (ne_of_gt h1Δ)]
    ring
  have hloglb2 : p - Δ ≤ (1 - Δ) * Real.log ((1 - Δ) / (1 - p)) := by
    have hlb : 1 - (1 - p) / (1 - Δ) ≤ Real.log ((1 - Δ) / (1 - p)) := by
      rw [hneg2]
      linarith [Real.log_le_sub_one_of_pos (div_pos h1p h1Δ)]
    have hkey : (1 - Δ) * (1 - (1 - p) / (1 - Δ)) = p - Δ := by
      field_simp [ne_of_gt h1Δ]
      ring
    calc p - Δ = (1 - Δ) * (1 - (1 - p) / (1 - Δ)) := hkey.symm
      _ ≤ (1 - Δ) * Real.log ((1 - Δ) / (1 - p)) :=
          mul_le_mul_of_nonneg_left hlb h1Δ.le
  show 0 < Δ * Real.log (Δ / p) + (1 - Δ) * Real.log ((1 - Δ) / (1 - p))
  linarith [hstrict1, hloglb2]

/-- For `0 < p < Δ < 1`, the binomial upper tail is at most exp(-N binaryKL(Δ,p)). -/
theorem binomial_chernoff_tail (N : ℕ) (p Δ : ℝ) (hp : 0 < p)
    (hpΔ : p < Δ) (hΔ1 : Δ < 1) :
    binomTail N p Δ ≤ Real.exp (-(N : ℝ) * binaryKL Δ p) := by
  have hΔp : 0 < Δ := lt_trans hp hpΔ
  have h1p : 0 < 1 - p := by linarith
  have h1Δ : 0 < 1 - Δ := by linarith
  have hr₁01 : 0 < p / Δ ∧ p / Δ < 1 :=
    ⟨div_pos hp hΔp, (div_lt_one hΔp).2 hpΔ⟩
  have hr₂gt1 : 1 < (1 - p) / (1 - Δ) := by
    rw [one_lt_div h1Δ]
    linarith
  have hlogr₂ : 0 ≤ Real.log ((1 - p) / (1 - Δ)) := (Real.log_pos hr₂gt1).le

  have hexp : Real.exp (-(N : ℝ) * binaryKL Δ p)
      = (p / Δ) ^ (Δ * (N : ℝ)) * ((1 - p) / (1 - Δ)) ^ ((1 - Δ) * (N : ℝ)) := by
    have hneg1 : Real.log (Δ / p) = -Real.log (p / Δ) := by
      rw [Real.log_div (ne_of_gt hΔp) (ne_of_gt hp),
          Real.log_div (ne_of_gt hp) (ne_of_gt hΔp)]
      ring
    have hneg2 : Real.log ((1 - Δ) / (1 - p)) = -Real.log ((1 - p) / (1 - Δ)) := by
      rw [Real.log_div (ne_of_gt h1Δ) (ne_of_gt h1p),
          Real.log_div (ne_of_gt h1p) (ne_of_gt h1Δ)]
      ring
    rw [Real.rpow_def_of_pos (div_pos hp hΔp), Real.rpow_def_of_pos (div_pos h1p h1Δ),
      ← Real.exp_add, Real.exp_eq_exp]
    simp only [binaryKL, hneg1, hneg2]
    ring

  have hmono2 : ∀ a b : ℝ, a ≤ b →
      ((1 - p) / (1 - Δ)) ^ a ≤ ((1 - p) / (1 - Δ)) ^ b := by
    intro a b hab
    rw [Real.rpow_def_of_pos (div_pos h1p h1Δ), Real.rpow_def_of_pos (div_pos h1p h1Δ)]
    exact Real.exp_le_exp_of_le (mul_le_mul_of_nonneg_left hab hlogr₂)

  have hpoint : ∀ x : ℕ, x ≤ N → Δ * (N : ℝ) ≤ (x : ℝ) →
      binomPMF N p x ≤ Real.exp (-(N : ℝ) * binaryKL Δ p) * binomPMF N Δ x := by
    intro x hxn hx
    have hx1 : (p / Δ) ^ x ≤ (p / Δ) ^ (Δ * (N : ℝ)) := by
      rw [← Real.rpow_natCast (p / Δ) x]
      exact (Real.rpow_le_rpow_left_iff_of_base_lt_one hr₁01.1 hr₁01.2).2 hx
    have hsub : (((N - x : ℕ) : ℝ)) = (N : ℝ) - (x : ℝ) := by
      rw [Nat.cast_sub hxn]
    have hle2 : ((N - x : ℕ) : ℝ) ≤ (1 - Δ) * (N : ℝ) := by
      rw [hsub]
      have hexp : (N : ℝ) - (x : ℝ) ≤ (N : ℝ) - Δ * (N : ℝ) := by linarith
      have hring : (N : ℝ) - Δ * (N : ℝ) = (1 - Δ) * (N : ℝ) := by ring
      linarith
    have hxr2 : ((1 - p) / (1 - Δ)) ^ ((N - x : ℕ) : ℝ)
        ≤ ((1 - p) / (1 - Δ)) ^ ((1 - Δ) * (N : ℝ)) := hmono2 _ _ hle2
    have hprodle : (p / Δ) ^ x * ((1 - p) / (1 - Δ)) ^ ((N - x : ℕ) : ℝ)
        ≤ (p / Δ) ^ (Δ * (N : ℝ)) * ((1 - p) / (1 - Δ)) ^ ((1 - Δ) * (N : ℝ)) :=
      mul_le_mul hx1 hxr2
        (Real.rpow_nonneg (div_pos h1p h1Δ).le _)
        (Real.rpow_nonneg (div_pos hp hΔp).le _)
    have hnnΔ : 0 ≤ binomPMF N Δ x := by
      unfold binomPMF
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hΔp.le _))
        (pow_nonneg h1Δ.le _)
    calc binomPMF N p x
        = binomPMF N Δ x * ((p / Δ) ^ x * ((1 - p) / (1 - Δ)) ^ ((N - x : ℕ) : ℝ)) := by
          unfold binomPMF
          rw [Real.rpow_natCast, div_pow, div_pow]
          field_simp [pow_ne_zero _ (ne_of_gt hΔp), pow_ne_zero _ (ne_of_gt h1Δ)]
      _ ≤ binomPMF N Δ x * ((p / Δ) ^ (Δ * (N : ℝ)) *
            ((1 - p) / (1 - Δ)) ^ ((1 - Δ) * (N : ℝ))) :=
          mul_le_mul_of_nonneg_left hprodle hnnΔ
      _ = Real.exp (-(N : ℝ) * binaryKL Δ p) * binomPMF N Δ x := by
          rw [← hexp]
          ring

  have hnnΔall : ∀ x : ℕ, 0 ≤ binomPMF N Δ x := by
    intro x
    unfold binomPMF
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hΔp.le _))
      (pow_nonneg h1Δ.le _)
  have hsum : binomTail N p Δ
      ≤ Real.exp (-(N : ℝ) * binaryKL Δ p) *
          (∑ x ∈ Finset.Icc (Nat.ceil (Δ * (N : ℝ))) N, binomPMF N Δ x) := by
    have hpt : ∀ x ∈ Finset.Icc (Nat.ceil (Δ * (N : ℝ))) N,
        binomPMF N p x ≤ Real.exp (-(N : ℝ) * binaryKL Δ p) * binomPMF N Δ x := by
      intro x hx
      have hmem := Finset.mem_Icc.mp hx
      have hceil : Δ * (N : ℝ) ≤ (x : ℝ) := by
        have hc := Nat.le_ceil (Δ * (N : ℝ))
        have hx' : ((Nat.ceil (Δ * (N : ℝ)) : ℕ) : ℝ) ≤ (x : ℝ) := by
          exact_mod_cast hmem.1
        linarith
      exact hpoint x hmem.2 hceil
    rw [binomTail, Finset.mul_sum]
    exact Finset.sum_le_sum hpt

  have htailΔ : (∑ x ∈ Finset.Icc (Nat.ceil (Δ * (N : ℝ))) N, binomPMF N Δ x) ≤ 1 := by
    have hsub : Finset.Icc (Nat.ceil (Δ * (N : ℝ))) N ⊆ Finset.range (N + 1) := by
      intro x hx
      have hmem := Finset.mem_Icc.mp hx
      simp only [Finset.mem_range]
      omega
    have hsd : (∑ x ∈ Finset.range (N + 1) \ Finset.Icc (Nat.ceil (Δ * (N : ℝ))) N,
          binomPMF N Δ x) +
          ∑ x ∈ Finset.Icc (Nat.ceil (Δ * (N : ℝ))) N, binomPMF N Δ x =
        ∑ x ∈ Finset.range (N + 1), binomPMF N Δ x :=
      Finset.sum_sdiff hsub
    have hextra : (0 : ℝ) ≤ ∑ x ∈ Finset.range (N + 1) \
        Finset.Icc (Nat.ceil (Δ * (N : ℝ))) N, binomPMF N Δ x :=
      Finset.sum_nonneg (fun x _ => hnnΔall x)
    have htotal : (∑ x ∈ Finset.range (N + 1), binomPMF N Δ x) = 1 := by
      have hbinom : (Δ + (1 - Δ)) ^ N
          = ∑ m ∈ Finset.range (N + 1), Δ ^ m * (1 - Δ) ^ (N - m) * ↑(N.choose m) :=
        Commute.add_pow (Commute.all Δ (1 - Δ)) N
      have hone : Δ + (1 - Δ) = 1 := by ring
      calc ∑ x ∈ Finset.range (N + 1), binomPMF N Δ x
          = ∑ m ∈ Finset.range (N + 1), Δ ^ m * (1 - Δ) ^ (N - m) * ↑(N.choose m) := by
            unfold binomPMF
            apply Finset.sum_congr rfl
            intro m _
            ring
        _ = (Δ + (1 - Δ)) ^ N := hbinom.symm
        _ = 1 := by rw [hone, one_pow]
    calc ∑ x ∈ Finset.Icc (Nat.ceil (Δ * (N : ℝ))) N, binomPMF N Δ x
        ≤ (∑ x ∈ Finset.range (N + 1) \ Finset.Icc (Nat.ceil (Δ * (N : ℝ))) N,
              binomPMF N Δ x) +
            ∑ x ∈ Finset.Icc (Nat.ceil (Δ * (N : ℝ))) N, binomPMF N Δ x :=
          le_add_of_nonneg_left hextra
      _ = ∑ x ∈ Finset.range (N + 1), binomPMF N Δ x := hsd
      _ = 1 := htotal
  refine le_trans hsum ?_
  have h1 : Real.exp (-(N : ℝ) * binaryKL Δ p) *
      (∑ x ∈ Finset.Icc (Nat.ceil (Δ * (N : ℝ))) N, binomPMF N Δ x)
      ≤ Real.exp (-(N : ℝ) * binaryKL Δ p) * 1 :=
    mul_le_mul_of_nonneg_left htailΔ (Real.exp_nonneg _)
  rw [mul_one] at h1
  exact h1

/-- For `N ≥ 1` and `0 < p < Δ < 1`, the binomial upper tail satisfies the relative-entropy
exponential bound and its rate is strictly positive. -/
theorem binomial_chernoff
    (N : ℕ) (p Δ : ℝ) (_hN : 1 ≤ N) (hp : 0 < p) (hpΔ : p < Δ) (hΔ1 : Δ < 1) :
    binomTail N p Δ ≤ Real.exp (-(N : ℝ) * binaryKL Δ p) ∧ 0 < binaryKL Δ p :=
  ⟨binomial_chernoff_tail N p Δ hp hpΔ hΔ1, binaryKL_pos p Δ hp hpΔ hΔ1⟩

/-- The real upper-tail probability computed from `PMF.binomial`, summing counts at least
`Nat.ceil (Δ * N)`. -/
def nativeTail (N : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (Δ : ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin (N+1) => Nat.ceil (Δ*(N : ℝ)) ≤ i.val),
    (PMF.binomial p hp N i).toReal

/-- The real mass of Mathlib's binomial PMF at a finite count equals the explicit `binomPMF`
expression. -/
theorem native_mass (N : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (i : Fin (N+1)) :
    (PMF.binomial p hp N i).toReal = binomPMF N p i.val := by
  have hi : i.val ≤ N := Nat.le_of_lt_succ i.isLt
  have h := PMF.binomial_apply_of_le hi hp
  have he : Fin.ofNat (N+1) i.val = i := by ext; simp
  rw [he] at h
  have hpR : (p : ℝ) ≤ 1 := by exact_mod_cast hp
  rw [← h, ENNReal.toReal_ofReal (by positivity)]
  unfold binomPMF
  ring

/-- The upper tail computed from `PMF.binomial` equals the explicit finite sum `binomTail`. -/
theorem nativeTail_eq (N : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (Δ : ℝ) :
    nativeTail N p hp Δ = binomTail N p Δ := by
  classical
  unfold nativeTail binomTail
  refine Finset.sum_bij (fun i _ => i.val) ?_ ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.mp hi).2,Nat.le_of_lt_succ i.isLt⟩
  · intro i _ j _ hij
    exact Fin.ext hij
  · intro j hj
    obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hj
    exact ⟨⟨j,Nat.lt_succ_of_le hu⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl⟩,rfl⟩
  · intro i _
    exact native_mass N p hp i

/-- For `0 < p < Δ < 1`, the native binomial upper tail satisfies the relative-entropy Chernoff
bound with strictly positive rate. -/
theorem native_chernoff (N : ℕ) (p : ℝ≥0) (hp : 0 < p) (Δ : ℝ)
    (hpΔ : (p : ℝ) < Δ) (hΔ1 : Δ < 1) :
    nativeTail N p (by exact_mod_cast hpΔ.le.trans hΔ1.le) Δ ≤
      Real.exp (-(N : ℝ)*binaryKL Δ p) ∧ 0 < binaryKL Δ p := by
  rw [nativeTail_eq]
  exact ⟨binomial_chernoff_tail N p Δ (by exact_mod_cast hp) hpΔ hΔ1,
    binaryKL_pos p Δ (by exact_mod_cast hp) hpΔ hΔ1⟩

end Qatlib.Foundations.ProbabilityCore.SharpBinomial
