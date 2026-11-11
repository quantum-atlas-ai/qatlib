/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 10: matching-probability lower bound

Formalises Lemma 10 of Liu--Shaydulin--Niroula et al., *Certified randomness
using a trapped-ion quantum processor*, fixed arXiv:2503.20498v1, Lemma 10,
p. 4 (Eq. I.14 and its proof Eqs. I.15--I.19).

The paper samples `s` coordinatewise from the product of the circuit output
distributions `p_{C_i}` and asks for the probability that at least one sampled
coordinate matches a fixed output `z`.  Writing `p i = p_{C_i}(z_i)`, the
coordinates are independent Bernoulli tests and the matching probability is
`1 - ∏ i, (1 - p i)` (the paper's Eq. I.18).  The paper proves

* `1 - ∏ (1 - p_i) ≥ Σ p_i - (Σ p_i)^2`   (second-order inclusion--exclusion),
* and, conditioned on `Σ p_i ≥ bk/N` with `k = O(n^2)` (so `bk/N ≤ 1/4`),
  the display Eq. I.19 `≥ bk/N - b^2 k^2 / N^2`.

We prove both statements outright.  The inclusion--exclusion step is replaced
by the equivalent exponential estimate `∏(1-p_i) ≤ exp(-Σp_i)`, which yields
the same quadratic lower bound and avoids a second-order error bookkeeping.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.RandCertLiu25.MainResults.ThresholdMatching

/-- **Union-bound product estimate.**  For `p i ∈ [0,1]` on a finite set,
`1 - Σ p i ≤ ∏ (1 - p i)` (the paper's Eq. I.15--I.18 in product form). -/
theorem one_sub_sum_le_prod_one_sub {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) :
    1 - ∑ i ∈ s, p i ≤ ∏ i ∈ s, (1 - p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hp0s : ∀ i ∈ s, 0 ≤ p i := fun i hi => hp0 i (Finset.mem_insert_of_mem hi)
      have hp1s : ∀ i ∈ s, p i ≤ 1 := fun i hi => hp1 i (Finset.mem_insert_of_mem hi)
      have hpa0 : 0 ≤ p a := hp0 a (Finset.mem_insert_self a s)
      have hpa1 : p a ≤ 1 := hp1 a (Finset.mem_insert_self a s)
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have h1 := ih hp0s hp1s
      have hS0 : 0 ≤ ∑ i ∈ s, p i := Finset.sum_nonneg hp0s
      have hprod_le : (1 - ∑ i ∈ s, p i) * (1 - p a) ≤
          (∏ i ∈ s, (1 - p i)) * (1 - p a) :=
        mul_le_mul_of_nonneg_right h1 (by linarith)
      nlinarith [mul_nonneg hpa0 hS0, hprod_le]

/-- **Second-order product estimate.**  For `p i ∈ [0,1]`,
`∏ (1 - p i) ≤ 1 - Σ p i + (Σ p i)^2`; this is the engine behind Eq. I.17. -/
theorem prod_one_sub_le_one_sub_sum_add_sq {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) :
    ∏ i ∈ s, (1 - p i) ≤ 1 - ∑ i ∈ s, p i + (∑ i ∈ s, p i) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have hp0s : ∀ i ∈ s, 0 ≤ p i := fun i hi => hp0 i (Finset.mem_insert_of_mem hi)
      have hp1s : ∀ i ∈ s, p i ≤ 1 := fun i hi => hp1 i (Finset.mem_insert_of_mem hi)
      have hpa0 : 0 ≤ p a := hp0 a (Finset.mem_insert_self a s)
      have hpa1 : p a ≤ 1 := hp1 a (Finset.mem_insert_self a s)
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have h1 := ih hp0s hp1s
      have hS0 : 0 ≤ ∑ i ∈ s, p i := Finset.sum_nonneg hp0s
      have hstep : (∏ i ∈ s, (1 - p i)) * (1 - p a) ≤
          (1 - ∑ i ∈ s, p i + (∑ i ∈ s, p i) ^ 2) * (1 - p a) :=
        mul_le_mul_of_nonneg_right h1 (by linarith)
      nlinarith [mul_nonneg hpa0 hS0, mul_nonneg hpa0 (sq_nonneg (∑ i ∈ s, p i)),
        mul_nonneg (mul_nonneg hpa0 hS0) hS0, hstep]

/-- The product of independent non-matching probabilities is at most the
exponential of minus the summed matching probability. -/
theorem prod_one_sub_le_exp_neg_sum {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (hp0 : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) :
    ∏ i ∈ s, (1 - p i) ≤ Real.exp (-∑ i ∈ s, p i) := by
  classical
  have hfac : ∀ i ∈ s, 1 - p i ≤ Real.exp (-p i) := fun i _ =>
    Real.one_sub_le_exp_neg (p i)
  have hnonneg : ∀ i ∈ s, 0 ≤ 1 - p i := fun i hi => by linarith [hp1 i hi]
  calc
    ∏ i ∈ s, (1 - p i) ≤ ∏ i ∈ s, Real.exp (-p i) :=
      Finset.prod_le_prod₀ hnonneg hfac
    _ = Real.exp (-∑ i ∈ s, p i) := by
      rw [← Finset.sum_neg_distrib]
      exact (Real.exp_sum s (fun i => -p i)).symm

/-- **Elementary exponential bound** `x - x^2 ≤ 1 - exp(-x)` for `x ≥ 0`. -/
theorem sub_sq_le_one_sub_exp_neg (x : ℝ) (hx : 0 ≤ x) :
    x - x ^ 2 ≤ 1 - Real.exp (-x) := by
  have hx1 : (0 : ℝ) < x + 1 := by linarith
  have h_exp : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
  have hpos : 0 < Real.exp x := Real.exp_pos x
  have hinv : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x
  have hle : (Real.exp x)⁻¹ ≤ (x + 1)⁻¹ :=
    (inv_le_inv₀ hpos hx1).mpr h_exp
  have hkey : x - x ^ 2 ≤ 1 - (x + 1)⁻¹ := by
    have hxne : x + 1 ≠ 0 := hx1.ne'
    field_simp
    nlinarith [pow_nonneg hx 3]
  rw [hinv]
  linarith

/-- **Lemma 10, first form** (Eq. I.18): the probability that some coordinate of
the output matches an independent sample is at least `Σ p_i - (Σ p_i)^2`. -/
theorem matching_probability_lower {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    (∑ i, p i) - (∑ i, p i) ^ 2 ≤ 1 - ∏ i, (1 - p i) := by
  classical
  have hprod := prod_one_sub_le_exp_neg_sum (Finset.univ) p
    (by simp [hp0]) (by simp [hp1])
  have hS0 : 0 ≤ ∑ i, p i := Finset.sum_nonneg (fun i _ => hp0 i)
  have hexp := sub_sq_le_one_sub_exp_neg (∑ i, p i) hS0
  linarith

/-- **Lemma 10, conditioned form** (Eq. I.19): if the output passes MLXEB so
that `Σ p_i ≥ bk/N`, and `bk/N ≤ 1/4`, then the matching probability is at
least `bk/N - b^2 k^2 / N^2` (written here as `s - s^2` with `s = bk/N`). -/
theorem matching_probability_passing {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (s : ℝ)
    (hs0 : 0 ≤ s) (hs : s ≤ ∑ i, p i) :
    s - s ^ 2 ≤ 1 - ∏ i, (1 - p i) := by
  classical
  let S : ℝ := ∑ i, p i
  have hprod := prod_one_sub_le_exp_neg_sum (Finset.univ) p
    (by simp [hp0]) (by simp [hp1])
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => hp0 i)
  have hS_le : Real.exp (-S) ≤ Real.exp (-s) := Real.exp_le_exp.mpr (by linarith)
  have hexp := sub_sq_le_one_sub_exp_neg s hs0
  have hmono : s - s ^ 2 ≤ 1 - Real.exp (-s) := hexp
  -- `1 - exp(-S) ≥ 1 - exp(-s)` because `exp(-S) ≤ exp(-s)`.
  have : 1 - Real.exp (-S) ≥ 1 - Real.exp (-s) := by linarith
  dsimp [S] at *
  linarith

end Qatlib.Papers.RandCertLiu25.MainResults.ThresholdMatching
