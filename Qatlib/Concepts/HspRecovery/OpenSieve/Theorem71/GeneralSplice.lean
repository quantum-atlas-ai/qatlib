/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.OpenSieve.NonabelianSieveExt

/-!
# Product characters and composed abelian costs

This module defines characters on finite products of cyclic groups and the subgroup of labels
supported at one distinguished coordinate. It proves multiplicativity in both character
arguments and reduces a character on that subgroup to its single active coordinate, as used in
the abelian setting of [Kuperberg2005].

The cost estimates combine a bound on sums of square roots with cardinality and output-length
bounds for the product label space.

## Main statements

* `prodChar_lastCoord`: reduce a supported product character to one coordinate.
* `cost_composition`: bound the exponential of a sum of square roots.
* `theorem71_cost_from_output_length`: control the cardinality-based cost by the sum of
  coordinate bit lengths.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.HspRecovery.OpenSieve.GeneralSplice

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The product label type with one coordinate in `ZMod (N j)` for each index `j`. -/
abbrev Label (N : ι → ℕ) := (j : ι) → ZMod (N j)

/-- The product of the standard cyclic additive characters evaluated on the coordinate products
of `k` and `s`. -/
def prodChar (N : ι → ℕ) [∀ j, NeZero (N j)] (k s : Label N) : ℂ :=
  ∏ j, ZMod.stdAddChar (s j * k j)

/-- A product character evaluated at the zero argument is one. -/
@[simp] theorem prodChar_zero (N : ι → ℕ) [∀ j, NeZero (N j)] (k : Label N) :
    prodChar N k 0 = 1 := by
  simp only [prodChar, Pi.zero_apply, zero_mul, AddChar.map_zero_eq_one, Finset.prod_const_one]

/-- A product character sends addition of its argument to multiplication of character values. -/
theorem prodChar_add (N : ι → ℕ) [∀ j, NeZero (N j)] (k s t : Label N) :
    prodChar N k (s + t) = prodChar N k s * prodChar N k t := by
  simp only [prodChar, Pi.add_apply, add_mul, AddChar.map_add_eq_mul, Finset.prod_mul_distrib]

/-- Addition of character labels corresponds to multiplication of the associated product
character values. -/
theorem prodChar_add_label (N : ι → ℕ) [∀ j, NeZero (N j)] (k l s : Label N) :
    prodChar N (k + l) s = prodChar N k s * prodChar N l s := by
  simp only [prodChar, Pi.add_apply, mul_add, AddChar.map_add_eq_mul, Finset.prod_mul_distrib]

/-- The additive subgroup of product labels vanishing outside the distinguished coordinate `i₀`. -/
def lastCoord (N : ι → ℕ) (i₀ : ι) : AddSubgroup (Label N) where
  carrier := {k | ∀ j, j ≠ i₀ → k j = 0}
  zero_mem' := by intro j _; simp
  add_mem' := by
    intro a b ha hb j hj
    rw [Pi.add_apply, ha j hj, hb j hj, add_zero]
  neg_mem' := by
    intro a ha j hj
    rw [Pi.neg_apply, ha j hj, neg_zero]

/-- A label belongs to `lastCoord N i₀` exactly when all coordinates other than `i₀` vanish. -/
@[simp] theorem mem_lastCoord {N : ι → ℕ} {i₀ : ι} {k : Label N} :
    k ∈ lastCoord N i₀ ↔ ∀ j, j ≠ i₀ → k j = 0 := Iff.rfl

/-- The sum of two labels supported at the distinguished coordinate remains supported there. -/
theorem lastCoord_add {N : ι → ℕ} {i₀ : ι} {k l : Label N}
    (hk : k ∈ lastCoord N i₀) (hl : l ∈ lastCoord N i₀) :
    k + l ∈ lastCoord N i₀ :=
  (lastCoord N i₀).add_mem hk hl

/-- The difference of two labels supported at the distinguished coordinate remains supported
there [Kuperberg2005]. -/
theorem lastCoord_sub {N : ι → ℕ} {i₀ : ι} {k l : Label N}
    (hk : k ∈ lastCoord N i₀) (hl : l ∈ lastCoord N i₀) :
    k - l ∈ lastCoord N i₀ :=
  (lastCoord N i₀).sub_mem hk hl

/-- For a label supported at one coordinate, its product character equals the standard additive
character at that coordinate [Kuperberg2005]. -/
theorem prodChar_lastCoord (N : ι → ℕ) [∀ j, NeZero (N j)] {i₀ : ι} {k : Label N}
    (hk : k ∈ lastCoord N i₀) (s : Label N) :
    prodChar N k s = ZMod.stdAddChar (s i₀ * k i₀) := by
  rw [prodChar, Finset.prod_eq_single i₀]
  · intro j _ hj
    rw [hk j hj, mul_zero, AddChar.map_zero_eq_one]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

/-- Two labels supported at the distinguished coordinate have equal product character values if
their products with the corresponding argument coordinate agree. -/
theorem prodChar_lastCoord_congr (N : ι → ℕ) [∀ j, NeZero (N j)] {i₀ : ι} {k l : Label N}
    (hk : k ∈ lastCoord N i₀) (hl : l ∈ lastCoord N i₀) (s : Label N)
    (h : s i₀ * k i₀ = s i₀ * l i₀) :
    prodChar N k s = prodChar N l s := by
  rw [prodChar_lastCoord N hk, prodChar_lastCoord N hl, h]

/-- The cardinality of the product label type is the product of the cyclic moduli
[Kuperberg2005]. -/
theorem card_label (N : ι → ℕ) [∀ j, NeZero (N j)] :
    Fintype.card (Label N) = ∏ j, N j := by
  simp [Label, Fintype.card_pi, ZMod.card]

/-- The sum of square roots of nonnegative terms is at most the square root of the number of
terms times their sum. -/
theorem sum_sqrt_le_sqrt_card_mul_sum (b : ι → ℝ) (hb : ∀ j, 0 ≤ b j) :
    (∑ j, Real.sqrt (b j)) ≤ Real.sqrt ((Fintype.card ι : ℝ) * ∑ j, b j) := by
  have hsq : (∑ j, Real.sqrt (b j)) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ j, b j := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ)
      (fun _ : ι => (1 : ℝ)) (fun j => Real.sqrt (b j))
    have h1 : (∑ j, Real.sqrt (b j)) ^ 2
        = (∑ j, (1 : ℝ) * Real.sqrt (b j)) ^ 2 := by simp
    rw [h1]
    calc (∑ j, (1 : ℝ) * Real.sqrt (b j)) ^ 2
        ≤ (∑ _j : ι, (1 : ℝ) ^ 2) * ∑ j, (Real.sqrt (b j)) ^ 2 := hcs
      _ = (Fintype.card ι : ℝ) * ∑ j, b j := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          simp only [one_pow, mul_one]
          congr 1
          exact Finset.sum_congr rfl fun j _ => Real.sq_sqrt (hb j)
  have hnn : 0 ≤ ∑ j, Real.sqrt (b j) :=
    Finset.sum_nonneg fun j _ => Real.sqrt_nonneg (b j)
  have hrhs : 0 ≤ (Fintype.card ι : ℝ) * ∑ j, b j := by
    have : 0 ≤ ∑ j, b j := Finset.sum_nonneg fun j _ => hb j
    exact mul_nonneg (Nat.cast_nonneg _) this
  calc (∑ j, Real.sqrt (b j))
      = Real.sqrt ((∑ j, Real.sqrt (b j)) ^ 2) := (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((Fintype.card ι : ℝ) * ∑ j, b j) := Real.sqrt_le_sqrt hsq

/-- For nonnegative `C` and `b`, the exponential cost with exponent `C` times the sum of square
roots is bounded using the square root of the cardinality times the sum [Kuperberg2005]. -/
theorem cost_composition (C : ℝ) (hC : 0 ≤ C) (b : ι → ℝ) (hb : ∀ j, 0 ≤ b j) :
    (2 : ℝ) ^ (C * ∑ j, Real.sqrt (b j))
      ≤ (2 : ℝ) ^ (C * Real.sqrt ((Fintype.card ι : ℝ) * ∑ j, b j)) := by
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  exact mul_le_mul_of_nonneg_left (sum_sqrt_le_sqrt_card_mul_sum b hb) hC

/-- The index cardinality is at most the sum of the coordinate bounds `Nat.log2 (N j) + 1`. -/
theorem card_le_sum_log (N : ι → ℕ) :
    Fintype.card ι ≤ ∑ j, (Nat.log2 (N j) + 1) := by
  rw [show Fintype.card ι = ∑ _j : ι, (1 : ℕ) from by simp]
  exact Finset.sum_le_sum fun j _ => by omega

/-- The natural logarithm of the product label cardinality is at most the sum of the coordinate
bit-length bounds [Kuperberg2005]. -/
theorem log_card_label_le (N : ι → ℕ) [∀ j, NeZero (N j)] :
    Real.log (Fintype.card (Label N)) ≤ ∑ j, ((Nat.log2 (N j) + 1 : ℕ) : ℝ) := by
  have hN : ∀ j, 1 ≤ N j := fun j => by
    have h : N j ≠ 0 := NeZero.ne (N j)
    omega
  rw [card_label N]
  push_cast
  rw [Real.log_prod (fun j _ => by have h := hN j; positivity)]
  refine Finset.sum_le_sum fun j _ => ?_
  have hpos : (0 : ℝ) < (N j : ℝ) := by have h := hN j; exact_mod_cast h
  have hpow : (N j : ℝ) ≤ (2 : ℝ) ^ ((Nat.log2 (N j) : ℝ) + 1) := by
    have h2 : (N j : ℝ) < ((2 : ℝ) ^ (Nat.log2 (N j) + 1 : ℕ)) := by
      have h2' : N j < 2 ^ (Nat.log2 (N j) + 1) := by
        simpa [Nat.log2_eq_log_two] using!
          Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (N j)
      exact_mod_cast h2'
    have h4 : ((2 : ℝ) ^ (Nat.log2 (N j) + 1 : ℕ))
        = (2 : ℝ) ^ ((Nat.log2 (N j) : ℝ) + 1) := by
      rw [show ((Nat.log2 (N j) : ℝ) + 1)
          = ((Nat.log2 (N j) + 1 : ℕ) : ℝ) by push_cast; ring]
      rw [Real.rpow_natCast]
    rw [h4] at h2
    exact le_of_lt h2
  have hlog2 : Real.log 2 ≤ 1 :=
    (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)).mpr
      (by linarith [Real.exp_one_gt_two])
  calc Real.log (N j)
      ≤ Real.log ((2 : ℝ) ^ ((Nat.log2 (N j) : ℝ) + 1)) :=
        Real.log_le_log hpos hpow
    _ = ((Nat.log2 (N j) : ℝ) + 1) * Real.log 2 := Real.log_rpow (by norm_num) _
    _ ≤ ((Nat.log2 (N j) : ℝ) + 1) * 1 :=
        mul_le_mul_of_nonneg_left hlog2 (by positivity)
    _ = ((Nat.log2 (N j) : ℝ) + 1) := by ring

/-- For nonnegative `C`, the exponential cost based on the square root of log cardinality is
bounded by the cost based on the square root of the total coordinate bit-length bound
[Kuperberg2005]. -/
theorem theorem71_cost_from_output_length (C : ℝ) (hC : 0 ≤ C) (N : ι → ℕ)
    [∀ j, NeZero (N j)] :
    (2 : ℝ) ^ (C * Real.sqrt (Real.log (Fintype.card (Label N))))
      ≤ (2 : ℝ) ^ (C * Real.sqrt (∑ j, ((Nat.log2 (N j) + 1 : ℕ) : ℝ))) := by
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  exact mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (log_card_label_le N)) hC

end Qatlib.Concepts.HspRecovery.OpenSieve.GeneralSplice
