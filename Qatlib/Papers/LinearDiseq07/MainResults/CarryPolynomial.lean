/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Finite-field polynomials for addition carries

`digitIndicator` constructs finite-field digit indicators, and `carryPoly` sums their products
over pairs whose sum produces a base-`p` carry. For prime `p`, evaluation on digits gives the
carry bit, and `source_lemma4_carry_polynomial` packages the construction with total degree at
most `2 * p - 2`. See [Ivanyos2008] for the paper context.

## Main statements

* `carryPoly_totalDegree_le`: If `p ≥ 2`, the carry polynomial has total degree at most `2 * p -
  2`.
* `carryPoly_eval`: For prime `p` and digits `a, b < p`, the carry polynomial evaluates to zero
  if `a + b < p` and to one otherwise.
* `source_lemma4_carry_polynomial`: For prime `p`, there exists a bivariate polynomial over
  `ZMod p` of total degree at most `2 * p - 2` evaluating to the carry bit of every pair of
  base-`p` digits.

## References

* [Ivanyos, 2008][Ivanyos2008]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.LinearDiseq07.MainResults

open MvPolynomial

variable {p : ℕ} [hp : Fact p.Prime]

/-- The polynomial `1 - (X i - C d) ^ (p - 1)` over `ZMod p` used to select a digit value. -/
def digitIndicator (p : ℕ) (i : Fin 2) (d : ℕ) : MvPolynomial (Fin 2) (ZMod p) :=
  1 - (X i - C (d : ZMod p)) ^ (p - 1)

/-- The sum of products of the two digit-indicator polynomials over digit pairs whose natural
sum is at least `p`. -/
def carryPoly (p : ℕ) : MvPolynomial (Fin 2) (ZMod p) :=
  ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range p,
    if p ≤ i + j then digitIndicator p 0 i * digitIndicator p 1 j else 0

/-- The total degree of a digit-indicator polynomial is at most `p - 1`. -/
lemma totalDegree_digitIndicator (i : Fin 2) (d : ℕ) :
    (digitIndicator p i d).totalDegree ≤ p - 1 := by
  have hlin : (X i - C (d : ZMod p) : MvPolynomial (Fin 2) (ZMod p)).totalDegree ≤ 1 := by
    refine (totalDegree_sub _ _).trans ?_
    rw [totalDegree_X, totalDegree_C, max_eq_left (Nat.zero_le 1)]
  have hpow : ((X i - C (d : ZMod p)) ^ (p - 1) : MvPolynomial (Fin 2) (ZMod p)).totalDegree
      ≤ p - 1 := by
    calc ((X i - C (d : ZMod p)) ^ (p - 1) : MvPolynomial (Fin 2) (ZMod p)).totalDegree
        ≤ (p - 1) * (X i - C (d : ZMod p) : MvPolynomial (Fin 2) (ZMod p)).totalDegree :=
          totalDegree_pow _ _
      _ ≤ (p - 1) * 1 := Nat.mul_le_mul_left _ hlin
      _ = p - 1 := Nat.mul_one _
  unfold digitIndicator
  refine (totalDegree_sub _ _).trans ?_
  rw [totalDegree_one]
  exact max_le (Nat.zero_le _) hpow

/-- If `p ≥ 2`, the carry polynomial has total degree at most `2 * p - 2` [Ivanyos, Lemma
4][Ivanyos2008]. -/
lemma carryPoly_totalDegree_le (h2 : 2 ≤ p) :
    (carryPoly p).totalDegree ≤ 2 * p - 2 := by
  have hterm : ∀ i ∈ Finset.range p,
      (∑ j ∈ Finset.range p,
        (if p ≤ i + j then digitIndicator p 0 i * digitIndicator p 1 j else 0)).totalDegree
        ≤ 2 * p - 2 := by
    intro i _
    refine totalDegree_finsetSum_le ?_
    intro j _
    split_ifs with h
    · refine (totalDegree_mul _ _).trans ?_
      have h0 := totalDegree_digitIndicator (p := p) 0 i
      have h1 := totalDegree_digitIndicator (p := p) 1 j
      omega
    · simp
  exact totalDegree_finsetSum_le hterm

/-- Evaluating a digit-indicator polynomial substitutes the chosen coordinate into `1 - (x i -
d) ^ (p - 1)`. -/
lemma eval_digitIndicator (x : Fin 2 → ZMod p) (i : Fin 2) (d : ℕ) :
    MvPolynomial.eval x (digitIndicator p i d) = 1 - (x i - (d : ZMod p)) ^ (p - 1) := by
  simp [digitIndicator]

/-- For prime `p` and natural digits `a, d < p`, the finite-field digit indicator equals one
when `a = d` and zero otherwise. -/
lemma indicator_natCast (a d : ℕ) (ha : a < p) (hd : d < p) :
    (1 : ZMod p) - (((a : ℕ) : ZMod p) - ((d : ℕ) : ZMod p)) ^ (p - 1)
      = if a = d then 1 else 0 := by
  have hiff : (((a : ℕ) : ZMod p) - ((d : ℕ) : ZMod p)) = 0 ↔ a = d := by
    rw [sub_eq_zero]
    exact ⟨fun h => (ZMod.natCast_eq_natCast_iff a d p).mp h |>.eq_of_lt_of_lt ha hd,
      fun h => by rw [h]⟩
  by_cases h : a = d
  · subst h
    have hz : (0 : ZMod p) ^ (p - 1) = 0 := zero_pow (by have := hp.out.two_le; omega)
    rw [if_pos rfl, sub_self, hz, sub_zero]
  · have hne : ((a : ℕ) : ZMod p) - ((d : ℕ) : ZMod p) ≠ 0 := fun h0 => h (hiff.mp h0)
    rw [if_neg h, ZMod.pow_card_sub_one_eq_one hne, sub_self]

/-- Evaluation of the carry polynomial expands as the sum of the evaluated digit-indicator
products over pairs with sum at least `p`. -/
lemma eval_carryPoly_eq_sum (x : Fin 2 → ZMod p) :
    MvPolynomial.eval x (carryPoly p)
      = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range p,
          (if p ≤ i + j then
            (1 - (x 0 - (i : ZMod p)) ^ (p - 1)) * (1 - (x 1 - (j : ZMod p)) ^ (p - 1))
          else 0) := by
  unfold carryPoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [map_mul, eval_digitIndicator, eval_digitIndicator]
  · rw [map_zero]

/-- For prime `p` and digits `a, b < p`, the carry polynomial evaluates to zero if `a + b < p`
and to one otherwise [Ivanyos, Lemma 4][Ivanyos2008]. -/
theorem carryPoly_eval (a b : ℕ) (ha : a < p) (hb : b < p) :
    MvPolynomial.eval ![((a : ℕ) : ZMod p), ((b : ℕ) : ZMod p)] (carryPoly p)
      = if a + b < p then 0 else 1 := by
  have hx0 : (![((a : ℕ) : ZMod p), ((b : ℕ) : ZMod p)] : Fin 2 → ZMod p) 0
      = ((a : ℕ) : ZMod p) := rfl
  have hx1 : (![((a : ℕ) : ZMod p), ((b : ℕ) : ZMod p)] : Fin 2 → ZMod p) 1
      = ((b : ℕ) : ZMod p) := rfl
  rw [eval_carryPoly_eq_sum, hx0, hx1]
  have hinner : ∀ i ∈ Finset.range p,
      (∑ j ∈ Finset.range p,
        (if p ≤ i + j then
          (1 - (((a : ℕ) : ZMod p) - (i : ZMod p)) ^ (p - 1))
          * (1 - (((b : ℕ) : ZMod p) - (j : ZMod p)) ^ (p - 1))
        else 0))
      = if a = i then (if p ≤ i + b then 1 else 0) else 0 := by
    intro i hi
    by_cases hai : a = i
    · subst hai
      have hterm : ∀ j ∈ Finset.range p, j ≠ b →
          (if p ≤ a + j then
            (1 - (((a : ℕ) : ZMod p) - (a : ZMod p)) ^ (p - 1))
            * (1 - (((b : ℕ) : ZMod p) - (j : ZMod p)) ^ (p - 1))
          else 0) = 0 := by
        intro j hj hjb
        rw [indicator_natCast b j hb (Finset.mem_range.mp hj), if_neg (Ne.symm hjb), mul_zero]
        split_ifs <;> rfl
      rw [Finset.sum_eq_single b hterm]
      · rw [if_pos rfl, indicator_natCast b b hb hb, if_pos rfl]
        have hz : (0 : ZMod p) ^ (p - 1) = 0 := zero_pow (by have := hp.out.two_le; omega)
        rw [sub_self, hz, sub_zero, one_mul]
      · intro hbnot
        exact absurd (Finset.mem_range.mpr hb) hbnot
    · have hterm : ∀ j ∈ Finset.range p,
          (if p ≤ i + j then
            (1 - (((a : ℕ) : ZMod p) - (i : ZMod p)) ^ (p - 1))
            * (1 - (((b : ℕ) : ZMod p) - (j : ZMod p)) ^ (p - 1))
          else 0) = 0 := by
        intro j hj
        rw [indicator_natCast a i ha (Finset.mem_range.mp hi), if_neg hai, zero_mul]
        split_ifs <;> rfl
      rw [Finset.sum_eq_zero hterm, if_neg hai]
  rw [Finset.sum_congr rfl hinner,
    Finset.sum_eq_single a (fun i _ hia => by rw [if_neg (Ne.symm hia)])
      (fun hanot => absurd (Finset.mem_range.mpr ha) hanot),
    if_pos rfl]
  by_cases hab : a + b < p
  · rw [if_neg (by omega), if_pos hab]
  · rw [if_pos (by omega), if_neg hab]

/-- For prime `p`, there exists a bivariate polynomial over `ZMod p` of total degree at most `2
* p - 2` evaluating to the carry bit of every pair of base-`p` digits [Ivanyos, Lemma
4][Ivanyos2008]. -/
theorem source_lemma4_carry_polynomial :
    ∃ C : MvPolynomial (Fin 2) (ZMod p),
      C.totalDegree ≤ 2 * p - 2 ∧
      ∀ a b : ℕ, a < p → b < p →
        MvPolynomial.eval ![((a : ℕ) : ZMod p), ((b : ℕ) : ZMod p)] C =
          if a + b < p then 0 else 1 :=
  ⟨carryPoly p, carryPoly_totalDegree_le hp.out.two_le,
    fun a b ha hb => carryPoly_eval (p := p) a b ha hb⟩

end Qatlib.Papers.LinearDiseq07.MainResults
