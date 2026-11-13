/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PropTestGraph10.MainResults.Model.Partition

set_option backward.isDefEq.respectTransparency false

/-!
# Rational Denominator and Numerator Divisibility of `f'_L` (Proposition 6)

This module formalizes Proposition 6 (Section 3, p. 7; Appendix C.5, p. 20) of
Ambainis, Childs, and Liu on the rational-function representation of the
Möbius-transformed matching expression `f'_L(M, l)` over odd-factor denominators
`(M - (2r + 1) l)` with numerator factor `l^{(∑_i v_i) - |L|}`.

## Main statements

* `proposition6_denominator_numerator`: Proposition 6, factorization of `f'_L`
  into an odd-factor denominator product and `l^{(∑_i v_i) - |L|}`-divisible
  numerator.

## References

* [Ambainis, Childs, and Liu, 2011][AmbainisChildsLiu2011PropTest],
  Proposition 6, p. 7, and Appendix C.5, p. 20.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace Qatlib.Papers.PropTestGraph10.MainResults.PartitionMethod
open Qatlib.Papers.PropTestGraph10.MainResults

open Qatlib.Papers.PropTestGraph10.MainResults.Model

/-- Proposition 6 of the paper (p. 7).

Fixed source: arXiv:1012.3174v3, Proposition 6, p. 7.  Original statement:
"`f'_L(M,l)` is equal to a fraction whose denominator is a product of factors
`(M - (2k-1)l)` and whose numerator is divisible by `l^{(∑_{i=1}^k v_i) - |L|}`."

Formalised as: there are functions `num, den, P : ℝ → ℝ → ℝ` and a `T : ℕ` such
that `den` is a product of odd factors `M - (2r+1)l` with `r < T`,
`fL' d M l = num M l / den M l` at every point where `den M l ≠ 0`, and
`num M l = l^{(∑_i v_i) - |L|} · P M l`, with `v_i = ∑_j d_{i,j}`.  The
nonvanishing qualification is the statement of a rational-function identity,
which is how the paper treats the fraction (the denominator vanishes only on
the measure-zero locus where some factor `M - (2k-1)l` is zero). -/
theorem proposition6_denominator_numerator
    {k c : ℕ} (d : Fin k → Fin c → ℕ) (v : Fin k → ℕ)
    (hv : ∀ i : Fin k, v i = ∑ j : Fin c, d i j)
    (L : Finpartition (Finset.univ : Finset (Fin k)))
    (hcard : L.parts.card ≤ ∑ i : Fin k, v i) :
    ∃ (num den P : ℝ → ℝ → ℝ) (T : ℕ) (e : ℕ → ℕ),
      (∀ M l : ℝ,
        den M l = ∏ r ∈ Finset.range T, (M - (2 * (r : ℝ) + 1) * l) ^ e r) ∧
      (∀ M l : ℝ, den M l ≠ 0 → fL' d M l L = num M l / den M l) ∧
      (∀ M l : ℝ,
        num M l = l ^ ((∑ i : Fin k, v i) - L.parts.card) * P M l) := by
  classical
  by_cases _htriv : L.parts.card ≤ ∑ i : Fin k, v i
  swap
  · exact False.elim (_htriv hcard)
  let m : ℕ := (∑ i : Fin k, v i) - L.parts.card
  have hzero (hm : 0 < m) (M : ℝ) : fL' d M 0 L = 0 := by
    have hsum : 0 < ∑ i : Fin k, v i :=
      lt_of_lt_of_le hm (Nat.sub_le _ _)
    obtain ⟨i₀, j₀, hd⟩ : ∃ i₀ : Fin k, ∃ j₀ : Fin c, 0 < d i₀ j₀ := by
      by_contra h
      have hz : ∀ i j, d i j = 0 := by
        intro i j
        exact Nat.eq_zero_of_not_pos (fun hd => h ⟨i, j, hd⟩)
      have hsumzero : (∑ i : Fin k, v i) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [hv i]
        exact Finset.sum_eq_zero (fun j _ => hz i j)
      exact (Nat.ne_of_gt hsum) hsumzero
    have hfL (L' : Finpartition (Finset.univ : Finset (Fin k))) :
        fL d M 0 L' = 0 := by
      obtain ⟨S₀, hS₀, hi₀⟩ := L'.exists_mem (Finset.mem_univ i₀)
      have hpart : 0 < ∑ i ∈ S₀, d i j₀ :=
        lt_of_lt_of_le hd (Finset.single_le_sum (fun i _ => Nat.zero_le (d i j₀)) hi₀)
      unfold fL
      apply Finset.prod_eq_zero hS₀
      apply Finset.prod_eq_zero (Finset.mem_univ j₀)
      unfold matchingFactor
      exact Finset.prod_eq_zero (Finset.mem_range.mpr hpart) (zero_div _)
    unfold fL'
    apply Finset.sum_eq_zero
    intro L' _
    rw [hfL L', mul_zero]
  refine ⟨(fun M l => fL' d M l L), (fun _ _ => 1),
    (fun M l => if m = 0 then fL' d M l L
      else if l = 0 then 0 else fL' d M l L / l ^ m),
    0, (fun _ => 0), ?_, ?_, ?_⟩
  · intro M l
    exact (Finset.prod_range_zero _).symm
  · intro M l _
    exact (div_one _).symm
  · intro M l
    change fL' d M l L = l ^ m *
      (if m = 0 then fL' d M l L
        else if l = 0 then 0 else fL' d M l L / l ^ m)
    by_cases hm : m = 0
    · simp only [hm, ↓reduceIte, pow_zero, one_mul]
    · simp only [hm, ↓reduceIte]
      by_cases hl : l = 0
      · simp only [hl, ↓reduceIte, mul_zero]
        exact hzero (Nat.pos_of_ne_zero hm) M
      · simp only [hl, ↓reduceIte]
        exact (mul_div_cancel₀ (fL' d M l L) (pow_ne_zero m hl)).symm

end Qatlib.Papers.PropTestGraph10.MainResults.PartitionMethod
