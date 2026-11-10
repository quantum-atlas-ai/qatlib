/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZetaCurve04.MainResults.Theorem1.NewtonGirard
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ZetaCurve04.MainResults.Theorem1

open Qatlib.Papers.ZetaCurve04.MainResults.Defs

def reciprocalExtend (q g : ℕ) (a : ℕ → ℚ) : ℕ → ℚ :=
  fun k => if k ≤ g then a k else (q : ℚ) ^ (k - g) * a (g - (k - g))

theorem reciprocalExtend_low {q g : ℕ} {a : ℕ → ℚ} {k : ℕ} (hk : k ≤ g) :
    reciprocalExtend q g a k = a k := by
  simp [reciprocalExtend, hk]

theorem reciprocalExtend_high {q g : ℕ} {a : ℕ → ℚ} {k : ℕ} (hk : g < k) :
    reciprocalExtend q g a k = (q : ℚ) ^ (k - g) * a (g - (k - g)) := by
  simp [reciprocalExtend, Nat.not_le.mpr hk]

theorem reciprocalExtend_spec {q g : ℕ} {a : ℕ → ℚ} {i : ℕ} (hi : i ≤ g) :
    reciprocalExtend q g a (g + i) = (q : ℚ) ^ i * reciprocalExtend q g a (g - i) := by
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    simp
  · have hgt : ¬ (g + i ≤ g) := by omega
    have hback : g - i ≤ g := Nat.sub_le _ _
    have h1 : g + i - g = i := by omega
    unfold reciprocalExtend
    rw [if_neg hgt, if_pos hback, h1]

noncomputable def numeratorPoly (q g : ℕ) (a : ℕ → ℚ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (2 * g + 1), Polynomial.monomial k (reciprocalExtend q g a k)

theorem numeratorPoly_coeff {q g : ℕ} {a : ℕ → ℚ} {k : ℕ} (hk : k ≤ 2 * g) :
    (numeratorPoly q g a).coeff k = reciprocalExtend q g a k := by
  unfold numeratorPoly
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single k]
  · rw [Polynomial.coeff_monomial, if_pos rfl]
  · intro b _ hb
    rw [Polynomial.coeff_monomial, if_neg hb]
  · intro hknot
    exact absurd (Finset.mem_range.mpr (by omega)) hknot

theorem numeratorPoly_natDegree_le (q g : ℕ) (a : ℕ → ℚ) :
    (numeratorPoly q g a).natDegree ≤ 2 * g := by
  unfold numeratorPoly
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro i hi
  rw [Finset.mem_range] at hi
  calc (Polynomial.monomial i (reciprocalExtend q g a i)).natDegree
      ≤ i := Polynomial.natDegree_monomial_le _
    _ ≤ 2 * g := by omega

theorem theorem1_numerator_determined
    (q g : ℕ) (s t a b : ℕ → ℚ)
    (hs : ∀ k, 1 ≤ k → k ≤ g → s k = t k)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (ha : ∀ n, 1 ≤ n → n ≤ g →
      (∑ i ∈ Finset.range n,
          a i * ((n - i : ℕ) : ℚ) * (q : ℚ) ^ (n - i) * s (n - i)) +
        (n : ℚ) * a n = 0)
    (hb : ∀ n, 1 ≤ n → n ≤ g →
      (∑ i ∈ Finset.range n,
          b i * ((n - i : ℕ) : ℚ) * (q : ℚ) ^ (n - i) * t (n - i)) +
        (n : ℚ) * b n = 0) :
    numeratorPoly q g a = numeratorPoly q g b := by
  have hlow : ∀ j, j ≤ g → a j = b j :=
    theorem1_lower_half (q : ℚ) s t a b g hs ha0 hb0 ha hb
  unfold numeratorPoly
  refine Finset.sum_congr rfl ?_
  intro k _
  congr 1
  unfold reciprocalExtend
  by_cases hk : k ≤ g
  · simp only [if_pos hk]
    exact hlow k hk
  · simp only [if_neg hk]
    rw [hlow (g - (k - g)) (Nat.sub_le _ _)]

end Qatlib.Papers.ZetaCurve04.MainResults.Theorem1
