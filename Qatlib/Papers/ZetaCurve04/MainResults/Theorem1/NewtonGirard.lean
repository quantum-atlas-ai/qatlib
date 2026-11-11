/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZetaCurve04.MainResults.Defs

/-!
# Newton relations for numerator coefficients

The rational recurrence `NewtonRelation` determines a coefficient sequence uniquely, and finite
versions exist to any prescribed degree. Agreement of the input power sums forces agreement of
the resulting coefficients, including the scaled recurrence used for the lower half of a zeta
numerator.

This development forms part of the formalization of [Kedlaya2006].

## Main statements

* `newtonRelation_unique`: Two coefficient sequences satisfying the same Newton relation are
  equal.
* `theorem1_lower_half`: Equal input sequences through degree `g` determine equal lower-half
  coefficients under the stated normalized, scaled Newton recurrences.

## References

* [Kedlaya, 2006][Kedlaya2006]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ZetaCurve04.MainResults.Theorem1

/-- The rational sequence `a` starts at one and satisfies `sum (a i * p (n - i)) + n * a n = 0`
for every positive `n`, with the sum over `i < n`. -/
def NewtonRelation (p a : ℕ → ℚ) : Prop :=
  a 0 = 1 ∧ ∀ n : ℕ, 1 ≤ n →
    (∑ i ∈ Finset.range n, a i * p (n - i)) + (n : ℚ) * a n = 0

/-- Two coefficient sequences satisfying the same Newton relation are equal. -/
theorem newtonRelation_unique {p a b : ℕ → ℚ}
    (ha : NewtonRelation p a) (hb : NewtonRelation p b) : a = b := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      exact ha.1.trans hb.1.symm
    · have ha' := ha.2 n hn
      have hb' := hb.2 n hn
      have hsum :
          (∑ i ∈ Finset.range n, a i * p (n - i)) =
            ∑ i ∈ Finset.range n, b i * p (n - i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [ih i (Finset.mem_range.mp hi)]
      have hkey : (n : ℚ) * a n = (n : ℚ) * b n := by
        rw [hsum] at ha'
        linarith
      have hn0 : (n : ℚ) ≠ 0 := by
        have hpos : (0 : ℚ) < n := by exact_mod_cast hn
        exact ne_of_gt hpos
      exact mul_left_cancel₀ hn0 hkey

/-- For any rational input sequence and cutoff `N`, there exists a coefficient sequence starting
at one and satisfying the Newton recurrence through degree `N`. -/
theorem newtonRelation_exists_finite (p : ℕ → ℚ) :
    ∀ N : ℕ, ∃ a : ℕ → ℚ, a 0 = 1 ∧
      ∀ n : ℕ, 1 ≤ n → n ≤ N →
        (∑ i ∈ Finset.range n, a i * p (n - i)) + (n : ℚ) * a n = 0 := by
  intro N
  induction N with
  | zero =>
      refine ⟨fun k => if k = 0 then 1 else 0, by simp, ?_⟩
      intro n hn hn0
      omega
  | succ N ih =>
      obtain ⟨a, h0, hrel⟩ := ih
      set c : ℚ := -((N + 1 : ℚ))⁻¹ *
        ∑ i ∈ Finset.range (N + 1), a i * p (N + 1 - i) with hc
      refine ⟨Function.update a (N + 1) c, ?_, ?_⟩
      · rw [Function.update_of_ne (by omega : _ ≠ _)]
        exact h0
      · intro n hn hnle
        rcases Nat.lt_or_eq_of_le hnle with hlt | heq
        · have hnN : n ≤ N := by omega
          have hreln := hrel n hn hnN
          have hsum :
              (∑ i ∈ Finset.range n,
                  Function.update a (N + 1) c i * p (n - i))
                = ∑ i ∈ Finset.range n, a i * p (n - i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi' : i < n := Finset.mem_range.mp hi
            rw [Function.update_of_ne (by omega : _ ≠ _)]
          have han : Function.update a (N + 1) c n = a n := by
            rw [Function.update_of_ne (by omega : _ ≠ _)]
          rw [hsum, han]
          exact hreln
        · subst heq
          have hsum :
              (∑ i ∈ Finset.range (N + 1),
                  Function.update a (N + 1) c i * p (N + 1 - i))
                = ∑ i ∈ Finset.range (N + 1), a i * p (N + 1 - i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi' : i < N + 1 := Finset.mem_range.mp hi
            rw [Function.update_of_ne (by omega : _ ≠ _)]
          have han : Function.update a (N + 1) c (N + 1) = c :=
            Function.update_self _ _ _
          rw [hsum, han, hc]
          have hN1 : ((N + 1 : ℕ) : ℚ) ≠ 0 := by positivity
          field_simp
          push_cast
          ring

/-- Agreement of two input sequences through positive degree `N` forces agreement of their
normalized Newton-recursive coefficient sequences through degree `N`. -/
theorem newtonRelation_agree {p q a b : ℕ → ℚ} {N : ℕ}
    (hpq : ∀ k, 1 ≤ k → k ≤ N → p k = q k)
    (ha0 : a 0 = 1)
    (harel : ∀ n, 1 ≤ n → n ≤ N →
      (∑ i ∈ Finset.range n, a i * p (n - i)) + (n : ℚ) * a n = 0)
    (hb0 : b 0 = 1)
    (hbrel : ∀ n, 1 ≤ n → n ≤ N →
      (∑ i ∈ Finset.range n, b i * q (n - i)) + (n : ℚ) * b n = 0) :
    ∀ n, n ≤ N → a n = b n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      exact ha0.trans hb0.symm
    · have ha' := harel n hpos hn
      have hb' := hbrel n hpos hn
      have hsum :
          (∑ i ∈ Finset.range n, a i * p (n - i)) =
            ∑ i ∈ Finset.range n, b i * q (n - i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hi' : i < n := Finset.mem_range.mp hi
        have hilt : i ≤ N := by omega
        have hialt : i < n := hi'
        rw [ih i hialt hilt]
        have hni : 1 ≤ n - i := by omega
        have hniN : n - i ≤ N := by omega
        rw [hpq (n - i) hni hniN]
      have hkey : (n : ℚ) * a n = (n : ℚ) * b n := by
        rw [hsum] at ha'
        linarith
      have hn0 : (n : ℚ) ≠ 0 := by
        have hpos' : (0 : ℚ) < n := by exact_mod_cast hpos
        exact ne_of_gt hpos'
      exact mul_left_cancel₀ hn0 hkey

/-- Equal input sequences through degree `N` determine equal coefficients through degree `N`
under the stated Newton recurrences scaled by `k * q ^ k`. See [Kedlaya2006]. -/
theorem theorem1_power_sum_determines
    (q : ℚ) (s t a b : ℕ → ℚ) (N : ℕ)
    (hs : ∀ k, 1 ≤ k → k ≤ N → s k = t k)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (ha : ∀ n, 1 ≤ n → n ≤ N →
      (∑ i ∈ Finset.range n,
          a i * ((n - i : ℕ) : ℚ) * q ^ (n - i) * s (n - i)) +
        (n : ℚ) * a n = 0)
    (hb : ∀ n, 1 ≤ n → n ≤ N →
      (∑ i ∈ Finset.range n,
          b i * ((n - i : ℕ) : ℚ) * q ^ (n - i) * t (n - i)) +
        (n : ℚ) * b n = 0) :
    ∀ n, n ≤ N → a n = b n := by
  refine newtonRelation_agree (p := fun k => (k : ℚ) * q ^ k * s k)
    (q := fun k => (k : ℚ) * q ^ k * t k) ?_ ha0 ?_ hb0 ?_
  · intro k hk1 hkN
    simp only [hs k hk1 hkN]
  · intro n hn1 hnN
    have h := ha n hn1 hnN
    have hsum :
        (∑ i ∈ Finset.range n,
            a i * ((n - i : ℕ) : ℚ) * q ^ (n - i) * s (n - i)) =
          ∑ i ∈ Finset.range n,
            a i * (((n - i : ℕ) : ℚ) * q ^ (n - i) * s (n - i)) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    rw [hsum] at h
    exact h
  · intro n hn1 hnN
    have h := hb n hn1 hnN
    have hsum :
        (∑ i ∈ Finset.range n,
            b i * ((n - i : ℕ) : ℚ) * q ^ (n - i) * t (n - i)) =
          ∑ i ∈ Finset.range n,
            b i * (((n - i : ℕ) : ℚ) * q ^ (n - i) * t (n - i)) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    rw [hsum] at h
    exact h

/-- Equal input sequences through degree `g` determine equal lower-half coefficients under the
stated normalized, scaled Newton recurrences. See [Kedlaya2006]. -/
theorem theorem1_lower_half
    (q : ℚ) (s t a b : ℕ → ℚ) (g : ℕ)
    (hs : ∀ k, 1 ≤ k → k ≤ g → s k = t k)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (ha : ∀ n, 1 ≤ n → n ≤ g →
      (∑ i ∈ Finset.range n,
          a i * ((n - i : ℕ) : ℚ) * q ^ (n - i) * s (n - i)) +
        (n : ℚ) * a n = 0)
    (hb : ∀ n, 1 ≤ n → n ≤ g →
      (∑ i ∈ Finset.range n,
          b i * ((n - i : ℕ) : ℚ) * q ^ (n - i) * t (n - i)) +
        (n : ℚ) * b n = 0) :
    ∀ n, n ≤ g → a n = b n :=
  theorem1_power_sum_determines q s t a b g hs ha0 hb0 ha hb

end Qatlib.Papers.ZetaCurve04.MainResults.Theorem1
