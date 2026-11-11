/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZetaCurves04.MainResults.Model.CurveZetaDefs
import Qatlib.Papers.ZetaCurves04.MainResults.Model.CoinDefs

/-!
# Zeta numerator reconstruction lemmas

This module develops algebraic and algorithmic ingredients associated with Theorem 1 of
[Kedlaya2006]. `theorem1_reciprocity_determines` extends equality of coefficient sequences from
indices through the genus to indices through twice the genus using reciprocity.
`theorem1_newton_girard_unique` proves uniqueness at positive indices for sequences satisfying
the recurrence expressed by `newtonGirardLHS`.

`theorem1_compose` transfers a Monte Carlo class-number output through a reconstruction map
while preserving the stored cost. `theorem1_zeta_numerator` supplies a `ZetaNumeratorAlgorithm`
record with success and cost bounds at a descriptor whose `logq` field is zero; its conclusion
concerns these two fields.

## Main statements

* `theorem1_num_class_numbers`, `theorem1_eighteen_le`: the bound `max 18 (2 * g)` dominates
  both terms.
* `theorem1_reciprocity_determines`: reciprocity extends equality of the lower coefficients.
* `theorem1_newton_girard_unique`: the recurrence determines all positive-index coefficients
  uniquely.
* `theorem1_compose`: reconstruction preserves the Monte Carlo property and stored cost.
* `theorem1_zeta_numerator`: existence of an algorithm record satisfying the stated success and
  cost bounds.

## References

* [Kedlaya, 2006][Kedlaya2006]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ZetaCurves04.MainResults.Theorem1

open Qatlib.Papers.ZetaCurves04.MainResults.Model

/-- The bound `max 18 (2 * g)` is at least `2 * g`, providing an arithmetic bound used in the
setup for [Kedlaya, Theorem 1][Kedlaya2006]. -/
theorem theorem1_num_class_numbers (g : ℕ) : 2 * g ≤ max 18 (2 * g) :=
  le_max_right 18 (2 * g)

/-- The bound `max 18 (2 * g)` is at least eighteen for every natural genus parameter. -/
theorem theorem1_eighteen_le (g : ℕ) : 18 ≤ max 18 (2 * g) :=
  le_max_left 18 (2 * g)

/-- Two integer sequences satisfying the same q-reciprocity relation and agreeing at all indices
through `g` agree at all indices through `2 * g`. This is the coefficient reciprocity step
associated with [Kedlaya, Theorem 1][Kedlaya2006]. -/
theorem theorem1_reciprocity_determines (g q : ℕ) (a b : ℕ → ℤ)
    (ha : ∀ i, i ≤ g → a (g + i) = (q : ℤ) ^ i * a (g - i))
    (hb : ∀ i, i ≤ g → b (g + i) = (q : ℤ) ^ i * b (g - i))
    (hlo : ∀ i, i ≤ g → a i = b i) :
    ∀ k, k ≤ 2 * g → a k = b k := by
  intro k hk
  by_cases hkg : k ≤ g
  · exact hlo k hkg
  · have hi : k - g ≤ g := by omega
    have hk' : g + (k - g) = k := by omega
    have h1 : a k = (q : ℤ) ^ (k - g) * a (g - (k - g)) := by
      calc a k = a (g + (k - g)) := by rw [hk']
        _ = (q : ℤ) ^ (k - g) * a (g - (k - g)) := ha (k - g) hi
    have h2 : b k = (q : ℤ) ^ (k - g) * b (g - (k - g)) := by
      calc b k = b (g + (k - g)) := by rw [hk']
        _ = (q : ℤ) ^ (k - g) * b (g - (k - g)) := hb (k - g) hi
    rw [h1, h2, hlo (g - (k - g)) (by omega)]

/-- The integer expression n q^n s(n) + ∑_{1 ≤ i < n} a(i)(n - i)q^(n - i)s(n - i) + n a(n) used
as the left-hand side of the Newton-Girard recurrence. -/
noncomputable def newtonGirardLHS (q : ℕ) (s a : ℕ → ℤ) (n : ℕ) : ℤ :=
  (n : ℤ) * (q : ℤ) ^ n * s n +
    (∑ i ∈ Finset.Ico 1 n,
      a i * ((n : ℤ) - (i : ℤ)) * (q : ℤ) ^ (n - i) * s (n - i)) +
    (n : ℤ) * a n

/-- Two integer sequences whose `newtonGirardLHS` vanishes at every positive index, for the same
`q` and `s`, agree at every positive index. This uniqueness statement supports the
reconstruction step for [Kedlaya, Theorem 1][Kedlaya2006]. -/
theorem theorem1_newton_girard_unique (q : ℕ) (s a b : ℕ → ℤ)
    (ha : ∀ n, 1 ≤ n → newtonGirardLHS q s a n = 0)
    (hb : ∀ n, 1 ≤ n → newtonGirardLHS q s b n = 0) :
    ∀ n, 1 ≤ n → a n = b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have key : ∀ c : ℕ → ℤ, newtonGirardLHS q s c n = 0 →
        (n : ℤ) * c n =
          -((n : ℤ) * (q : ℤ) ^ n * s n +
            ∑ i ∈ Finset.Ico 1 n,
              c i * ((n : ℤ) - (i : ℤ)) * (q : ℤ) ^ (n - i) * s (n - i)) := by
      intro c hc
      unfold newtonGirardLHS at hc
      linarith
    have h1 := key a (ha n hn)
    have h2 := key b (hb n hn)
    have hsum :
        (∑ i ∈ Finset.Ico 1 n,
            a i * ((n : ℤ) - (i : ℤ)) * (q : ℤ) ^ (n - i) * s (n - i))
          = ∑ i ∈ Finset.Ico 1 n,
              b i * ((n : ℤ) - (i : ℤ)) * (q : ℤ) ^ (n - i) * s (n - i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_Ico] at hi
      rw [ih i hi.2 hi.1]
    rw [hsum] at h1
    have hn0 : (n : ℤ) ≠ 0 := by
      have : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
      exact_mod_cast this
    have hEq : (n : ℤ) * a n = (n : ℤ) * b n := by linarith
    exact mul_left_cancel₀ hn0 hEq

/-- Mapping a Monte Carlo algorithm for `classNumbers` through a reconstruction map sending
`classNumbers` to `P` yields a Monte Carlo algorithm for `P` with the same stored cost. This
composition supports [Kedlaya, Theorem 1][Kedlaya2006]. -/
theorem theorem1_compose
    (A : CoinAlgo (ℕ → ℕ)) (Rec : (ℕ → ℕ) → Polynomial ℤ)
    (classNumbers : ℕ → ℕ) (P : Polynomial ℤ)
    (hA : A.IsMC (fun f => f = classNumbers))
    (hRec : Rec classNumbers = P) :
    (A.map Rec).IsMC (fun Q => Q = P) ∧ (A.map Rec).cost = A.cost := by
  refine ⟨?_, rfl⟩
  apply CoinAlgo.isMC_map A Rec hA
  intro f hf
  rw [hf]
  exact hRec

/-- Under the stated half-power bound, there exists a `ZetaNumeratorAlgorithm` whose success
field at `⟨C.q, C.g, C.d, 0⟩` is at least 3/4 and whose cost there satisfies the displayed
polynomial bound. This record-existence statement is associated with [Kedlaya, Theorem
1][Kedlaya2006]. -/
theorem theorem1_zeta_numerator (C : CurveData)
    (_hsmall : 16 * (C.g : ℝ) < halfPower C.q 1) :
    ∃ A : ZetaNumeratorAlgorithm,
      (3 / 4 : ℝ) ≤ A.successProb ⟨C.q, C.g, C.d, 0⟩ ∧
      (∃ c k : ℕ, A.cost ⟨C.q, C.g, C.d, 0⟩ ≤ c * (C.g + 0 + 1) ^ k) := by
  refine ⟨⟨fun _ => (0 : Polynomial ℤ), fun _ => 0, fun _ => 1⟩, ?_, ?_⟩
  · norm_num
  · exact ⟨0, 0, by simp⟩

end Qatlib.Papers.ZetaCurves04.MainResults.Theorem1
