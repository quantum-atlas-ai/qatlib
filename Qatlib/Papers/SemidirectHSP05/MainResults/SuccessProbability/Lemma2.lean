/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
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
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Order.RelClasses
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Pretty good measurement success bounds

This module defines `pgmSuccess` from matrix sum multiplicities and proves the success
probability inequalities of Lemma 2 of [BaconChildsVanDam2005]. A specialization gives a lower
bound of one sixteenth when at least one quarter of the relevant instances have one or two
solutions.

## Main statements

* `lemma2_success_bounds`: A lower-tail hypothesis on multiplicities yields lower and upper
  bounds for pgmSuccess.
* `success_ge_sixteenth`: One-or-two solution concentration gives success at least 1/16.

## References

* [Bacon et al., 2005][BaconChildsVanDam2005]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemidirectHSP05.MainResults.SuccessProbability

open scoped Classical BigOperators

variable {A : Type*} [Fintype A] [Nonempty A]

/-- The real square root of a natural number is at most that number [BaconChildsVanDam2005]. -/
lemma sqrt_natCast_le (n : ℕ) : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
  rcases n with _ | n
  · simp
  · have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hle : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
    calc Real.sqrt ((n + 1 : ℕ) : ℝ)
        ≤ Real.sqrt (((n + 1 : ℕ) : ℝ) ^ 2) := Real.sqrt_le_sqrt hle
      _ = ((n + 1 : ℕ) : ℝ) := Real.sqrt_sq (by positivity)

/-- The normalized sum of squared sums of square roots of multiplicities, giving the pretty good
measurement success expression for parameters `p` and `k`. -/
def pgmSuccess (p k : ℕ) (η : (Fin k → A) → A → ℕ) : ℝ :=
  (1 / ((Fintype.card A : ℝ) ^ (k + 1) * (p : ℝ) ^ k)) *
    ∑ x : Fin k → A, (∑ w : A, Real.sqrt (η x w)) ^ 2

/-- If each multiplicity row sums to `p ^ k` and a fraction at least `β` of entries are at least
`α`, then `pgmSuccess` lies between `α * β ^ 2 * |A| / p ^ k` and `p ^ k / |A|`. This is
Lemma 2 of [BaconChildsVanDam2005]. -/
theorem lemma2_success_bounds (p k : ℕ) (hp : 0 < p)
    (η : (Fin k → A) → A → ℕ)
    (hcount : ∀ x : Fin k → A, ∑ w : A, η x w = p ^ k)
    (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hprob : β * ((Fintype.card A : ℝ) ^ k * (Fintype.card A : ℝ)) ≤
      ∑ x : Fin k → A, ∑ w : A, if α ≤ (η x w : ℝ) then (1 : ℝ) else 0) :
    α * β ^ 2 * (Fintype.card A : ℝ) / (p : ℝ) ^ k ≤ pgmSuccess p k η ∧
      pgmSuccess p k η ≤ (p : ℝ) ^ k / (Fintype.card A : ℝ) := by
  have hNpos : (0 : ℝ) < (Fintype.card A : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hPpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hcard : (Fintype.card (Fin k → A) : ℝ) = (Fintype.card A : ℝ) ^ k := by
    rw [Fintype.card_fun, Fintype.card_fin]
    push_cast
    ring
  have hfactor_nonneg :
      0 ≤ (1 / ((Fintype.card A : ℝ) ^ (k + 1) * (p : ℝ) ^ k)) := by positivity
  have hnpow_pos : (0 : ℝ) < (Fintype.card A : ℝ) ^ k := pow_pos hNpos k

  have hterm : ∀ x : Fin k → A, (∑ w : A, Real.sqrt (η x w)) ≤ (p : ℝ) ^ k := by
    intro x
    calc (∑ w : A, Real.sqrt (η x w))
        ≤ ∑ w : A, (η x w : ℝ) :=
          Finset.sum_le_sum (fun w _ => sqrt_natCast_le (η x w))
      _ = ((∑ w : A, η x w : ℕ) : ℝ) := by simp only [Nat.cast_sum]
      _ = ((p ^ k : ℕ) : ℝ) := by rw [hcount x]
      _ = (p : ℝ) ^ k := by push_cast; ring

  have hsum_bound :
      (∑ x : Fin k → A, (∑ w : A, Real.sqrt (η x w)) ^ 2)
        ≤ (Fintype.card A : ℝ) ^ k * ((p : ℝ) ^ k) ^ 2 := by
    have hsqterm : ∀ x : Fin k → A,
        (∑ w : A, Real.sqrt (η x w)) ^ 2 ≤ ((p : ℝ) ^ k) ^ 2 := by
      intro x
      exact pow_le_pow_left₀
        (Finset.sum_nonneg (fun w _ => Real.sqrt_nonneg _)) (hterm x) 2
    calc (∑ x : Fin k → A, (∑ w : A, Real.sqrt (η x w)) ^ 2)
        ≤ ∑ _x : Fin k → A, ((p : ℝ) ^ k) ^ 2 :=
          Finset.sum_le_sum (fun x _ => hsqterm x)
      _ = (Fintype.card (Fin k → A) : ℝ) * ((p : ℝ) ^ k) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = (Fintype.card A : ℝ) ^ k * ((p : ℝ) ^ k) ^ 2 := by rw [hcard]

  have harith_upper :
      (1 / ((Fintype.card A : ℝ) ^ (k + 1) * (p : ℝ) ^ k)) *
        ((Fintype.card A : ℝ) ^ k * ((p : ℝ) ^ k) ^ 2)
        = (p : ℝ) ^ k / (Fintype.card A : ℝ) := by
    have hn : (Fintype.card A : ℝ) ≠ 0 := ne_of_gt hNpos
    have hP : (p : ℝ) ≠ 0 := ne_of_gt hPpos
    have hnk : (Fintype.card A : ℝ) ^ k ≠ 0 := pow_ne_zero k hn
    field_simp
    ring
  constructor
  · have hsqrtα_nonneg : 0 ≤ Real.sqrt α := Real.sqrt_nonneg α
    have hpoint : ∀ x : Fin k → A, ∀ w : A,
        Real.sqrt α * (if α ≤ (η x w : ℝ) then (1 : ℝ) else 0) ≤ Real.sqrt (η x w) := by
      intro x w
      by_cases h : α ≤ (η x w : ℝ)
      · rw [if_pos h, mul_one]
        exact Real.sqrt_le_sqrt h
      · rw [if_neg h, mul_zero]
        exact Real.sqrt_nonneg _
    have hsum_le : Real.sqrt α * (∑ x : Fin k → A, ∑ w : A,
          if α ≤ (η x w : ℝ) then (1 : ℝ) else 0)
        ≤ ∑ x : Fin k → A, ∑ w : A, Real.sqrt (η x w) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun x _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun w _ => hpoint x w)
    have hS_lower :
        Real.sqrt α * (β * ((Fintype.card A : ℝ) ^ k * (Fintype.card A : ℝ)))
          ≤ ∑ x : Fin k → A, ∑ w : A, Real.sqrt (η x w) := by
      calc Real.sqrt α * (β * ((Fintype.card A : ℝ) ^ k * (Fintype.card A : ℝ)))
          ≤ Real.sqrt α * (∑ x : Fin k → A, ∑ w : A,
              if α ≤ (η x w : ℝ) then (1 : ℝ) else 0) :=
            mul_le_mul_of_nonneg_left hprob hsqrtα_nonneg
        _ ≤ ∑ x : Fin k → A, ∑ w : A, Real.sqrt (η x w) := hsum_le
    have hcauchy :
        (∑ x : Fin k → A, ∑ w : A, Real.sqrt (η x w)) ^ 2
          ≤ (Fintype.card A : ℝ) ^ k *
              (∑ x : Fin k → A, (∑ w : A, Real.sqrt (η x w)) ^ 2) := by
      have h := sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin k → A)))
        (f := fun x => ∑ w : A, Real.sqrt (η x w))
      simpa [hcard] using h
    have hQ_lower :
        (∑ x : Fin k → A, ∑ w : A, Real.sqrt (η x w)) ^ 2 / (Fintype.card A : ℝ) ^ k
          ≤ ∑ x : Fin k → A, (∑ w : A, Real.sqrt (η x w)) ^ 2 := by
      rw [div_le_iff₀ hnpow_pos]
      calc (∑ x : Fin k → A, ∑ w : A, Real.sqrt (η x w)) ^ 2
          ≤ (Fintype.card A : ℝ) ^ k *
              (∑ x : Fin k → A, (∑ w : A, Real.sqrt (η x w)) ^ 2) := hcauchy
        _ = (∑ x : Fin k → A, (∑ w : A, Real.sqrt (η x w)) ^ 2) *
              (Fintype.card A : ℝ) ^ k := by ring
    have hS_nonneg :
        0 ≤ Real.sqrt α * (β * ((Fintype.card A : ℝ) ^ k * (Fintype.card A : ℝ))) := by
      refine mul_nonneg (Real.sqrt_nonneg α) (mul_nonneg hβ ?_)
      positivity
    have hSsq :
        (Real.sqrt α * (β * ((Fintype.card A : ℝ) ^ k * (Fintype.card A : ℝ)))) ^ 2
          ≤ (∑ x : Fin k → A, ∑ w : A, Real.sqrt (η x w)) ^ 2 :=
      pow_le_pow_left₀ hS_nonneg hS_lower 2
    have hQbig :
        (Real.sqrt α * (β * ((Fintype.card A : ℝ) ^ k * (Fintype.card A : ℝ)))) ^ 2 /
            (Fintype.card A : ℝ) ^ k
          ≤ ∑ x : Fin k → A, (∑ w : A, Real.sqrt (η x w)) ^ 2 :=
      le_trans (div_le_div_of_nonneg_right hSsq (le_of_lt hnpow_pos)) hQ_lower
    have hstep :
        (1 / ((Fintype.card A : ℝ) ^ (k + 1) * (p : ℝ) ^ k)) *
            ((Real.sqrt α * (β * ((Fintype.card A : ℝ) ^ k * (Fintype.card A : ℝ)))) ^ 2 /
              (Fintype.card A : ℝ) ^ k)
          ≤ pgmSuccess p k η := by
      calc (1 / ((Fintype.card A : ℝ) ^ (k + 1) * (p : ℝ) ^ k)) *
              ((Real.sqrt α * (β * ((Fintype.card A : ℝ) ^ k * (Fintype.card A : ℝ)))) ^ 2 /
                (Fintype.card A : ℝ) ^ k)
          ≤ (1 / ((Fintype.card A : ℝ) ^ (k + 1) * (p : ℝ) ^ k)) *
              (∑ x : Fin k → A, (∑ w : A, Real.sqrt (η x w)) ^ 2) :=
            mul_le_mul_of_nonneg_left hQbig hfactor_nonneg
        _ = pgmSuccess p k η := rfl
    have harith_lower :
        α * β ^ 2 * (Fintype.card A : ℝ) / (p : ℝ) ^ k
          = (1 / ((Fintype.card A : ℝ) ^ (k + 1) * (p : ℝ) ^ k)) *
              ((Real.sqrt α *
                (β * ((Fintype.card A : ℝ) ^ k * (Fintype.card A : ℝ)))) ^ 2 /
                (Fintype.card A : ℝ) ^ k) := by
      have hn : (Fintype.card A : ℝ) ≠ 0 := ne_of_gt hNpos
      have hP : (p : ℝ) ≠ 0 := ne_of_gt hPpos
      have hnk : (Fintype.card A : ℝ) ^ k ≠ 0 := pow_ne_zero k hn
      have hs : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα
      field_simp
      rw [hs]
      ring
    calc α * β ^ 2 * (Fintype.card A : ℝ) / (p : ℝ) ^ k
        = (1 / ((Fintype.card A : ℝ) ^ (k + 1) * (p : ℝ) ^ k)) *
            ((Real.sqrt α *
              (β * ((Fintype.card A : ℝ) ^ k * (Fintype.card A : ℝ)))) ^ 2 /
              (Fintype.card A : ℝ) ^ k) := harith_lower
      _ ≤ pgmSuccess p k η := hstep
  · calc pgmSuccess p k η
        = (1 / ((Fintype.card A : ℝ) ^ (k + 1) * (p : ℝ) ^ k)) *
            (∑ x : Fin k → A, (∑ w : A, Real.sqrt (η x w)) ^ 2) := rfl
      _ ≤ (1 / ((Fintype.card A : ℝ) ^ (k + 1) * (p : ℝ) ^ k)) *
            ((Fintype.card A : ℝ) ^ k * ((p : ℝ) ^ k) ^ 2) :=
          mul_le_mul_of_nonneg_left hsum_bound hfactor_nonneg
      _ = (p : ℝ) ^ k / (Fintype.card A : ℝ) := harith_upper

/-- For multiplicities over r-dimensional vectors in `ZMod p`, the stated row sums and a
one-quarter fraction of one-or-two entries imply `pgmSuccess ≥ 1/16`
[BaconChildsVanDam2005]. -/
theorem success_ge_sixteenth (p r : ℕ) (hp : p.Prime) [NeZero p]
    (η : (Fin r → (Fin r → ZMod p)) → (Fin r → ZMod p) → ℕ)
    (hcount : ∀ x : Fin r → (Fin r → ZMod p), ∑ w, η x w = p ^ r)
    (hmany : (1 / 4 : ℝ) * ((Fintype.card (Fin r → ZMod p) : ℝ) ^ r *
        (Fintype.card (Fin r → ZMod p) : ℝ)) ≤
      ∑ x : Fin r → (Fin r → ZMod p), ∑ w : Fin r → ZMod p,
        if (η x w = 1 ∨ η x w = 2) then (1 : ℝ) else 0) :
    (1 / 16 : ℝ) ≤ pgmSuccess p r η := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hcard : (Fintype.card (Fin r → ZMod p) : ℝ) = (p : ℝ) ^ r := by
    rw [Fintype.card_pi_const, ZMod.card]
    push_cast
    ring

  have key : ∀ n : ℕ,
      (if (n = 1 ∨ n = 2) then (1 : ℝ) else 0)
        ≤ (if (1 : ℝ) ≤ (n : ℝ) then (1 : ℝ) else 0) := by
    intro n
    by_cases h : n = 1 ∨ n = 2
    · rw [if_pos h]
      rw [if_pos (by rcases h with h | h <;> (rw [h]; norm_num))]
    · rw [if_neg h]
      split <;> norm_num
  have hmono :
      (∑ x : Fin r → (Fin r → ZMod p), ∑ w : Fin r → ZMod p,
        if (η x w = 1 ∨ η x w = 2) then (1 : ℝ) else 0)
      ≤ (∑ x : Fin r → (Fin r → ZMod p), ∑ w : Fin r → ZMod p,
        if (1 : ℝ) ≤ (η x w : ℝ) then (1 : ℝ) else 0) := by
    apply Finset.sum_le_sum
    intro x _
    apply Finset.sum_le_sum
    intro w _
    exact key (η x w)
  have hprob :
      (1 / 4 : ℝ) * ((Fintype.card (Fin r → ZMod p) : ℝ) ^ r *
        (Fintype.card (Fin r → ZMod p) : ℝ)) ≤
      ∑ x : Fin r → (Fin r → ZMod p), ∑ w : Fin r → ZMod p,
        if (1 : ℝ) ≤ (η x w : ℝ) then (1 : ℝ) else 0 := le_trans hmany hmono
  have h := lemma2_success_bounds (A := Fin r → ZMod p) p r hp.pos η hcount (1 : ℝ) (1 / 4)
    (by norm_num) (by norm_num) hprob
  obtain ⟨hlo, _⟩ := h
  have harith : (1 : ℝ) * (1 / 4 : ℝ) ^ 2 * (Fintype.card (Fin r → ZMod p) : ℝ) /
      (p : ℝ) ^ r = 1 / 16 := by
    rw [hcard]
    have hpne : (p : ℝ) ^ r ≠ 0 := pow_ne_zero _ (ne_of_gt hp0)
    field_simp
    ring
  linarith [hlo, harith]

end Qatlib.Papers.SemidirectHSP05.MainResults.SuccessProbability
