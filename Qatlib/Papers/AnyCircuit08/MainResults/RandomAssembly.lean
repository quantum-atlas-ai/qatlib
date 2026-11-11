/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
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
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Finite Markov bounds for bad circuits

Finite forms of Markov's inequality bound the fraction of samples where a nonnegative quantity
exceeds a threshold. Specializations control large fourth-moment quantities and convert bounds
for each bad row into a bound on the fraction of circuits with many bad rows
[HallgrenHarrow2008].

## Main statements

* `finite_markov_fraction`: bounds a threshold-event fraction by the mean divided by the
  threshold.
* `markov_qt_bad_fraction`: specializes the estimate to a fourth-moment scale.
* `bad_circuit_fraction`: bounds the fraction of samples with a large bad-row fraction.

## References

* [Hallgren and Harrow, 2008][HallgrenHarrow2008]
-/

namespace Qatlib.Papers.AnyCircuit08.MainResults

set_option autoImplicit false

open scoped BigOperators

/-- For a nonnegative function on a finite type and positive threshold `t`, the number of values
at least `t` is at most the sum of all values divided by `t` [HallgrenHarrow2008]. -/
theorem finite_markov_indicator {Ω : Type*} [Fintype Ω] (X : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω)
    {t : ℝ} (ht : 0 < t) :
    (∑ ω, if t ≤ X ω then (1:ℝ) else 0) ≤ (∑ ω, X ω) / t := by
  have h1 : t * (∑ ω, if t ≤ X ω then (1:ℝ) else 0) ≤ ∑ ω, X ω := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ω _
    by_cases h : t ≤ X ω
    · simp [h]
    · simp [h]
      exact hX ω
  rw [le_div_iff₀ ht, mul_comm]
  exact h1

/-- On a nonempty finite type, the fraction of values of a nonnegative function at least
positive `t` is at most its uniform mean divided by `t` [HallgrenHarrow2008]. -/
theorem finite_markov_fraction {Ω : Type*} [Fintype Ω] (X : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω)
    {t : ℝ} (ht : 0 < t) (hΩ : 0 < Fintype.card Ω) :
    (∑ ω, if t ≤ X ω then (1:ℝ) else 0) / (Fintype.card Ω : ℝ)
      ≤ (∑ ω, X ω) / ((Fintype.card Ω : ℝ) * t) := by
  have h := finite_markov_indicator X hX ht
  have hc : (0:ℝ) < (Fintype.card Ω : ℝ) := by exact_mod_cast hΩ
  calc (∑ ω, if t ≤ X ω then (1:ℝ) else 0) / (Fintype.card Ω : ℝ)
      ≤ ((∑ ω, X ω) / t) / (Fintype.card Ω : ℝ) := div_le_div_of_nonneg_right h hc.le
    _ = (∑ ω, X ω) / ((Fintype.card Ω : ℝ) * t) := by
        field_simp

/-- If a nonnegative quantity has uniform mean at most `2 * 2 ^ (-n)` and `β ≠ 0`, the fraction
of samples where it is at least `2 ^ (-n) / β ^ 2` is at most `2 * β ^ 2`
[HallgrenHarrow2008]. -/
theorem markov_qt_bad_fraction {Ω : Type*} [Fintype Ω] (Q : Ω → ℝ) (hQ : ∀ ω, 0 ≤ Q ω)
    {n : ℕ} {β : ℝ} (hβ : β ≠ 0) (hΩ : 0 < Fintype.card Ω)
    (hmean : (∑ ω, Q ω) / (Fintype.card Ω : ℝ) ≤ 2 * (2:ℝ) ^ (-(n:ℝ))) :
    (∑ ω, if (2:ℝ) ^ (-(n:ℝ)) / β ^ 2 ≤ Q ω then (1:ℝ) else 0)
        / (Fintype.card Ω : ℝ) ≤ 2 * β ^ 2 := by
  have h2n : (0:ℝ) < (2:ℝ) ^ (-(n:ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hβ2 : (0:ℝ) < β ^ 2 := by positivity
  have ht : (0:ℝ) < (2:ℝ) ^ (-(n:ℝ)) / β ^ 2 := div_pos h2n hβ2
  have hmark := finite_markov_fraction Q hQ ht hΩ
  have hc : (0:ℝ) < (Fintype.card Ω : ℝ) := by exact_mod_cast hΩ
  have hmono : (∑ ω, Q ω) / ((Fintype.card Ω : ℝ) * ((2:ℝ) ^ (-(n:ℝ)) / β ^ 2))
      = (∑ ω, Q ω) / (Fintype.card Ω : ℝ) / ((2:ℝ) ^ (-(n:ℝ)) / β ^ 2) := by
    field_simp
  have hstep : (∑ ω, Q ω) / (Fintype.card Ω : ℝ) / ((2:ℝ) ^ (-(n:ℝ)) / β ^ 2)
      ≤ 2 * β ^ 2 := by
    have h1 : (∑ ω, Q ω) / (Fintype.card Ω : ℝ) / ((2:ℝ) ^ (-(n:ℝ)) / β ^ 2)
        ≤ (2 * (2:ℝ) ^ (-(n:ℝ))) / ((2:ℝ) ^ (-(n:ℝ)) / β ^ 2) :=
      div_le_div_of_nonneg_right hmean ht.le
    have h2 : (2 * (2:ℝ) ^ (-(n:ℝ))) / ((2:ℝ) ^ (-(n:ℝ)) / β ^ 2) = 2 * β ^ 2 := by
      field_simp
    rwa [h2] at h1
  calc (∑ ω, if (2:ℝ) ^ (-(n:ℝ)) / β ^ 2 ≤ Q ω then (1:ℝ) else 0)
        / (Fintype.card Ω : ℝ)
      ≤ (∑ ω, Q ω) / ((Fintype.card Ω : ℝ) * ((2:ℝ) ^ (-(n:ℝ)) / β ^ 2)) := hmark
    _ = (∑ ω, Q ω) / (Fintype.card Ω : ℝ) / ((2:ℝ) ^ (-(n:ℝ)) / β ^ 2) := hmono
    _ ≤ 2 * β ^ 2 := hstep

/-- If each row is marked bad on at most a fraction `p` of samples, then the fraction of samples
with at least a positive fraction `s` of bad rows is at most `p / s` [HallgrenHarrow2008]. -/
theorem bad_circuit_fraction {Ω A : Type*} [Fintype Ω] [Fintype A]
    (bad : Ω → A → Bool) {p s : ℝ}
    (hp : ∀ a, (∑ ω, if bad ω a then (1:ℝ) else 0) / (Fintype.card Ω : ℝ) ≤ p)
    (hs : 0 < s) (hA : 0 < Fintype.card A) (hΩ : 0 < Fintype.card Ω) :
    (∑ ω, if s ≤ (∑ a, if bad ω a then (1:ℝ) else 0) / (Fintype.card A : ℝ)
        then (1:ℝ) else 0) / (Fintype.card Ω : ℝ) ≤ p / s := by
  set B : Ω → A → ℝ := fun ω a => if bad ω a then (1:ℝ) else 0 with hB
  have hB0 : ∀ ω a, 0 ≤ B ω a := by
    intro ω a
    simp only [hB]
    split_ifs <;> norm_num
  have hB01 : ∀ ω a, B ω a ≤ 1 := by
    intro ω a
    simp only [hB]
    split_ifs <;> norm_num
  have hcardA : (0:ℝ) < (Fintype.card A : ℝ) := by exact_mod_cast hA
  have hcardΩ : (0:ℝ) < (Fintype.card Ω : ℝ) := by exact_mod_cast hΩ

  have hcol : ∀ a, (∑ ω, B ω a) ≤ p * (Fintype.card Ω : ℝ) := by
    intro a
    have h := hp a
    rw [div_le_iff₀ hcardΩ] at h
    simpa [hB] using h
  have hswap : (∑ ω, ∑ a, B ω a) = ∑ a, ∑ ω, B ω a := Finset.sum_comm
  have hup : (∑ ω, ∑ a, B ω a) ≤ (Fintype.card A : ℝ) * (p * (Fintype.card Ω : ℝ)) := by
    rw [hswap]
    calc ∑ a, ∑ ω, B ω a ≤ ∑ _a : A, p * (Fintype.card Ω : ℝ) :=
          Finset.sum_le_sum (fun a _ => hcol a)
      _ = (Fintype.card A : ℝ) * (p * (Fintype.card Ω : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

  have hlow : (∑ ω, if s ≤ (∑ a, B ω a) / (Fintype.card A : ℝ) then (1:ℝ) else 0)
        * (s * (Fintype.card A : ℝ)) ≤ ∑ ω, ∑ a, B ω a := by
    rw [Finset.sum_mul]
    calc ∑ ω, (if s ≤ (∑ a, B ω a) / (Fintype.card A : ℝ) then (1:ℝ) else 0)
            * (s * (Fintype.card A : ℝ))
        = ∑ ω, if s ≤ (∑ a, B ω a) / (Fintype.card A : ℝ)
            then s * (Fintype.card A : ℝ) else 0 := by
          apply Finset.sum_congr rfl
          intro ω _
          by_cases h : s ≤ (∑ a, B ω a) / (Fintype.card A : ℝ) <;> simp [h]
      _ ≤ ∑ ω, ∑ a, B ω a := by
          apply Finset.sum_le_sum
          intro ω _
          by_cases h : s ≤ (∑ a, B ω a) / (Fintype.card A : ℝ)
          · simp only [h, if_true]
            have hmul : s * (Fintype.card A : ℝ) ≤ ∑ a, B ω a := by
              have hh := mul_le_mul_of_nonneg_right h hcardA.le
              rwa [div_mul_cancel₀ _ (ne_of_gt hcardA)] at hh
            linarith
          · simp only [h, if_false]
            exact Finset.sum_nonneg (fun a _ => hB0 ω a)
  have hkey : (∑ ω, if s ≤ (∑ a, B ω a) / (Fintype.card A : ℝ) then (1:ℝ) else 0)
        * (s * (Fintype.card A : ℝ)) ≤ (Fintype.card A : ℝ) * (p * (Fintype.card Ω : ℝ)) :=
    le_trans hlow hup
  have hsA : (0:ℝ) < s * (Fintype.card A : ℝ) := mul_pos hs hcardA
  have hbound : (∑ ω, if s ≤ (∑ a, B ω a) / (Fintype.card A : ℝ) then (1:ℝ) else 0)
      ≤ (p / s) * (Fintype.card Ω : ℝ) := by
    have h1 : (∑ ω, if s ≤ (∑ a, B ω a) / (Fintype.card A : ℝ) then (1:ℝ) else 0)
        ≤ ((Fintype.card A : ℝ) * (p * (Fintype.card Ω : ℝ))) / (s * (Fintype.card A : ℝ)) :=
      (le_div_iff₀ hsA).mpr hkey
    have h2 : ((Fintype.card A : ℝ) * (p * (Fintype.card Ω : ℝ)))
        / (s * (Fintype.card A : ℝ)) = (p / s) * (Fintype.card Ω : ℝ) := by
      field_simp
    rwa [h2] at h1
  rw [div_le_iff₀ hcardΩ]
  exact hbound

end Qatlib.Papers.AnyCircuit08.MainResults
