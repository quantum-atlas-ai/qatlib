/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
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
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Subtype
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core

/-!
# Classical success bounds from transcript counts

A deterministic transcript map can correctly identify no more secrets than there are
transcripts. The module converts this counting fact into uniform success bounds and extends the
inverse-power estimate to a finite convex combination of deterministic procedures
[HallgrenHarrow2008].

## Main statements

* `card_correct_le_card_transcripts`: bounds the number of correctly identified secrets.
* `classical_success_le_inv_pow`: derives the bound `1 / 2 ^ k`.
* `randomized_success_le_inv_pow`: extends the bound to weighted random choices.

## References

* [Hallgren and Harrow, 2008][HallgrenHarrow2008]
-/

namespace Qatlib.Papers.AnyCircuit08.MainResults

set_option autoImplicit false

/-- The number of inputs correctly recovered by a transcript map and output map is at most the
number of possible transcripts [HallgrenHarrow2008]. -/
theorem card_correct_le_card_transcripts {A τ : Type*} [Fintype A] [DecidableEq A] [Fintype τ]
    (T : A → τ) (out : τ → A) :
    (Finset.univ.filter (fun a => out (T a) = a)).card ≤ Fintype.card τ := by
  have hinj : Function.Injective (fun a : {a : A // out (T a) = a} => T a) := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    simp only [Subtype.mk_eq_mk]
    have hab' : T a = T b := hab
    calc a = out (T a) := ha.symm
      _ = out (T b) := by rw [hab']
      _ = b := hb
  have h1 := Fintype.card_le_of_injective (fun a : {a : A // out (T a) = a} => T a) hinj
  rwa [Fintype.card_subtype] at h1

/-- If there are at most `2 ^ q` transcripts and the secret space is nonempty, the uniform
success fraction is at most `2 ^ q / card A` [HallgrenHarrow2008]. -/
theorem classical_success_prob_le {A τ : Type*} [Fintype A] [DecidableEq A] [Fintype τ]
    (T : A → τ) (out : τ → A) (q : ℕ) (hq : Fintype.card τ ≤ 2 ^ q)
    (hA : 0 < Fintype.card A) :
    ((Finset.univ.filter (fun a => out (T a) = a)).card : ℝ) / Fintype.card A
      ≤ (2 : ℝ) ^ q / Fintype.card A := by
  have h2 : ((Finset.univ.filter (fun a => out (T a) = a)).card : ℝ) ≤ (2 : ℝ) ^ q := by
    have h3 : (Finset.univ.filter (fun a => out (T a) = a)).card ≤ 2 ^ q :=
      le_trans (card_correct_le_card_transcripts T out) hq
    exact_mod_cast h3
  exact div_le_div_of_nonneg_right h2 (by positivity)

/-- If the secret space has size `2 ^ (q + k)` and there are at most `2 ^ q` transcripts, the
uniform success fraction is at most `1 / 2 ^ k` [HallgrenHarrow2008]. -/
theorem classical_success_le_inv_pow {A τ : Type*} [Fintype A] [DecidableEq A] [Fintype τ]
    (T : A → τ) (out : τ → A) (q k : ℕ) (hcard : Fintype.card A = 2 ^ (q + k))
    (hq : Fintype.card τ ≤ 2 ^ q) :
    ((Finset.univ.filter (fun a => out (T a) = a)).card : ℝ) / Fintype.card A
      ≤ 1 / (2 : ℝ) ^ k := by
  have hA : 0 < Fintype.card A := by rw [hcard]; positivity
  refine le_trans (classical_success_prob_le T out q hq hA) ?_
  rw [hcard]
  push_cast
  rw [pow_add]
  have heq : (2 : ℝ) ^ q / ((2 : ℝ) ^ q * (2 : ℝ) ^ k) = 1 / (2 : ℝ) ^ k := by
    field_simp
  rw [heq]

/-- A convex combination of deterministic procedures with at most `2 ^ q` transcripts has
uniform average success at most `1 / 2 ^ k` on a secret space of size `2 ^ (q + k)`
[HallgrenHarrow2008]. -/
theorem randomized_success_le_inv_pow {A τ ι : Type*} [Fintype A] [DecidableEq A] [Fintype τ]
    [Fintype ι] (T : ι → A → τ) (out : ι → τ → A) (w : ι → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : (∑ i, w i) = 1)
    (q k : ℕ) (hcard : Fintype.card A = 2 ^ (q + k)) (hq : ∀ _i : ι, Fintype.card τ ≤ 2 ^ q) :
    (∑ i, w i * (((Finset.univ.filter (fun a => out i (T i a) = a)).card : ℝ)
        / Fintype.card A)) ≤ 1 / (2 : ℝ) ^ k := by
  have hA : 0 < Fintype.card A := by rw [hcard]; positivity
  have hbound : ∀ i, ((Finset.univ.filter (fun a => out i (T i a) = a)).card : ℝ)
      / Fintype.card A ≤ 1 / (2 : ℝ) ^ k := fun i =>
    classical_success_le_inv_pow (T i) (out i) q k hcard (hq i)
  calc ∑ i, w i * (((Finset.univ.filter (fun a => out i (T i a) = a)).card : ℝ)
          / Fintype.card A)
      ≤ ∑ i, w i * (1 / (2 : ℝ) ^ k) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hbound i) (hw0 i)
    _ = (∑ i, w i) * (1 / (2 : ℝ) ^ k) := by rw [Finset.sum_mul]
    _ = 1 / (2 : ℝ) ^ k := by rw [hw1, one_mul]

end Qatlib.Papers.AnyCircuit08.MainResults
