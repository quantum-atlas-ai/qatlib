/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Qatlib.Papers.LinearDiseq07.MainResults.HyperplanePolynomial
set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.LinearDiseq07.MainResults

theorem geomSum_mul_sub_one (x : ℕ) (hx : 1 ≤ x) (k : ℕ) :
    (x - 1) * ∑ i ∈ Finset.range k, x ^ i = x ^ k - 1 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    have h1 : (x - 1) * x ^ n = x ^ (n + 1) - x ^ n := by
      rw [Nat.sub_mul, one_mul, pow_succ']
    have hA : 1 ≤ x ^ n := one_le_pow₀ hx
    have hB : x ^ n ≤ x ^ (n + 1) :=
      Nat.pow_le_pow_right (by omega : 0 < x) (by omega : n ≤ n + 1)
    omega

theorem dvd_pow_sub_one (x : ℕ) (hx : 1 ≤ x) (k : ℕ) : x - 1 ∣ x ^ k - 1 :=
  ⟨∑ i ∈ Finset.range k, x ^ i, (geomSum_mul_sub_one x hx k).symm⟩

theorem lemma7Degree_eq_mul_sum (p k : ℕ) (hp : 2 ≤ p) :
    lemma7Degree p k = (p - 1) * ∑ i ∈ Finset.range k, (2 * p - 2) ^ i := by
  have hx : 1 ≤ 2 * p - 2 := by omega
  have hd : 0 < 2 * p - 3 := by omega
  have hgeom : (2 * p - 3) * ∑ i ∈ Finset.range k, (2 * p - 2) ^ i
      = (2 * p - 2) ^ k - 1 := by
    have h : 2 * p - 2 - 1 = 2 * p - 3 := by omega
    simpa [h] using geomSum_mul_sub_one (2 * p - 2) hx k
  have hdiv : ((2 * p - 2) ^ k - 1) / (2 * p - 3)
      = ∑ i ∈ Finset.range k, (2 * p - 2) ^ i := by
    rw [← hgeom]
    exact Nat.mul_div_cancel_left _ hd
  have hdvd : 2 * p - 3 ∣ (2 * p - 2) ^ k - 1 := ⟨_, hgeom.symm⟩
  unfold lemma7Degree
  rw [Nat.mul_div_assoc (p - 1) hdvd, hdiv]

theorem lemma7Degree_le (p k : ℕ) (hp : 2 ≤ p) (hk : 1 ≤ k) :
    lemma7Degree p k ≤ (p - 1) * k * (2 * p - 2) ^ (k - 1) := by
  rw [lemma7Degree_eq_mul_sum p k hp]
  have hsum : ∑ i ∈ Finset.range k, (2 * p - 2) ^ i
      ≤ k * (2 * p - 2) ^ (k - 1) := by
    have hterm : ∀ i ∈ Finset.range k, (2 * p - 2) ^ i ≤ (2 * p - 2) ^ (k - 1) := by
      intro i hi
      rw [Finset.mem_range] at hi
      exact Nat.pow_le_pow_right (by omega : 0 < 2 * p - 2) (by omega)
    calc ∑ i ∈ Finset.range k, (2 * p - 2) ^ i
        ≤ ∑ _i ∈ Finset.range k, (2 * p - 2) ^ (k - 1) :=
          Finset.sum_le_sum hterm
      _ = k * (2 * p - 2) ^ (k - 1) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  calc (p - 1) * ∑ i ∈ Finset.range k, (2 * p - 2) ^ i
      ≤ (p - 1) * (k * (2 * p - 2) ^ (k - 1)) := Nat.mul_le_mul_left _ hsum
    _ = (p - 1) * k * (2 * p - 2) ^ (k - 1) := by ring

theorem lemma7Degree_le_pow (p k : ℕ) (hp : 2 ≤ p) (hk : 1 ≤ k) :
    lemma7Degree p k ≤ (2 * p) ^ k * k := by
  refine (lemma7Degree_le p k hp hk).trans ?_
  have h1 : p - 1 ≤ 2 * p := by omega
  have h2 : (2 * p - 2) ^ (k - 1) ≤ (2 * p) ^ (k - 1) :=
    Nat.pow_le_pow_left (by omega) (k - 1)
  calc (p - 1) * k * (2 * p - 2) ^ (k - 1)
      ≤ (2 * p) * k * (2 * p) ^ (k - 1) := by
        gcongr
    _ = (2 * p) ^ k * k := by
        have hpow : (2 * p) ^ k = (2 * p) ^ (k - 1) * (2 * p) := by
          conv_lhs => rw [← Nat.sub_add_cancel hk]
          rw [pow_succ]
        rw [hpow]; ring

end Qatlib.Papers.LinearDiseq07.MainResults
