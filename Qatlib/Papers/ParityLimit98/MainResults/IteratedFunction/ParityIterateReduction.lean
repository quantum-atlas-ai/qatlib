/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound
set_option warningAsError false

namespace Qatlib.Papers.ParityLimit98.MainResults.IteratedFunction

open scoped BigOperators

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false

def iterMap {N : ℕ} (f : ZMod N → Bool) (p : ZMod N × ZMod 2) : ZMod N × ZMod 2 :=
  (p.1 + 1, p.2 + (if f p.1 = true then (1 : ZMod 2) else 0))

def partialSign {N : ℕ} (f : ZMod N → Bool) (k : ℕ) : ZMod 2 :=
  ∑ i ∈ Finset.range k, (if f ((i : ℕ) : ZMod N) = true then (1 : ZMod 2) else 0)

theorem iterMap_iterate {N : ℕ} (f : ZMod N → Bool) (k : ℕ) :
    (iterMap f)^[k] (0, 0) = ((k : ZMod N), partialSign f k) := by
  induction k with
  | zero => simp [partialSign]
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [iterMap, partialSign, Finset.sum_range_succ, Nat.cast_succ]

def zmodEquivFin (N : ℕ) [NeZero N] : Fin N ≃ ZMod N where
  toFun i := ((i : ℕ) : ZMod N)
  invFun x := ⟨x.val, x.val_lt⟩
  left_inv i := Fin.ext (by simpa using ZMod.val_natCast_of_lt (n := N) (a := (i : ℕ)) i.isLt)
  right_inv x := by
    show ((x.val : ℕ) : ZMod N) = x
    exact ZMod.natCast_zmod_val x

theorem sum_range_cast_eq_sum_univ {N : ℕ} [NeZero N] {M : Type*} [AddCommMonoid M]
    (g : ZMod N → M) :
    (∑ i ∈ Finset.range N, g ((i : ℕ) : ZMod N)) = ∑ x : ZMod N, g x := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => g ((i : ℕ) : ZMod N)) N]
  exact Fintype.sum_equiv (zmodEquivFin N) _ _ (fun i => rfl)

theorem card_cast_sum {α : Type*} [Fintype α] (p : α → Bool) :
    (∑ x : α, (if p x = true then (1 : ZMod 2) else 0))
      = ((Finset.univ.filter (fun x => p x = true)).card : ZMod 2) := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

def truthSum {N : ℕ} [NeZero N] (f : ZMod N → Bool) : ZMod 2 :=
  ∑ x : ZMod N, (if f x = true then (1 : ZMod 2) else 0)

theorem iterMap_iterate_card {N : ℕ} [NeZero N] (f : ZMod N → Bool) :
    (iterMap f)^[N] (0, 0) = (0, truthSum f) := by
  rw [iterMap_iterate]
  have hcast : (N : ZMod N) = 0 := ZMod.natCast_self N
  have hsum : partialSign f N = truthSum f := by
    unfold partialSign truthSum
    exact sum_range_cast_eq_sum_univ (fun x => if f x = true then (1 : ZMod 2) else 0)
  rw [hcast, hsum]

theorem truthSum_eq_card {N : ℕ} [NeZero N] (f : ZMod N → Bool) :
    truthSum f = ((Finset.univ.filter (fun x => f x = true)).card : ZMod 2) := by
  unfold truthSum
  exact card_cast_sum f

theorem truthSum_comp_eq_card {N : ℕ} [NeZero N] (f : Fin N → Bool) :
    truthSum (fun x : ZMod N => f ((zmodEquivFin N).symm x))
      = ((Finset.univ.filter (fun i : Fin N => f i = true)).card : ZMod 2) := by
  unfold truthSum
  change (∑ x : ZMod N, (if f ((zmodEquivFin N).symm x) = true then (1 : ZMod 2) else 0))
      = ((Finset.univ.filter (fun i : Fin N => f i = true)).card : ZMod 2)
  rw [← Fintype.sum_equiv (zmodEquivFin N)
        (fun i : Fin N => if f i = true then (1 : ZMod 2) else 0)
        (fun x : ZMod N => if f ((zmodEquivFin N).symm x) = true then (1 : ZMod 2) else 0)
        (fun i => by simp)]
  exact card_cast_sum f

theorem iterate_second_eq_truthSum {N : ℕ} [NeZero N] (f : ZMod N → Bool) :
    ((iterMap f)^[N] (0, 0)).2 = truthSum f := by
  rw [iterMap_iterate_card]

theorem truthSum_eq_of_iterate_eq {N : ℕ} [NeZero N] (f g : ZMod N → Bool)
    (h : ((iterMap f)^[N] (0, 0)).2 = ((iterMap g)^[N] (0, 0)).2) :
    truthSum f = truthSum g := by
  rw [iterate_second_eq_truthSum, iterate_second_eq_truthSum] at h
  exact h

end Qatlib.Papers.ParityLimit98.MainResults.IteratedFunction
