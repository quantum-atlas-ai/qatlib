/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.List.Monad
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Order.Nat
import Mathlib.Order.SuccPred.Nat
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.Result

/-!
# Zeckendorf encoding of Fibonacci strings

This module defines `Allowed` Boolean strings with no adjacent true entries and their
Fibonacci-weighted value `starWeight`. For allowed strings of length `n`, the values are exactly
the natural numbers strictly below `Nat.fib (n + 2)`, with each value represented uniquely.

The map `zMap` and the equivalence `zEquiv` package this correspondence as the finite-string
bijection in Proposition 4 of [Jordan2008].

## Main statements

* `starWeight_lt_fib`: the Fibonacci bound for an allowed string of fixed length.
* `exists_allowed_of_lt`: existence of an allowed representation below that bound.
* `allowed_injective`: uniqueness among allowed strings of the same length.
* `proposition4_zeckendorf_bijection`: bijectivity of `zMap`.

## References

* [Jordan, 2008][Jordan2008]
-/

set_option autoImplicit false
noncomputable section

open Nat

namespace Qatlib.Papers.BeyondCircuit08.MainResults.Zeckendorf

/-- The Fibonacci-weighted value of a Boolean list, with the head of a list of length `n`
carrying weight `Nat.fib (n + 1)` when true. -/
def starWeight : List Bool → ℕ
  | [] => 0
  | b :: t => starWeight t + if b then Nat.fib (t.length + 2) else 0

/-- The condition that a Boolean list contains no pair of adjacent true entries. -/
def Allowed : List Bool → Prop
  | [] => True
  | [_] => True
  | b :: c :: t => ¬ (b = true ∧ c = true) ∧ Allowed (c :: t)

/-- Prepending a false entry leaves the Fibonacci-weighted value unchanged. -/
lemma starWeight_false_cons (t : List Bool) :
    starWeight (false :: t) = starWeight t := by
  simp [starWeight]

/-- Prepending a true entry adds the Fibonacci weight `Nat.fib (t.length + 2)` to the value of
the tail. -/
lemma starWeight_true_cons (t : List Bool) :
    starWeight (true :: t) = starWeight t + Nat.fib (t.length + 2) := by
  simp [starWeight]

/-- A list beginning with false is allowed exactly when its tail is allowed. -/
lemma allowed_false_cons (t : List Bool) : Allowed (false :: t) ↔ Allowed t := by
  cases t with
  | nil => simp [Allowed]
  | cons c u => simp [Allowed]

/-- A list beginning with true is allowed exactly when its tail is empty or begins with false
followed by an allowed list. -/
lemma allowed_true_cons (t : List Bool) :
    Allowed (true :: t) ↔ (t = [] ∨ ∃ u, t = false :: u ∧ Allowed u) := by
  cases t with
  | nil => simp [Allowed]
  | cons c u =>
    cases c
    · simp [Allowed, allowed_false_cons]
    · simp [Allowed]

/-- The tail of an allowed list beginning with true is allowed. -/
lemma allowed_of_true_cons {t : List Bool} (h : Allowed (true :: t)) : Allowed t := by
  rcases (allowed_true_cons t).1 h with rfl | ⟨u, rfl, hu⟩
  · trivial
  · exact (allowed_false_cons u).2 hu

/-- An allowed Boolean list of length `L` has Fibonacci-weighted value strictly below `Nat.fib
(L + 2)`. -/
theorem starWeight_lt_fib : ∀ L (l : List Bool), l.length = L → Allowed l →
    starWeight l < Nat.fib (L + 2) := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro l hl ha
    cases l with
    | nil =>
      have hL : L = 0 := by simpa using hl.symm
      subst hL
      simp [starWeight]
    | cons b t =>
      have hlen : t.length + 1 = L := by simpa using hl
      cases b
      · have ha' : Allowed t := (allowed_false_cons t).1 ha
        have ht : t.length = L - 1 := by omega
        have hih := ih (L - 1) (by omega) t ht ha'
        rw [starWeight_false_cons]
        calc starWeight t < Nat.fib ((L - 1) + 2) := hih
          _ = Nat.fib (L + 1) := by rw [show L - 1 + 2 = L + 1 by omega]
          _ ≤ Nat.fib (L + 2) := Nat.fib_le_fib_succ
      · rcases (allowed_true_cons t).1 ha with ht | ⟨u, rfl, hau⟩
        · subst ht
          have hL : L = 1 := by simpa using hlen.symm
          subst hL
          rw [starWeight_true_cons]
          simp only [starWeight, List.length_nil]
          norm_num [Nat.fib]
        · rw [starWeight_true_cons, starWeight_false_cons]
          simp only [List.length_cons] at hlen
          have hLge : 2 ≤ L := by omega
          have hu : u.length = L - 2 := by omega
          have hih := ih (L - 2) (by omega) u hu hau
          have hih' : starWeight u < Nat.fib L := by
            rw [show L - 2 + 2 = L by omega] at hih
            exact hih
          have hlen2 : (false :: u).length + 2 = L + 1 := by
            simp only [List.length_cons]
            omega
          rw [hlen2, Nat.fib_add_two (n := L)]
          omega

/-- Every natural number strictly below `Nat.fib (L + 2)` is the Fibonacci-weighted value of an
allowed Boolean list of length `L`. -/
theorem exists_allowed_of_lt : ∀ L (v : ℕ), v < Nat.fib (L + 2) →
    ∃ l : List Bool, l.length = L ∧ Allowed l ∧ starWeight l = v := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro v hv
    cases L with
    | zero =>
      have hv0 : v = 0 := by
        have h : Nat.fib (0 + 2) = 1 := by simp
        omega
      subst hv0
      exact ⟨[], rfl, trivial, rfl⟩
    | succ m =>
      cases m with
      | zero =>
        norm_num [Nat.fib] at hv
        cases v with
        | zero => exact ⟨[false], rfl, trivial, by simp [starWeight]⟩
        | succ v' =>
          cases v' with
          | zero => exact ⟨[true], rfl, trivial, by simp [starWeight]⟩
          | succ v'' => omega
      | succ n =>
        have hv' : v < Nat.fib ((n + 2) + 2) := hv
        rw [Nat.fib_add_two (n := n + 2)] at hv'
        by_cases hlow : v < Nat.fib (n + 3)
        · have hvlow : v < Nat.fib ((n + 1) + 2) := by
            rwa [show n + 1 + 2 = n + 3 by omega]
          obtain ⟨l, hl, ha, hz⟩ := ih (n + 1) (by omega) v hvlow
          exact ⟨false :: l, by simp [hl], (allowed_false_cons l).2 ha,
            by simp [starWeight, hz]⟩
        · have hge : Nat.fib (n + 3) ≤ v := Nat.le_of_not_lt hlow
          have hw : v - Nat.fib (n + 3) < Nat.fib (n + 2) := by
            rw [Nat.sub_lt_iff_lt_add hge]
            omega
          obtain ⟨u, hu, hau, hzu⟩ := ih n (by omega) (v - Nat.fib (n + 3)) hw
          refine ⟨true :: false :: u, by simp [hu], ?_, ?_⟩
          · rw [allowed_true_cons]
            exact Or.inr ⟨u, rfl, hau⟩
          · rw [starWeight_true_cons, starWeight_false_cons]
            have hlen2 : (false :: u).length + 2 = n + 3 := by
              simp only [List.length_cons]
              omega
            rw [hlen2, hzu, Nat.sub_add_cancel hge]

/-- Two allowed Boolean lists of the same length with equal Fibonacci-weighted values are equal. -/
theorem allowed_injective : ∀ L (l₁ l₂ : List Bool), l₁.length = L → l₂.length = L →
    Allowed l₁ → Allowed l₂ → starWeight l₁ = starWeight l₂ → l₁ = l₂ := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
    intro l₁ l₂ h₁ h₂ ha₁ ha₂ hw
    cases L with
    | zero =>
      have hl₁ : l₁ = [] := by
        cases l₁ with
        | nil => rfl
        | cons b t => simp at h₁
      have hl₂ : l₂ = [] := by
        cases l₂ with
        | nil => rfl
        | cons b t => simp at h₂
      rw [hl₁, hl₂]
    | succ m =>
      cases l₁ with
      | nil => simp at h₁
      | cons b t =>
        cases l₂ with
        | nil => simp at h₂
        | cons c u =>
          have ht : t.length = m := by simpa using h₁
          have hu : u.length = m := by simpa using h₂
          cases b <;> cases c
          · rw [starWeight_false_cons, starWeight_false_cons] at hw
            have hait : Allowed t := (allowed_false_cons t).1 ha₁
            have haiu : Allowed u := (allowed_false_cons u).1 ha₂
            have htu : t = u := ih m (by omega) t u ht hu hait haiu hw
            simp [htu]
          · exfalso
            rw [starWeight_false_cons, starWeight_true_cons] at hw
            have htlt : starWeight t < Nat.fib (m + 2) := by
              have := starWeight_lt_fib m t ht ((allowed_false_cons t).1 ha₁)
              rwa [show m + 2 = m + 2 by rfl] at this
            have hu2 : u.length + 2 = m + 2 := by omega
            rw [hu2] at hw
            omega
          · exfalso
            rw [starWeight_true_cons, starWeight_false_cons] at hw
            have hult : starWeight u < Nat.fib (m + 2) := by
              have := starWeight_lt_fib m u hu ((allowed_false_cons u).1 ha₂)
              rwa [show m + 2 = m + 2 by rfl] at this
            have ht2 : t.length + 2 = m + 2 := by omega
            rw [ht2] at hw
            omega
          · rw [starWeight_true_cons, starWeight_true_cons] at hw
            have ht2 : t.length + 2 = m + 2 := by omega
            have hu2 : u.length + 2 = m + 2 := by omega
            rw [ht2, hu2] at hw
            have hw' : starWeight t = starWeight u := by omega
            have hait : Allowed t := allowed_of_true_cons ha₁
            have haiu : Allowed u := allowed_of_true_cons ha₂
            have htu : t = u := ih m (by omega) t u ht hu hait haiu hw'
            simp [htu]

/-- The type of allowed Boolean lists of length `n`. -/
def PStrings (n : ℕ) : Type := {l : List Bool // l.length = n ∧ Allowed l}

/-- The Fibonacci-weighted value of an allowed length-`n` string, regarded as an element of `Fin
(Nat.fib (n + 2))`. -/
def zMap {n : ℕ} (s : PStrings n) : Fin (Nat.fib (n + 2)) :=
  ⟨starWeight s.1, by
    have hl : s.1.length = n := s.2.1
    have := starWeight_lt_fib n s.1 hl s.2.2
    simpa using this⟩

/-- The Fibonacci encoding `zMap` is injective on allowed strings of a fixed length. -/
theorem zMap_injective {n : ℕ} : Function.Injective (zMap (n := n)) := by
  intro a b hab
  apply Subtype.ext
  have hw : starWeight a.1 = starWeight b.1 := by
    have := congrArg Fin.val hab
    simpa [zMap] using this
  exact allowed_injective n a.1 b.1 a.2.1 b.2.1 a.2.2 b.2.2 hw

/-- The Fibonacci encoding `zMap` reaches every natural number below `Nat.fib (n + 2)`. -/
theorem zMap_surjective {n : ℕ} : Function.Surjective (zMap (n := n)) := by
  intro v
  obtain ⟨l, hl, ha, hz⟩ := exists_allowed_of_lt n v.1 v.2
  refine ⟨⟨l, hl, ha⟩, ?_⟩
  apply Fin.ext
  simpa [zMap] using hz

/-- The Fibonacci encoding of allowed length-`n` strings is bijective onto `Fin (Nat.fib (n +
2))`, as in [Jordan, Proposition 4][Jordan2008]. -/
theorem proposition4_zeckendorf_bijection (n : ℕ) : Function.Bijective (zMap (n := n)) :=
  ⟨zMap_injective, zMap_surjective⟩

/-- The equivalence between allowed length-`n` Boolean strings and `Fin (Nat.fib (n + 2))`
induced by [Jordan, Proposition 4][Jordan2008]. -/
def zEquiv (n : ℕ) : PStrings n ≃ Fin (Nat.fib (n + 2)) :=
  Equiv.ofBijective zMap (proposition4_zeckendorf_bijection n)

end Qatlib.Papers.BeyondCircuit08.MainResults.Zeckendorf
