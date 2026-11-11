/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Finite probability distributions for the game arguments

This module defines `FinProb`, a normalized family of nonnegative real weights on a finite type,
and its event probabilities and pushforward distributions. It supplies the elementary
probability identities used in the classical game arguments of [ChildsEtAl2003].

## Main statements

* `FinProb`: a finite probability distribution.
* `FinProb.eventMass_union_le`: the union bound for two events.
* `FinProb.eventMass_pushforward`: the event probability identity for a pushforward.

## References

* [Childs et al., 2003][ChildsEtAl2003]
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.QWalkSpeedup02.MainResults.Common.FiniteProbability

/-- A probability distribution on a finite type, represented by nonnegative real weights summing
to one. -/
structure FinProb (Ω : Type*) [Fintype Ω] where

  prob : Ω → ℝ

  nonneg : ∀ ω, 0 ≤ prob ω

  sum_one : (∑ ω, prob ω) = 1

namespace FinProb

variable {Ω : Type*} [Fintype Ω]

/-- The probability of a decidable event, computed by summing the weights of its outcomes. -/
def eventMass (P : FinProb Ω) (E : Ω → Prop) [DecidablePred E] : ℝ :=
  ∑ ω, if E ω then P.prob ω else 0

/-- Every event has nonnegative probability under a finite probability distribution. -/
lemma eventMass_nonneg (P : FinProb Ω) (E : Ω → Prop) [DecidablePred E] :
    0 ≤ P.eventMass E := by
  unfold eventMass
  exact Finset.sum_nonneg (fun ω _ => by
    split_ifs with h
    · exact P.nonneg ω
    · exact le_rfl)

/-- Every event has probability at most one under a finite probability distribution. -/
lemma eventMass_le_one (P : FinProb Ω) (E : Ω → Prop) [DecidablePred E] :
    P.eventMass E ≤ 1 := by
  unfold eventMass
  calc ∑ ω, (if E ω then P.prob ω else 0) ≤ ∑ ω, P.prob ω := by
        apply Finset.sum_le_sum
        intro ω _
        split_ifs with h
        · exact le_rfl
        · exact P.nonneg ω
    _ = 1 := P.sum_one

/-- Pointwise implication between events implies the corresponding inequality of their
probabilities. -/
lemma eventMass_mono (P : FinProb Ω) {E F : Ω → Prop} [DecidablePred E]
    [DecidablePred F] (h : ∀ ω, E ω → F ω) : P.eventMass E ≤ P.eventMass F := by
  unfold eventMass
  apply Finset.sum_le_sum
  intro ω _
  by_cases hE : E ω
  · have hF : F ω := h ω hE
    simp [hE, hF]
  · by_cases hF : F ω <;> simp [hE, hF, P.nonneg ω]

/-- Pointwise equivalent events have equal probabilities. -/
lemma eventMass_congr (P : FinProb Ω) {E F : Ω → Prop} [DecidablePred E]
    [DecidablePred F] (h : ∀ ω, E ω ↔ F ω) : P.eventMass E = P.eventMass F := by
  unfold eventMass
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hE : E ω
  · have hF : F ω := (h ω).mp hE
    simp [hE, hF]
  · have hF : ¬ F ω := fun hF => hE ((h ω).mpr hF)
    simp [hE, hF]

/-- The probabilities of an event and its complement sum to one. -/
lemma eventMass_compl (P : FinProb Ω) (E : Ω → Prop) [DecidablePred E] :
    P.eventMass E + P.eventMass (fun ω => ¬ E ω) = 1 := by
  unfold eventMass
  rw [← Finset.sum_add_distrib, ← P.sum_one]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : E ω <;> simp [h]

/-- The probability of the union of two events is at most the sum of their probabilities. -/
lemma eventMass_union_le (P : FinProb Ω) (E F : Ω → Prop) [DecidablePred E]
    [DecidablePred F] :
    P.eventMass (fun ω => E ω ∨ F ω) ≤ P.eventMass E + P.eventMass F := by
  unfold eventMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hE : E ω <;> by_cases hF : F ω <;> simp [hE, hF, P.nonneg ω]

/-- The distribution induced by a map `f`, assigning each target value the probability of its
fiber. -/
def pushforward (P : FinProb Ω) {T : Type*} [Fintype T] [DecidableEq T]
    (f : Ω → T) : FinProb T where
  prob t := P.eventMass (fun ω => f ω = t)
  nonneg t := P.eventMass_nonneg _
  sum_one := by
    have h : (∑ t, P.eventMass (fun ω => f ω = t))
        = ∑ t, ∑ ω, (if f ω = t then P.prob ω else 0) := rfl
    rw [h, Finset.sum_comm, ← P.sum_one]
    apply Finset.sum_congr rfl
    intro ω _
    rw [Finset.sum_eq_single (f ω)]
    · simp
    · intro b _ hb
      rw [if_neg (Ne.symm hb)]
    · intro h
      simp at h

/-- The probability of `W` under the pushforward along `f` equals the probability of the event
`W ∘ f` under the original distribution. -/
lemma eventMass_pushforward (P : FinProb Ω) {T : Type*} [Fintype T] [DecidableEq T]
    (f : Ω → T) (W : T → Prop) [DecidablePred W] :
    P.eventMass (fun ω => W (f ω)) = (P.pushforward f).eventMass W := by
  have hQ : (P.pushforward f).eventMass W
      = ∑ t, if W t then P.eventMass (fun ω => f ω = t) else 0 := rfl
  rw [hQ]
  unfold eventMass
  have hpush : ∀ t, (if W t then (∑ ω, if f ω = t then P.prob ω else 0) else 0)
      = ∑ ω, (if W t then (if f ω = t then P.prob ω else 0) else 0) := by
    intro t
    by_cases hW : W t <;> simp [hW]
  simp only [hpush]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Finset.sum_eq_single (f ω)]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb)]
    simp
  · intro h
    simp at h

end FinProb
