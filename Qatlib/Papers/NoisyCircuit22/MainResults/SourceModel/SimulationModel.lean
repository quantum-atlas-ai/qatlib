/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# NoisyCircuit22 — simulation / statistical model

Fixed arXiv:2211.03999v1.  This file contains the minimal abstract vocabulary used to
state Theorem 1 and Corollary 1: total variation distance, probability vectors, a circuit
ensemble with its expectation functional, anti-concentration (Definition 4), and a
polynomial runtime bound.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel

open BigOperators

/-- Total variation distance of two real functions on a finite set. -/
def TotalVariation {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  (1 / 2) * ∑ x, |p x - q x|

/-- A probability vector on a finite outcome set. -/
def IsProbability {α : Type*} [Fintype α] (p : α → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

/-- Advantage of a Boolean statistical test in distinguishing `p` from `q`. -/
def TestAdvantage {α : Type*} [Fintype α] (p q : α → ℝ) (test : α → Bool) : ℝ :=
  |∑ x, (if test x then p x else 0) - ∑ x, (if test x then q x else 0)|

/-- An ensemble of random circuits: a probability on predicates, together with the
expectation functional used throughout the Pauli-path analysis. -/
structure CircuitEnsemble (Circuit : Type*) where
  prob : (Circuit → Prop) → ℝ
  prob_true : prob (fun _ => True) = 1
  prob_mono : ∀ {A B : Circuit → Prop}, (∀ C, A C → B C) → prob A ≤ prob B
  expec : (Circuit → ℝ) →ₗ[ℝ] ℝ
  expec_one : expec (fun _ => 1) = 1

/-- Definition 4, p.10: anti-concentration of the output distribution, with an explicit
constant. -/
def AntiConcentrated {Circuit : Type*} (n : ℕ) (D : CircuitEnsemble Circuit)
    (p : Circuit → (Fin n → Bool) → ℝ) : Prop :=
  ∃ Cac : ℝ, (2 : ℝ) ^ n * ∑ x : Fin n → Bool,
    D.expec (fun C => (p C x) ^ 2) ≤ Cac

/-- `T` is bounded by a polynomial in `n`, `1/ε`, `1/δ`. -/
def PolyBound (T n : ℕ) (ε δ : ℝ) : Prop :=
  ∃ k : ℕ, (T : ℝ) ≤ ((n : ℝ) + 1) ^ k * ((1 / ε) + 1) ^ k * ((1 / δ) + 1) ^ k

/-- Product distribution on `M` independent copies of a distribution on `α`. -/
def ProductDist {α : Type*} (M : ℕ) (p : α → ℝ) : (Fin M → α) → ℝ :=
  fun y => ∏ i, p (y i)

end Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel
