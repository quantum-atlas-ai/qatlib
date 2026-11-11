/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# Shared vocabulary for "Verifiable Quantum Advantage without Structure"

Brakerski--Canetti--Qian, fixed arXiv:2204.02063v3.

This file collects the elementary notions used by the paper-layer statements:
negligible functions, finite probability distributions, statistical distance and
collision probability (§2.1, §7.1 and Appendix A of the paper).  The
cryptographic objects themselves (random oracles, one-wayness, proofs of
quantumness, PKE, signatures) are represented in the individual claim files by
their security predicates, because the query-counted oracle model of the paper
is not yet mechanised in the shared library.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Filter

namespace Qatlib.Papers.VerifiableAdv22.MainResults

/-- `Negligible ε`: the function `ε : ℕ → ℝ` decays faster than every inverse
polynomial.  This is the paper's notion of a negligible function (§2.1). -/
def Negligible (ε : ℕ → ℝ) : Prop :=
  ∀ c : ℕ, ∀ᶠ n in Filter.atTop, ε n ≤ (n : ℝ) ^ (-(c : ℤ))

/-- `NonNegligible ε`: `ε` is not negligible, i.e. it is non-negligible in the
sense used for the soundness/security statements of the paper. -/
def NonNegligible (ε : ℕ → ℝ) : Prop := ¬ Negligible ε

/-- A probability distribution on a finite type, represented by its mass
function.  Finite distributions are the only ones used in the paper's
probability-theoretic lemmas (Lemma 7.5, Lemma 8.5, Lemma 9.8). -/
structure ProbDist (α : Type*) [Fintype α] where
  /-- the probability mass function -/
  prob : α → ℝ
  /-- masses are nonnegative -/
  nonneg : ∀ a, 0 ≤ prob a
  /-- the masses sum to one -/
  sum_one : ∑ a, prob a = 1

/-- The uniform distribution on a finite nonempty type. -/
def uniformProb (α : Type*) [Fintype α] [Nonempty α] : ProbDist α where
  prob := fun _ => (Fintype.card α : ℝ)⁻¹
  nonneg := by
    intro a
    positivity
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- Statistical distance `∆(p,q) = ½ ∑_a |p(a) − q(a)|`. -/
def statDist {α : Type*} [Fintype α] (p q : ProbDist α) : ℝ :=
  (1 / 2) * ∑ a, |p.prob a - q.prob a|

/-- Collision probability `Col(p) = ∑_a p(a)²`. -/
def collisionProb {α : Type*} [Fintype α] (p : ProbDist α) : ℝ :=
  ∑ a, p.prob a ^ 2

/-- Statistical distance is nonnegative. -/
theorem statDist_nonneg {α : Type*} [Fintype α] (p q : ProbDist α) :
    0 ≤ statDist p q := by
  unfold statDist
  positivity

/-- Statistical distance to itself is zero. -/
theorem statDist_self {α : Type*} [Fintype α] (p : ProbDist α) :
    statDist p p = 0 := by
  unfold statDist
  simp

/-- Collision probability is nonnegative. -/
theorem collisionProb_nonneg {α : Type*} [Fintype α] (p : ProbDist α) :
    0 ≤ collisionProb p := by
  unfold collisionProb
  positivity

end Qatlib.Papers.VerifiableAdv22.MainResults
