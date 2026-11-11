/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfaces
import Qatlib.Papers.QPatternMatch14.MainResults.Model.PatternStrings

/-!
# Abstract query algorithms and the paper's complexity expressions

Montanaro, *Quantum pattern matching fast on average* (arXiv:1408.1816v3) states
its results in the bounded-error query model: an algorithm is a distribution over
answers for each input together with a worst-case query count.  This file gives
that interface (`QueryAlgorithm`, `successMass`, `boundedError`) and the explicit
complexity expressions appearing in Theorems 1, 2, 4, 5 and Propositions 8, 13,
and Lemmas 10, 11 (Section 1.1, Section 3, Section 4).

The concrete quantum-circuit realisation of these algorithms is deliberately not
modelled; the statements of the paper layer only assert existence of an abstract
`QueryAlgorithm` with the stated cost and success mass.
-/

/-!
# QueryModel

Paper-layer definitions and source results for QPatternMatch14.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.QPatternMatch14.MainResults.Model

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

/-- The uniform distribution on a nonempty finite type (used for random strings in Lemma 7, arXiv:1408.1816v3, p. 9). -/
noncomputable def uniformFinDist (X : Type*) [Fintype X] [Nonempty X] : FinDist X where
  prob _ := (Fintype.card X : ℝ)⁻¹
  nonneg _ := by positivity
  sum_one := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast (Fintype.card_pos (α := X)).ne')

/-- The law of a uniformly random string `P : [m]^d → A`: all coordinates are
independent and uniform.  This is the distribution of the pattern in Lemma 7. -/
noncomputable def randomStringDist {d m : ℕ} (A : Type*) [Fintype A] [Nonempty A] :
    FinDist (DStr d m A) :=
  Qatlib.Concepts.ProbabilityCore.Concentration.independent
    (fun _ : Coord d m => uniformFinDist A)

/-- A bounded-error query algorithm on a finite input type: for every input a
worst-case query count and a probability distribution over answers. -/
structure QueryAlgorithm (Input : Type*) (Answer : Type*) [Fintype Answer] where
  /-- Worst-case number of queries to the input oracle on a given input. -/
  cost : Input → ℕ
  /-- Probability of outputting a given answer on a given input. -/
  outProb : Input → Answer → ℝ
  /-- Probabilities are nonnegative. -/
  nonneg : ∀ i a, 0 ≤ outProb i a
  /-- Probabilities sum to one. -/
  sum_one : ∀ i, ∑ a, outProb i a = 1

/-- A classical (possibly randomised) algorithm is the same abstract interface. -/
abbrev ClassicalAlgorithm (Input : Type*) (Answer : Type*) [Fintype Answer] :=
  QueryAlgorithm Input Answer

/-- The success probability of an algorithm with respect to a specification. -/
noncomputable def successMass {Input Answer : Type*} [Fintype Answer]
    (Alg : QueryAlgorithm Input Answer) (spec : Input → Answer → Prop) (i : Input) : ℝ := by
  classical
  exact ∑ a ∈ Finset.univ.filter (spec i), Alg.outProb i a

/-- Bounded-error correctness: every input succeeds with probability at least
`2/3`, the paper's convention throughout Section 1 and Section 4. -/
def boundedError {Input Answer : Type*} [Fintype Answer]
    (Alg : QueryAlgorithm Input Answer) (spec : Input → Answer → Prop) : Prop :=
  ∀ i, 2 / 3 ≤ successMass Alg spec i

/-- `2 ^ sqrt((2 log₂ 3) d log₂ m)`, the exponential factor `2^{O(d^{3/2}√log m)}`
of Theorem 1 and the `2^{√((2 log₂ 3) d log₂ m)}` factor of Theorem 2. -/
noncomputable def expLogTerm (d m : ℝ) : ℝ :=
  Real.rpow 2 (Real.sqrt ((2 * Real.logb 2 3) * d * Real.logb 2 m))

/-- The query bound of Theorem 1 (arXiv:1408.1816v3, p. 2):
`(n/m)^{d/2} 2^{O(d^{3/2}√(log m))}`. -/
noncomputable def theorem1QueryBound (d n m : ℝ) : ℝ :=
  Real.rpow (n / m) (d / 2) *
    Real.rpow 2 (Real.rpow d (3 / 2) * Real.sqrt (Real.logb 2 m))

/-- The query bound of Theorem 2 (arXiv:1408.1816v3, p. 3):
`(n log²m / m)^{d/2} (ν^d log m 2^{√((2 log₂ 3) d log₂ m)} + 1/√γ)`. -/
noncomputable def theorem2QueryBound (d n m ν γ : ℝ) : ℝ :=
  Real.rpow (n * (Real.log m) ^ 2 * expLogTerm d m / m) (d / 2) *
    (Real.rpow ν d * Real.log m * expLogTerm d m + 1 / Real.sqrt γ)

/-- The query bound of Theorem 4 (arXiv:1408.1816v3, p. 6):
`O(n 2^{√((2 log₂ 3) d n)})`. -/
noncomputable def theorem4QueryBound (d n : ℝ) : ℝ :=
  n * expLogTerm d n

/-- The query bound of Theorem 5 (arXiv:1408.1816v3, p. 8):
`(n/m)^{d/2} ν^d log^{d+1} m 2^{√((2 log₂ 3) d log₂ m)(d/2+1)}`. -/
noncomputable def theorem5QueryBound (d n m ν : ℝ) : ℝ :=
  Real.rpow (n / m) (d / 2) * Real.rpow ν d * Real.rpow (Real.log m) (d + 1) *
    Real.rpow 2 (Real.sqrt ((2 * Real.logb 2 3) * d * Real.logb 2 m) * (d / 2 + 1))

/-- The query bound of Proposition 8 (arXiv:1408.1816v3, p. 9):
`(n/m)^{d/2} 2^{(d/2+1)√((2 log₂ 3) d log₂ m)} log^{d+1} m log n`. -/
noncomputable def proposition8QueryBound (d n m : ℝ) : ℝ :=
  Real.rpow (n / m) (d / 2) *
    Real.rpow 2 ((d / 2 + 1) * Real.sqrt ((2 * Real.logb 2 3) * d * Real.logb 2 m)) *
    Real.rpow (Real.log m) (d + 1) * Real.log n

/-- Quantum lower bound of Lemma 10 (arXiv:1408.1816v3, p. 10):
`Ω((n/m)^{d/2}/√γ)`. -/
noncomputable def lemma10QuantumBound (d n m γ : ℝ) : ℝ :=
  Real.rpow (n / m) (d / 2) / Real.sqrt γ

/-- Classical lower bound of Lemma 10: `Ω((n/m)^d/γ)`. -/
noncomputable def lemma10ClassicalBound (d n m γ : ℝ) : ℝ :=
  Real.rpow (n / m) d / γ

/-- The bound `n^{d/2} + (n/m)^d + 1/γ` of Lemma 11 and Theorem 12
(arXiv:1408.1816v3, pp. 11-12). -/
noncomputable def injectiveBound (d n m γ : ℝ) : ℝ :=
  Real.rpow n (d / 2) + Real.rpow (n / m) d + 1 / γ

/-- The random-string classical lower bound of Proposition 13
(arXiv:1408.1816v3, p. 12): `(n/m)^d log_q m + n^{d/2}/√(log_q n)`. -/
noncomputable def proposition13Bound (d n m q : ℝ) : ℝ :=
  Real.rpow (n / m) d * Real.logb q m +
    Real.rpow n (d / 2) / Real.sqrt (Real.logb q n)

/-- The success probability is at most one (bounded-error bookkeeping of Theorem 2, arXiv:1408.1816v3, p. 3). -/
theorem successMass_le_one {Input Answer : Type*} [Fintype Answer]
    (Alg : QueryAlgorithm Input Answer) (spec : Input → Answer → Prop) (i : Input) :
    successMass Alg spec i ≤ 1 := by
  classical
  unfold successMass
  rw [← Alg.sum_one i]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro a ha
    exact Finset.mem_univ a
  · intro a _ ha
    exact Alg.nonneg i a

/-- Success mass is nonnegative (bounded-error bookkeeping of Theorem 2, arXiv:1408.1816v3, p. 3). -/
theorem successMass_nonneg {Input Answer : Type*} [Fintype Answer]
    (Alg : QueryAlgorithm Input Answer) (spec : Input → Answer → Prop) (i : Input) :
    0 ≤ successMass Alg spec i := by
  classical
  unfold successMass
  exact Finset.sum_nonneg fun a _ => Alg.nonneg i a

end Qatlib.Papers.QPatternMatch14.MainResults.Model
