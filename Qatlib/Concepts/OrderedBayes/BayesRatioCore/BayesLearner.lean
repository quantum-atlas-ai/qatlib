/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.FiniteStoppingTail
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution

/-!
# Bayesian learner kernels for ordered search

Prefix masses and binary entropy define information quantities and cut selection for a finite
ordered posterior. The update formulas and `learnerNext` give a randomized learner that halts
when an entry reaches the threshold and otherwise samples an answer to update the posterior, in
the adaptive learning setting of [BenOrHassidim2007]

## Main statements

* `updateFalse` and `updateTrue`: define the two normalized update formulas.
* `stageTwoCut` and `haltCut`: choose query and stopping indices.
* `learnerExpectedStages`: sums finite survival probabilities.

## References

* [Ben-Or and Hassidim, 2007][BenOrHassidim2007]
-/

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open scoped BigOperators NNReal ENNReal

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

open Classical

/-- The sum of entries of `a` at indices at most `i`. -/
noncomputable def prefixMass {n : ℕ} (a : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j : Fin n, if j.val ≤ i.val then a j else 0

/-- The binary entropy expression `-p * log₂ p - (1 - p) * log₂ (1 - p)`. -/
noncomputable def binEntropy (p : ℝ) : ℝ :=
  -(p * (Real.log p / Real.log 2) + (1 - p) * (Real.log (1 - p) / Real.log 2))

/-- The information expression `1 - binEntropy p` for a query with parameter `p`. -/
noncomputable def queryInfo (p : ℝ) : ℝ := 1 - binEntropy p

/-- The base two entropy expression given by the negative sum of `a i * log₂ (a i)`. -/
noncomputable def entropy {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  -(∑ i, a i * (Real.log (a i) / Real.log 2))

/-- The information expression `log₂ n - entropy a` relative to the uniform posterior. -/
noncomputable def postInfo {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  Real.log n / Real.log 2 - entropy a

/-- The update denominator `p * prefixMass a i + (1 - p) * (1 - prefixMass a i)`. -/
noncomputable def normFalse {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (p : ℝ) : ℝ :=
  p * prefixMass a i + (1 - p) * (1 - prefixMass a i)

/-- The complementary update denominator `1 - normFalse a i p`. -/
noncomputable def normTrue {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (p : ℝ) : ℝ :=
  1 - normFalse a i p

/-- The update weighting entries at or below the cut by `p` and entries above it by `1 - p`,
then dividing by `normFalse`. -/
noncomputable def updateFalse {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (p : ℝ) : Fin n → ℝ :=
  fun j => (if j.val ≤ i.val then p * a j else (1 - p) * a j) / normFalse a i p

/-- The update weighting entries at or below the cut by `1 - p` and entries above it by `p`,
then dividing by `normTrue`. -/
noncomputable def updateTrue {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (p : ℝ) : Fin n → ℝ :=
  fun j => (if j.val ≤ i.val then (1 - p) * a j else p * a j) / normTrue a i p

/-- The finite set of cut indices whose prefix mass lies in `[1 / 2 - ε, 1 / 2)`. -/
noncomputable def cutSet {n : ℕ} (a : Fin n → ℝ) (ε : ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => 1 / 2 - ε ≤ prefixMass a i ∧ prefixMass a i < 1 / 2

/-- The least index in `cutSet a ε` when it is nonempty, and index zero otherwise. -/
noncomputable def stageTwoCut {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ε : ℝ) : Fin n :=
  if h : (cutSet a ε).Nonempty then (cutSet a ε).min' h else ⟨0, hn⟩

/-- The least index whose entry is at least `ε` when such an index exists, and index zero
otherwise. -/
noncomputable def haltCut {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ε : ℝ) : Fin n :=
  if h : (Finset.univ.filter fun i : Fin n => ε ≤ a i).Nonempty then
    (Finset.univ.filter fun i : Fin n => ε ≤ a i).min' h
  else ⟨0, hn⟩

/-- The nonnegative real value obtained by clamping a real number to the interval `[0, 1]`. -/
def clampProb (x : ℝ) : ℝ≥0 := ⟨max 0 (min x 1), le_max_left 0 (min x 1)⟩

/-- The clamped probability is at most one. -/
theorem clampProb_le (x : ℝ) : clampProb x ≤ 1 :=
  NNReal.coe_le_coe.mp (max_le zero_le_one (min_le_right x 1))

/-- The learner transition that halts at `haltCut` if an entry reaches `ε`, and otherwise
applies a Bernoulli selected update at `stageTwoCut` using the clamped `normTrue`
probability. -/
noncomputable def learnerNext {n : ℕ} (hn : 0 < n) (p ε : ℝ) :
    (Fin n → ℝ) → PMF (RandomizedExecution.Configuration (Fin n → ℝ) (Fin n)) :=
  fun a =>
    if _h : ∃ i : Fin n, ε ≤ a i then PMF.pure (Sum.inl (haltCut hn a ε))
    else
      (PMF.bernoulli
          (clampProb (normTrue a (stageTwoCut hn a ε) p)) (clampProb_le _)).bind
        fun b =>
          PMF.pure
            (Sum.inr
              (if b then updateTrue a (stageTwoCut hn a ε) p
                else updateFalse a (stageTwoCut hn a ε) p))

/-- The extended nonnegative sum of finite survival probabilities of the learner from the
initial posterior. -/
noncomputable def learnerExpectedStages {n : ℕ} (hn : 0 < n) (p ε : ℝ)
    (a : Fin n → ℝ) : ℝ≥0∞ :=
  ∑' t : ℕ, finiteSurvival (learnerNext hn p ε) t (Sum.inr a)

/-- The constant posterior with value `1 / n` at each index. -/
noncomputable def uniformPosterior {n : ℕ} : Fin n → ℝ := fun _ => 1 / n

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
