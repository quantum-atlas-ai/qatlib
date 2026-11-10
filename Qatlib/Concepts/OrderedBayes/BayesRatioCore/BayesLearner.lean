/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.FiniteStoppingTail
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
set_option warningAsError false
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open scoped BigOperators NNReal ENNReal

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

open Classical

noncomputable def prefixMass {n : ℕ} (a : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j : Fin n, if j.val ≤ i.val then a j else 0

noncomputable def binEntropy (p : ℝ) : ℝ :=
  -(p * (Real.log p / Real.log 2) + (1 - p) * (Real.log (1 - p) / Real.log 2))

noncomputable def queryInfo (p : ℝ) : ℝ := 1 - binEntropy p

noncomputable def entropy {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  -(∑ i, a i * (Real.log (a i) / Real.log 2))

noncomputable def postInfo {n : ℕ} (a : Fin n → ℝ) : ℝ :=
  Real.log n / Real.log 2 - entropy a

noncomputable def normFalse {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (p : ℝ) : ℝ :=
  p * prefixMass a i + (1 - p) * (1 - prefixMass a i)

noncomputable def normTrue {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (p : ℝ) : ℝ :=
  1 - normFalse a i p

noncomputable def updateFalse {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (p : ℝ) : Fin n → ℝ :=
  fun j => (if j.val ≤ i.val then p * a j else (1 - p) * a j) / normFalse a i p

noncomputable def updateTrue {n : ℕ} (a : Fin n → ℝ) (i : Fin n) (p : ℝ) : Fin n → ℝ :=
  fun j => (if j.val ≤ i.val then (1 - p) * a j else p * a j) / normTrue a i p

noncomputable def cutSet {n : ℕ} (a : Fin n → ℝ) (ε : ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => 1 / 2 - ε ≤ prefixMass a i ∧ prefixMass a i < 1 / 2

noncomputable def stageTwoCut {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ε : ℝ) : Fin n :=
  if h : (cutSet a ε).Nonempty then (cutSet a ε).min' h else ⟨0, hn⟩

noncomputable def haltCut {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) (ε : ℝ) : Fin n :=
  if h : (Finset.univ.filter fun i : Fin n => ε ≤ a i).Nonempty then
    (Finset.univ.filter fun i : Fin n => ε ≤ a i).min' h
  else ⟨0, hn⟩

def clampProb (x : ℝ) : ℝ≥0 := ⟨max 0 (min x 1), le_max_left 0 (min x 1)⟩

theorem clampProb_le (x : ℝ) : clampProb x ≤ 1 :=
  NNReal.coe_le_coe.mp (max_le zero_le_one (min_le_right x 1))

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

noncomputable def learnerExpectedStages {n : ℕ} (hn : 0 < n) (p ε : ℝ)
    (a : Fin n → ℝ) : ℝ≥0∞ :=
  ∑' t : ℕ, finiteSurvival (learnerNext hn p ε) t (Sum.inr a)

noncomputable def uniformPosterior {n : ℕ} : Fin n → ℝ := fun _ => 1 / n

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
