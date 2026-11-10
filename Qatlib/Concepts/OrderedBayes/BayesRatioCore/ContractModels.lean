/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.BayesTruthDefs
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryAlgorithm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Probability.ProbabilityMassFunction.Constructions
set_option warningAsError false

set_option autoImplicit false

noncomputable section

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.OrderedBayes.BayesRatioCore
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels

open scoped ENNReal NNReal BigOperators Classical
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution

def GeneralizedMarkovContract : Prop :=
  ∀ (α : Type) (μ : PMF α) (X : α → ℝ) (a b β c : ℝ),
    (∀ x, 0 ≤ X x) →
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation μ (fun x => ENNReal.ofReal (X x)) ≤ ENNReal.ofReal a →
    0 ≤ β → β ≤ 1 → 0 ≤ b → b ≤ a →
    ENNReal.ofReal (1 - β) ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event μ (fun x => b ≤ X x) →
    a < c →
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event μ (fun x => c < X x) ≤ ENNReal.ofReal ((a - b + β * b) / (c - b))

noncomputable def bayesTrueLikelihood {n : ℕ} (c m : Fin n) (p : ℝ) : ℝ :=
  if (c : ℕ) ≤ (m : ℕ) then p else 1 - p

noncomputable def bayesFalseLikelihood {n : ℕ} (c m : Fin n) (p : ℝ) : ℝ :=
  if (c : ℕ) ≤ (m : ℕ) then 1 - p else p

noncomputable def bayesTrueNorm {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (p : ℝ) : ℝ :=
  ∑ m, a m * bayesTrueLikelihood c m p

noncomputable def bayesFalseNorm {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (p : ℝ) : ℝ :=
  ∑ m, a m * bayesFalseLikelihood c m p

noncomputable def bayesTruePost {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (p : ℝ) : Fin n → ℝ :=
  fun m => a m * bayesTrueLikelihood c m p / bayesTrueNorm a c p

noncomputable def bayesFalsePost {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (p : ℝ) : Fin n → ℝ :=
  fun m => a m * bayesFalseLikelihood c m p / bayesFalseNorm a c p

def EqualCutBayesTransportContract : Prop :=
  (∀ (n : ℕ) (a : Fin n → ℝ) (c : Fin n) (p : ℝ),
      0 ≤ p → p ≤ 1 →
      (∀ m, 0 ≤ a m) → (∑ m, a m) = 1 →
      (∀ m, 0 < a m) →
      0 < bayesTrueNorm a c p ∧ 0 < bayesFalseNorm a c p ∧
        (∑ m, bayesTruePost a c p m) = 1 ∧ (∑ m, bayesFalsePost a c p m) = 1 ∧
        (∀ m, bayesTrueNorm a c p * bayesTruePost a c p m
            = a m * bayesTrueLikelihood c m p) ∧
        (∀ m, bayesFalseNorm a c p * bayesFalsePost a c p m
            = a m * bayesFalseLikelihood c m p))
  ∧
  (∃ (n : ℕ) (a : Fin n → ℝ) (c : Fin n) (p : ℝ),
      1 / 2 < p ∧ p < 1 ∧ (∀ m, 0 < a m) ∧ (∑ m, a m) = 1 ∧
        (updateTrue a c p ≠ bayesTruePost a c p ∨
          updateFalse a c p ≠ bayesFalsePost a c p))

def LearnerCutBridgeContract : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (a : Fin n → ℝ) (p ε : ℝ),
    1 / 2 < p → p < 1 → 0 < ε →
    ε ≤ Real.sqrt (1 / (24 * (Real.log n / Real.log 2))) →
    (∀ m, 0 < a m) → (∑ m, a m) = 1 →
    (¬ ∃ m, ε ≤ a m) →
    (cutSet a ε).Nonempty ∧
      (1 / 2 - ε ≤ prefixMass a (stageTwoCut (n := n) (lt_of_lt_of_le zero_lt_two hn) a ε) ∧
        prefixMass a (stageTwoCut (n := n) (lt_of_lt_of_le zero_lt_two hn) a ε) < 1 / 2) ∧
      (∑ m, updateTrue a (stageTwoCut (n := n) (lt_of_lt_of_le zero_lt_two hn) a ε) p m) = 1 ∧
      (∑ m, updateFalse a (stageTwoCut (n := n) (lt_of_lt_of_le zero_lt_two hn) a ε) p m) = 1

def Lemma2_3SharpContract : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℝ) (i : Fin n) (p ε : ℝ),
    2 ≤ n → 1 / 2 < p → p < 1 → 0 < ε →
    ε ≤ Real.sqrt (1 / (24 * (Real.log n / Real.log 2))) →
    (∀ j, 0 ≤ a j) → (∑ j, a j) = 1 →
    1 / 2 - ε ≤ prefixMass a i → prefixMass a i < 1 / 2 →
    queryInfo p - 4 * ε ^ 2 * (1 - 2 * p) ^ 2 ≤
      normFalse a i p * (postInfo (updateFalse a i p) - postInfo a) +
        normTrue a i p * (postInfo (updateTrue a i p) - postInfo a)

noncomputable def tickCosted {S A : Type*} (next : S → CostedLaw (Configuration S A)) :
    Configuration S A → CostedLaw (Configuration S A)
  | .inl out => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (.inl out)
  | .inr s => next s

noncomputable def runCostedFor {S A : Type*} (next : S → CostedLaw (Configuration S A)) :
    ℕ → Configuration S A → CostedLaw (Configuration S A)
  | 0, cfg => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret cfg
  | fuel + 1, cfg => Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.bind (tickCosted next cfg) (runCostedFor next fuel)

noncomputable def truthStepCosted {n : ℕ} (hn : 0 < n) (j : Fin n) (p ε : ℝ) :
    (Fin n → ℝ) → CostedLaw (Configuration (Fin n → ℝ) (Fin n → ℝ)) :=
  fun a =>
    if _h : ∃ i : Fin n, ε ≤ a i then Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (Sum.inl a)
    else
      (PMF.bernoulli (truthAnswerProb j (stageTwoCut hn a ε) p) (clampProb_le _)).map
        fun b =>
          ((Sum.inr (if b then updateTrue a (stageTwoCut hn a ε) p
            else updateFalse a (stageTwoCut hn a ε) p)), 1)

def RecursiveRecoveryCostContract : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n) (j : Fin n) (p ε δ : ℝ),
    1 / 2 < p → p < 1 → 0 < δ → δ < 1 → 0 < ε →
    ε ≤ Real.sqrt (1 / (24 * (Real.log n / Real.log 2))) →
    1 / n < ε →
    0 < queryInfo p →
    let hnn : 0 < n := lt_of_lt_of_le zero_lt_two hn
    let a₀ := uniformPosterior (n := n)
    let L := Real.log n / Real.log 2
    let run := runCostedFor (S := Fin n → ℝ) (A := Fin n → ℝ) (truthStepCosted hnn j p ε)
    (∀ fuel : ℕ,
      ENNReal.ofReal (1 - δ) ≤
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (run fuel (Sum.inr a₀))
          (fun cfg => ∃ a : Fin n → ℝ, cfg.1 = Sum.inl a ∧ haltCut hnn a ε = j)) ∧
    (∀ fuel : ℕ,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (run fuel (Sum.inr a₀)) ≤
        ENNReal.ofReal (L / queryInfo p + L * (Real.log (1 / δ) / Real.log 2) / queryInfo p
          + 2 / (3 * queryInfo p)))

noncomputable def printedT26Bound (n : ℕ) (p τ : ℝ) : ℝ :=
  (Real.log n / Real.log 2 - Real.log (1 / (1 - τ)) / Real.log 2) / queryInfo p

noncomputable def oneComparison (truth : Bool) : CostedLaw Bool :=
  (PMF.bernoulli (3 / 4 : ℝ≥0) (by
    exact_mod_cast (show (3 : ℝ) / 4 ≤ 1 by norm_num))).bind fun correct =>
    PMF.pure ((if correct then truth else !truth), 1)

def ClassicalInfoLowerBoundContract : Prop :=
  (∀ (n : ℕ) (τ p : ℝ) (program : PMF (BoolQueryTree (Fin n) (Fin n))) (oracle : Fin n → Bool),
      2 ≤ n → 0 ≤ τ → τ < 1 / 2 → 1 / 2 < p → p < 1 →
      0 < queryInfo p →
      (∀ j : Fin n, ENNReal.ofReal (1 - τ) ≤
        Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb program (fun c => c ≤ j) (fun out => out = j)) →
      ENNReal.ofReal ((Real.log n / Real.log 2 - binEntropy τ
          - τ * (Real.log (n - 1) / Real.log 2)) / queryInfo p) ≤
        Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.ExpectedQueries program oracle)
  ∧
  (1 < printedT26Bound 2 (3 / 4) (1 / 4) ∧
    (∀ truth : Bool,
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (oneComparison truth) (fun x => x.1 = truth) = (3 / 4 : ℝ≥0∞) ∧
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (oneComparison truth) = 1))

def Corollary2_7Contract : Prop :=
  ∀ (n : ℕ) (τ : ℝ) (program : PMF (BoolQueryTree (Fin n) (Fin n))) (oracle : Fin n → Bool),
    2 ≤ n → 0 ≤ τ → τ < 1 / 2 →
    (∀ j : Fin n, ENNReal.ofReal (1 - τ) ≤
      Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.SuccessProb program (fun c => c ≤ j) (fun out => out = j)) →
    ENNReal.ofReal (Real.log n / Real.log 2 - Real.log (1 / (1 - τ)) / Real.log 2) ≤
      Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.ExpectedQueries program oracle ∧
    ENNReal.ofReal (1 - 2 * τ) ≤
      ∑' tree, program tree *
        if (Real.log n / Real.log 2 - 2 * Real.log (1 / (1 - τ)) / Real.log 2)
            ≤ (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run oracle tree).2 then 1 else 0

def Lemma2_9TailContract : Prop :=
  ∀ (n : ℕ) (p δ c₁ χ : ℝ) (X : Type) (μ : PMF X) (Q : X → ℝ),
    4 ≤ n → 1 / 2 < p → p < 1 → 0 < δ → δ < 1 → 0 < c₁ → 1 < χ →
    0 < queryInfo p →
    let L := Real.log n / Real.log 2
    let lgL := Real.log L / Real.log 2
    let a := L / queryInfo p + c₁ * lgL * (Real.log (1 / δ) / Real.log 2) / queryInfo p
    let b := L / queryInfo p - 2 * lgL / queryInfo p
    (∀ x, 0 ≤ Q x) →
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation μ (fun x => ENNReal.ofReal (Q x)) ≤ ENNReal.ofReal a →
    ENNReal.ofReal (1 - 2 / L) ≤ Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event μ (fun x => b ≤ Q x) →
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event μ
        (fun x => L / queryInfo p + χ * (c₁ + 2) * lgL / queryInfo p < Q x) ≤
      ENNReal.ofReal (1 / χ)

noncomputable def multiInfo {k : ℕ} (p : Fin (k + 1) → ℝ) : ℝ :=
  Real.log (k + 1) / Real.log 2 - (∑ h, -(p h * (Real.log (p h) / Real.log 2)))

noncomputable def cyclicLikelihood {k : ℕ} (p : Fin (k + 1) → ℝ)
    (iv h : Fin (k + 1)) : ℝ := p (h - iv)

def intervalOf {k n : ℕ} (cuts : Fin k → Fin n) (m : Fin n) : Fin (k + 1) :=
  ⟨(Finset.univ.filter fun i : Fin k => (cuts i).val ≤ m.val).card, by
    have h1 := Finset.card_filter_le (s := (Finset.univ : Finset (Fin k)))
      (p := fun i : Fin k => (cuts i).val ≤ m.val)
    have h2 : (Finset.univ : Finset (Fin k)).card = k := Finset.card_fin _
    omega⟩

noncomputable def generalizedUpdate {k n : ℕ} (p : Fin (k + 1) → ℝ) (cuts : Fin k → Fin n)
    (a : Fin n → ℝ) (h : Fin (k + 1)) : Fin n → ℝ :=
  fun m =>
    a m * cyclicLikelihood p (intervalOf cuts m) h /
      (∑ m', a m' * cyclicLikelihood p (intervalOf cuts m') h)

noncomputable def cyclicAnswerPMF {k : ℕ} (p : Fin (k + 1) → ℝ) (iv : Fin (k + 1))
    (hp : ∀ h, 0 ≤ p h) (hs : ∑ h, p h = 1) : PMF (Fin (k + 1)) :=
  PMF.ofFintype (fun h => ENNReal.ofReal (cyclicLikelihood p iv h))
    (by
      have hnn : ∀ h, 0 ≤ p (h - iv) := fun h => hp _
      calc ∑ h, ENNReal.ofReal (cyclicLikelihood p iv h)
          = ∑ h, ENNReal.ofReal (p (h - iv)) :=
            Finset.sum_congr rfl (fun h _ => rfl)
        _ = ENNReal.ofReal (∑ h, p (h - iv)) :=
          (ENNReal.ofReal_sum_of_nonneg (fun h _ => hnn h)).symm
        _ = ENNReal.ofReal (∑ h, p h) := by
          congr 1
          exact (Equiv.subRight iv).sum_comp p
        _ = ENNReal.ofReal 1 := by rw [hs]
        _ = 1 := ENNReal.ofReal_one)

noncomputable def generalizedStepCosted {k n : ℕ} (_hn : 0 < n) (j : Fin n)
    (p : Fin (k + 1) → ℝ) (cuts : Fin k → Fin n) (ε : ℝ)
    (hp : ∀ h, 0 ≤ p h) (hs : ∑ h, p h = 1) :
    (Fin n → ℝ) → CostedLaw (Configuration (Fin n → ℝ) (Fin n → ℝ)) :=
  fun a =>
    if _h : ∃ i : Fin n, ε ≤ a i then Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (Sum.inl a)
    else
      (cyclicAnswerPMF p (intervalOf cuts j) hp hs).bind fun h =>
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.charge 1
          (Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.ret (Sum.inr (generalizedUpdate p cuts a h)))

def Theorem2_10Contract : Prop :=
  ∀ (k n : ℕ) (p : Fin (k + 1) → ℝ) (δ : ℝ),
    1 ≤ k → 4 ≤ n → 0 < δ → δ < 1 →
    (hpos : ∀ h, 0 < p h) → (hsum : (∑ h, p h) = 1) →
    0 < multiInfo p →
    let ε := (1 / (k : ℝ)) * Real.sqrt (1 / (24 * (Real.log n / Real.log 2)))
    ∀ (hn : 0 < n) (j : Fin n) (a₀ : Fin n → ℝ) (cuts : Fin k → Fin n),
      (∀ m, 0 < a₀ m) → (∑ m, a₀ m) = 1 → (∀ m, a₀ m < ε) →
      (∀ i i' : Fin k, i < i' → (cuts i).val < (cuts i').val) →
      let L := Real.log n / Real.log 2
      let run := runCostedFor (S := Fin n → ℝ) (A := Fin n → ℝ)
        (generalizedStepCosted hn j p cuts ε (fun h => le_of_lt (hpos h)) hsum)
      (∀ fuel : ℕ,
        ENNReal.ofReal (1 - δ) ≤
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (run fuel (Sum.inr a₀))
            (fun cfg => ∃ a : Fin n → ℝ, cfg.1 = Sum.inl a ∧ haltCut hn a ε = j)) ∧
      (∀ fuel : ℕ,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (run fuel (Sum.inr a₀)) ≤
          ENNReal.ofReal (L / multiInfo p
            + L * (Real.log (1 / δ) / Real.log 2) / multiInfo p + 2 / (3 * multiInfo p)))

end Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels.OrderedSearch2007

open scoped ENNReal NNReal BigOperators Classical
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution

noncomputable def noisyOracle {n : ℕ} (f : Fin n → Bool) (p : ℝ) :
    Matrix (Fin n × Bool) (Fin n × Bool) ℂ :=
  fun b a =>
    if b.1 = a.1 then
      if b.2 = (a.2 != f a.1) then (Real.sqrt p : ℂ)
      else if b.2 = !(a.2 != f a.1) then (Real.sqrt (1 - p) : ℂ)
      else 0
    else 0

noncomputable def printedOracle : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = j then (4 : ℂ) / 5 else 3 / 5

def NoisyQuantumOracleContract : Prop :=
  (∀ (n : ℕ) (f : Fin n → Bool) (p : ℝ), 0 ≤ p → p ≤ 1 →
      noisyOracle f p ∈ Matrix.unitaryGroup (Fin n × Bool) ℂ) ∧
  (∀ (n : ℕ) (f : Fin n → Bool) (p : ℝ) (x : Fin n) (c : Bool),
      0 ≤ p → p ≤ 1 →
      noisyOracle f p (x, c != f x) (x, c) = (Real.sqrt p : ℂ) ∧
        noisyOracle f p (x, !(c != f x)) (x, c) = (Real.sqrt (1 - p) : ℂ)) ∧
  (printedOracle.conjTranspose * printedOracle ≠ 1)

def Theorem4_2_4_3Contract : Prop :=
  ∀ (k : ℕ) (δ : ℝ),
    2 ≤ k → 0 ≤ δ → δ ≤ (k - 1) / (k : ℝ) →
    let Hδ := binEntropy δ
    (Real.log (Real.exp 1) / Real.pi) * ((1 - δ) * (Real.log k / Real.log 2) - Hδ) ≤
      (Real.log 2 / Real.pi) * ((1 - δ) * (Real.log k / Real.log 2) - Hδ)

noncomputable def fggsInfo : ℝ := 297 / 16

def FGGS99GreedyCertificateContract : Prop :=
  fggsInfo = 297 / 16 ∧
    (18 : ℝ) < fggsInfo ∧
    (6 : ℝ) / fggsInfo > 32 / 100 ∧
    (6 : ℝ) / fggsInfo < 1 / 3 ∧
    ∀ (Q : Fin (2 ^ 23) → ℝ),
      (∀ i, 0 < Q i) → (∑ i, Q i) = 1 →
      (∑ i, -(Q i * (Real.log (Q i) / Real.log 2))) ≤ (23 : ℝ) - fggsInfo

def Theorem1_1Contract : Prop :=
  (∀ (n : ℕ) (hn : 2 ≤ n) (j : Fin n) (p ε δ : ℝ),
      1 / 2 < p → p < 1 → 0 < δ → δ < 1 → 0 < ε →
      ε ≤ Real.sqrt (1 / (24 * (Real.log n / Real.log 2))) →
      1 / n < ε → 0 < queryInfo p →
      let hnn : 0 < n := lt_of_lt_of_le zero_lt_two hn
      let a₀ := uniformPosterior (n := n)
      let L := Real.log n / Real.log 2
      let run := runCostedFor (S := Fin n → ℝ) (A := Fin n → ℝ) (truthStepCosted hnn j p ε)
      (∀ fuel : ℕ,
        ENNReal.ofReal (1 - δ) ≤
          Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (run fuel (Sum.inr a₀))
            (fun cfg => ∃ a : Fin n → ℝ, cfg.1 = Sum.inl a ∧ haltCut hnn a ε = j)) ∧
      (∀ fuel : ℕ,
        Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (run fuel (Sum.inr a₀)) ≤
          ENNReal.ofReal (L / queryInfo p
            + L * (Real.log (1 / δ) / Real.log 2) / queryInfo p + 2 / (3 * queryInfo p))))
  ∧
  (∀ (n : ℕ) (δ : ℝ), 2 ≤ n → 0 < δ → δ < 1 →
      ¬ ((δ ≤ (Real.log n / Real.log 2) ^ 3) ∧ ¬ (δ ≥ (Real.log n / Real.log 2) ^ 3)))

end Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels.OrderedSearch2007
