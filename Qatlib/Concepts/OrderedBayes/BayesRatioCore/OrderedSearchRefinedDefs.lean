/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.OrderedSearch
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Refined noisy ordered-search models

This module defines finite transcript models for noisy ordered search and adaptive learning as
in [BenOrHassidim2007]. It separates the corrected cut posterior, explicit noisy-oracle
amplitudes, binary and cyclic answer laws, and the Fano capacity expressions used in query lower
bounds.

`BscStopProgram` records a prefix-determined stopping rule, while `RecBscProgram` organizes
several levels with a shared stopping rule. Padded transcript laws and entropy expressions
provide the finite probabilistic data for later stopping-cost and recursive information
estimates; entropy conventions follow [Wilde2017].

## Main statements

* `NoisyQueryBackend`: unitarity and answer-probability conditions for the noisy oracle.
* `FanoCapacityLowerBound`: the query-count inequality defined by the Fano capacity expression.
* `BscStopProgram`: adaptive binary queries with bounded stopping.
* `RecBscProgram`: recursive levels with a shared stopping rule and guesses determined by used
  answers.
* `recUsedJointLaw`: the joint weight function on hidden ranks and padded transcript towers.

## References

* [Ben-Or and Hassidim, 2007][BenOrHassidim2007]
* [Wilde, 2017][Wilde2017]
-/

set_option autoImplicit false

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

open scoped BigOperators Classical
open Qatlib.Concepts.OrderedBayes.BayesRatioCore
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels.OrderedSearch2007

/-- The Bayes posterior mass at the cut `c` after observing a true answer. -/
noncomputable def CorrectEqualCutPosterior {n : ℕ} (a : Fin n → ℝ) (c : Fin n)
    (p : ℝ) : ℝ :=
  bayesTruePost a c p c

/-- The proposition that the printed true-answer update and the Bayes posterior give different
masses at the cut. -/
def PrintedUpdateIsNotThePosterior {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (p : ℝ) : Prop :=
  updateTrue a c p c ≠ bayesTruePost a c p c

/-- The calibration condition requiring `0 < p < 1`, `δ > 0`, and a bound of `δ` on `treeCross`
at threshold `1 / δ` for every horizon. -/
def CrossPairCalibration {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u v : Fin n) (δ : ℝ) : Prop :=
  0 < p ∧ p < 1 ∧ 0 < δ ∧
    ∀ m : ℕ, treeCross hn p ε u v (1 / δ) m [] ≤ δ

/-- The Boolean ordered comparison `x.val ≤ rank.val`. -/
def truthBit {n : ℕ} (rank : Fin n) (x : Fin n) : Bool := decide (x.val ≤ rank.val)

/-- Encode a Boolean as an element of `Fin 2`, with false mapped to zero and true to one. -/
def boolIndex (b : Bool) : Fin 2 := if b then ⟨1, by decide⟩ else ⟨0, by decide⟩

/-- Decode an element of `Fin 2` as the Boolean test that its value is one. -/
def answerBit (a : Fin 2) : Bool := a.val = 1

/-- The two-dimensional complex matrix built from `√p` and `√(1 - p)` for the specified truth
bit. -/
noncomputable def noiseRotation (p : ℝ) (truth : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j =>
    if i.val = 0 then
      if j.val = 0 then (if truth then Real.sqrt (1 - p) else Real.sqrt p)
      else (if truth then Real.sqrt p else -(Real.sqrt (1 - p)))
    else
      if j.val = 0 then (if truth then Real.sqrt p else Real.sqrt (1 - p))
      else (if truth then -(Real.sqrt (1 - p)) else Real.sqrt p)

/-- The matrix preserving the query index and applying `noiseRotation` to the answer register
according to `truthBit`. -/
noncomputable def noisyQueryOracle {n : ℕ} (rank : Fin n) (p : ℝ) :
    Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ :=
  fun b a => if b.1 = a.1 then noiseRotation p (truthBit rank a.1) b.2 a.2 else 0

/-- The real amplitude `√p` for a correct answer and `√(1 - p)` for an incorrect answer. -/
noncomputable def noiseAmplitude (p : ℝ) (truth answer : Bool) : ℝ :=
  if answer = truth then Real.sqrt p else Real.sqrt (1 - p)

/-- The square of `noiseAmplitude` for the specified truth and answer bits. -/
noncomputable def noiseAnswerProb (p : ℝ) (truth answer : Bool) : ℝ :=
  (noiseAmplitude p truth answer) ^ 2

/-- Membership in the rational span of `1`, `√p`, `√(1 - p)`, and their product, embedded in the
complex numbers. -/
def InNoiseField (p : ℝ) (z : ℂ) : Prop :=
  ∃ a b c d : ℚ,
    z = ((a : ℝ) + (b : ℝ) * Real.sqrt p + (c : ℝ) * Real.sqrt (1 - p)
      + (d : ℝ) * (Real.sqrt p * Real.sqrt (1 - p)) : ℝ)

/-- The conjunction of the parameter range, unitarity of the noisy oracle, the prescribed answer
probabilities, and membership of all entries in `InNoiseField`. -/
def NoisyQueryBackend (n : ℕ) (rank : Fin n) (p : ℝ) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧
    noisyQueryOracle rank p ∈ Matrix.unitaryGroup (Fin n × Fin 2) ℂ ∧
    (∀ truth answer : Bool, noiseAnswerProb p truth answer =
      if answer = truth then p else 1 - p) ∧
    (∀ b a : Fin n × Fin 2, InNoiseField p (noisyQueryOracle rank p b a))

/-- The Fano expression `log₂ n - binEntropy δ - δ * log₂ (n - 1)`, with `n - 1` computed in the
natural numbers. -/
noncomputable def fanoNumerator (n : ℕ) (δ : ℝ) : ℝ :=
  Real.log (n : ℝ) / Real.log 2 - binEntropy δ
    - δ * (Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2)

/-- The quotient of `fanoNumerator n δ` by the per-query information `queryInfo p`. -/
noncomputable def fanoCapacityBound (n : ℕ) (p δ : ℝ) : ℝ :=
  fanoNumerator n δ / queryInfo p

/-- The conditions `2 ≤ n`, `1 / 2 < p ≤ 1`, `0 ≤ δ ≤ 1 - 1 / n`, and `queryInfo p > 0`,
together with the two binary calibration identities for `fanoCapacityBound`. -/
def FanoCapacityContract (n : ℕ) (p δ : ℝ) : Prop :=
  2 ≤ n ∧ 1 / 2 < p ∧ p ≤ 1 ∧ 0 ≤ δ ∧ δ ≤ 1 - 1 / (n : ℝ) ∧
    0 < queryInfo p ∧
    fanoCapacityBound 2 p (1 / 2) = 0 ∧
    (∀ p' : ℝ, 1 / 2 < p' → p' < 1 → fanoCapacityBound 2 p' p' = 1)

/-- The real-valued expression `x * log₂ x`. -/
noncomputable def xlog2 (x : ℝ) : ℝ := x * (Real.log x / Real.log 2)

/-- The base-two entropy expression `-∑ i, xlog2 (w i)` for a finite family of real weights. -/
noncomputable def entH {α : Type} [Fintype α] (w : α → ℝ) : ℝ := -∑ i, xlog2 (w i)

/-- The left marginal weight obtained by summing a joint weight function over its second
coordinate. -/
noncomputable def margL {α β : Type} [Fintype α] [Fintype β] (d : α × β → ℝ) : α → ℝ :=
  fun i => ∑ j, d (i, j)

/-- The right marginal weight obtained by summing a joint weight function over its first
coordinate. -/
noncomputable def margR {α β : Type} [Fintype α] [Fintype β] (d : α × β → ℝ) : β → ℝ :=
  fun j => ∑ i, d (i, j)

/-- The conditional weight `d (i, j) / margL d i`, defined to be zero when the left marginal
vanishes. -/
noncomputable def condW {α β : Type} [Fintype α] [Fintype β] (d : α × β → ℝ)
    (i : α) (j : β) : ℝ :=
  if _h : margL d i = 0 then 0 else d (i, j) / margL d i

/-- The conditional entropy expression for the second coordinate given the first, using `condW`
and logarithms to base two. -/
noncomputable def condEntH {α β : Type} [Fintype α] [Fintype β] (d : α × β → ℝ) : ℝ :=
  -∑ i, ∑ j, d (i, j) * (Real.log (condW d i j) / Real.log 2)

/-- The conditional entropy expression for the first coordinate given the second, obtained by
swapping the coordinates in `condEntH`. -/
noncomputable def condEntHR {α β : Type} [Fintype α] [Fintype β] (d : α × β → ℝ) : ℝ :=
  condEntH (fun p => d (p.2, p.1))

/-- The mutual information expression given by the entropy of the left marginal minus
`condEntHR`. -/
noncomputable def mutInfo {α β : Type} [Fintype α] [Fintype β] (d : α × β → ℝ) : ℝ :=
  entH (margL d) - condEntHR d

/-- The binary symmetric channel weight `p` for a correct answer and `1 - p` for an incorrect
answer. -/
noncomputable def bscProb (p : ℝ) (truth answer : Bool) : ℝ :=
  if answer = truth then p else 1 - p

/-- An adaptive binary-query program with `k` cuts chosen from preceding answers and a final
guess in `Fin n`. -/
structure BscProgram (n k : ℕ) where
  cuts : ∀ i : Fin k, (Fin i.val → Bool) → Fin n
  guess : (Fin k → Bool) → Fin n

/-- The restriction of an answer transcript to the positions strictly before `i`. -/
def answerPrefix {k : ℕ} (y : Fin k → Bool) (i : Fin k) : Fin i.val → Bool :=
  fun j => y (Fin.castLE (Nat.le_of_lt i.isLt) j)

/-- The product of binary symmetric channel weights along an adaptive program's transcript for
the hidden rank `x`. -/
noncomputable def bscLik {n k : ℕ} (prog : BscProgram n k) (p : ℝ) (x : Fin n)
    (y : Fin k → Bool) : ℝ :=
  ∏ i, bscProb p (truthBit x (prog.cuts i (answerPrefix y i))) (y i)

/-- The joint weight of a hidden rank and transcript, obtained from `bscLik` with the uniform
prior factor `1 / n`. -/
noncomputable def bscJoint {n k : ℕ} (prog : BscProgram n k) (p : ℝ)
    (x : Fin n) (y : Fin k → Bool) : ℝ :=
  (1 / (n : ℝ)) * bscLik prog p x y

/-- The Boolean indicator that the program's guess on the transcript differs from the hidden
rank. -/
def bscError {n k : ℕ} (prog : BscProgram n k) (x : Fin n) (y : Fin k → Bool) : Bool :=
  decide (prog.guess y ≠ x)

/-- The sum of `bscJoint` over the hidden ranks and transcripts on which the program guesses
incorrectly. -/
noncomputable def bscErrorProb {n k : ℕ} (prog : BscProgram n k) (p : ℝ) : ℝ :=
  ∑ x, ∑ y, bscJoint prog p x y * (if bscError prog x y then 1 else 0)

/-- The proposition that the number of queries `k` is at least `fanoCapacityBound n p δ`. -/
def FanoCapacityLowerBound (n k : ℕ) (p δ : ℝ) : Prop :=
  (k : ℝ) ≥ fanoCapacityBound n p δ

/-- Remove the last entry of a finite transcript. -/
def tPre {m : ℕ} {α : Type} (y : Fin (m + 1) → α) : Fin m → α := fun j => y (j.castSucc)

/-- The last entry of a transcript indexed by `Fin (m + 1)`. -/
def tLast {m : ℕ} {α : Type} (y : Fin (m + 1) → α) : α := y (Fin.last m)

/-- Extend a transcript by appending the entry `b` at its last position. -/
def tExt {m : ℕ} {α : Type} (pfx : Fin m → α) (b : α) : Fin (m + 1) → α :=
  fun i => if h : i.val = m then b else pfx ⟨i.val, by omega⟩

/-- Restrict a transcript to the positions strictly preceding `j`. -/
def tRestrict {k : ℕ} {α : Type} (y : Fin k → α) (j : Fin k) : Fin j.val → α :=
  fun l => y ⟨l.val, by omega⟩

/-- The equivalence between a transcript paired with one additional entry and the transcript
formed by appending that entry. -/
def tSplitEquiv {m : ℕ} {α : Type} : (Fin m → α) × α ≃ (Fin (m + 1) → α) where
  toFun p := tExt p.1 p.2
  invFun y := (tPre y, tLast y)
  left_inv p := by
    obtain ⟨pfx, b⟩ := p
    apply Prod.ext
    · change (fun j => tPre (tExt pfx b) j) = pfx
      funext j
      simp only [tPre]
      have hcast : j.castSucc = ⟨j.val, by omega⟩ := by
        apply Fin.ext
        rfl
      rw [hcast]
      have hne : (⟨j.val, by omega⟩ : Fin m).val ≠ m := by
        simpa using Nat.ne_of_lt j.isLt
      simp [tExt, hne]
    · change tLast (tExt pfx b) = b
      simp [tLast, tExt]
  right_inv y := by
    funext i
    by_cases hi : i.val = m
    · have hlast : i = Fin.last m := by
        apply Fin.ext
        simpa [Fin.last] using hi
      simp [tExt, tLast, hlast]
    · simp only [tExt, hi]
      have hcast : (⟨i.val, by omega⟩ : Fin m).castSucc = i := by
        apply Fin.ext
        simp
      simp [tPre, hcast]

/-- The product of binary symmetric channel weights for a cut family and a finite answer prefix
at hidden rank `x`. -/
noncomputable def bscLikPre {n m : ℕ} (cuts : ∀ i : Fin m, (Fin i.val → Bool) → Fin n)
    (p : ℝ) (x : Fin n) (pfx : Fin m → Bool) : ℝ :=
  ∏ j, bscProb p (truthBit x (cuts j (tRestrict pfx j))) (pfx j)

/-- The joint rank-transcript weight for a cut family, with uniform rank factor `1 / n`. -/
noncomputable def bscJointCuts {n m : ℕ} (cuts : ∀ i : Fin m, (Fin i.val → Bool) → Fin n)
    (p : ℝ) (x : Fin n) (y : Fin m → Bool) : ℝ :=
  (1 / (n : ℝ)) * bscLikPre cuts p x y

/-- The binary symmetric channel weight of the next answer after the given prefix, using the
last cut of the cut family. -/
noncomputable def bscStepCond {n m : ℕ} (cuts : ∀ i : Fin (m + 1), (Fin i.val → Bool) → Fin n)
    (p : ℝ) (x : Fin n) (pfx : Fin m → Bool) (b : Bool) : ℝ :=
  bscProb p (truthBit x (cuts (Fin.last m) pfx)) b

/-- The equivalence splitting a rank-transcript pair into the rank, the transcript prefix, and
its final entry. -/
def tSplitLawEquiv {n m : ℕ} {α : Type} :
    (Fin n × (Fin (m + 1) → α)) ≃ ((Fin n × (Fin m → α)) × α) where
  toFun z := ((z.1, tPre z.2), tLast z.2)
  invFun z := (z.1.1, tExt z.1.2 z.2)
  left_inv z := by
    obtain ⟨x, y⟩ := z
    apply Prod.ext
    · rfl
    · funext i
      by_cases hi : i.val = m
      · have hlast : i = Fin.last m := by
          apply Fin.ext
          simpa [Fin.last] using hi
        simp [tExt, tLast, hlast]
      · simp only [tExt, hi]
        have hcast : (⟨i.val, by omega⟩ : Fin m).castSucc = i := by
          apply Fin.ext
          simp
        simp [tPre, hcast]
  right_inv z := by
    obtain ⟨⟨x, pfx⟩, b⟩ := z
    apply Prod.ext
    · apply Prod.ext
      · rfl
      · funext j
        simp only [tPre]
        have hcast : j.castSucc = ⟨j.val, by omega⟩ := by
          apply Fin.ext
          rfl
        rw [hcast]
        have hne : (⟨j.val, by omega⟩ : Fin m).val ≠ m := by
          simpa using Nat.ne_of_lt j.isLt
        simp [tExt, hne]
    · simp [tLast, tExt]

/-- Restrict an adaptive family of `m + 1` cuts to its first `m` cuts. -/
def cutsPre {n m : ℕ} (cuts : ∀ i : Fin (m + 1), (Fin i.val → Bool) → Fin n) :
    ∀ j : Fin m, (Fin j.val → Bool) → Fin n :=
  fun j => cuts (j.castSucc)

/-- The joint weight function on hidden ranks and binary transcripts associated with a cut
family and uniform rank weights. -/
noncomputable def bscJointLaw {n m : ℕ}
    (cuts : ∀ i : Fin m, (Fin i.val → Bool) → Fin n) (p : ℝ) : Fin n × (Fin m → Bool) → ℝ :=
  fun z => bscJointCuts cuts p z.1 z.2

/-- The mutual information expression of the joint weight function `bscJointLaw`. -/
noncomputable def bscMutInfo {n m : ℕ}
    (cuts : ∀ i : Fin m, (Fin i.val → Bool) → Fin n) (p : ℝ) : ℝ :=
  mutInfo (bscJointLaw cuts p)

/-- The proposition that rank-transcript mutual information is at most the number of queries
times `queryInfo p`. -/
def BscQueryInfoBound {n m : ℕ}
    (cuts : ∀ i : Fin m, (Fin i.val → Bool) → Fin n) (p : ℝ) : Prop :=
  bscMutInfo cuts p ≤ (m : ℝ) * queryInfo p

/-- The condition `0 ≤ δ ≤ 1 / 2` on the error parameter. -/
def FanoCapacityLegalDelta (δ : ℝ) : Prop :=
  0 ≤ δ ∧ δ ≤ 1 / 2

/-- The implication from a legal error parameter and the program's error bound to the Fano
capacity lower bound on its query count. -/
def SameRunComparisonBound {n k : ℕ} (prog : BscProgram n k) (p δ : ℝ) : Prop :=
  FanoCapacityLegalDelta δ → bscErrorProb prog p ≤ δ → (k : ℝ) ≥ fanoCapacityBound n p δ

/-- The proposition that `fanoCapacityBound n p δ` is nonpositive whenever `n ≤ 1`. -/
def FanoCapacitySmallN (n : ℕ) (p δ : ℝ) : Prop :=
  n ≤ 1 → fanoCapacityBound n p δ ≤ 0

/-- The cyclic channel weight `p (h - s)` for signal `s` and answer `h` in `Fin (k + 1)`. -/
noncomputable def cycProb {k : ℕ} (p : Fin (k + 1) → ℝ) (s h : Fin (k + 1)) : ℝ :=
  p (h - s)

/-- An adaptive program with cyclic-valued signals and answers, together with a final guess of
the hidden rank. -/
structure CycProgram (n m k : ℕ) where
  sig : ∀ i : Fin m, (Fin i.val → Fin (k + 1)) → Fin n → Fin (k + 1)
  guess : (Fin m → Fin (k + 1)) → Fin n

/-- The product of cyclic channel weights along an adaptive signal family's transcript at hidden
rank `x`. -/
noncomputable def cycLikCuts {n m k : ℕ}
    (sig : ∀ i : Fin m, (Fin i.val → Fin (k + 1)) → Fin n → Fin (k + 1))
    (p : Fin (k + 1) → ℝ) (x : Fin n) (y : Fin m → Fin (k + 1)) : ℝ :=
  ∏ i, cycProb p (sig i (tRestrict y i) x) (y i)

/-- The joint rank-transcript weight formed from `cycLikCuts` with the uniform rank factor `1 /
n`. -/
noncomputable def cycJointCuts {n m k : ℕ}
    (sig : ∀ i : Fin m, (Fin i.val → Fin (k + 1)) → Fin n → Fin (k + 1))
    (p : Fin (k + 1) → ℝ) (x : Fin n) (y : Fin m → Fin (k + 1)) : ℝ :=
  (1 / (n : ℝ)) * cycLikCuts sig p x y

/-- The joint weight function on hidden ranks and cyclic-valued transcripts for an adaptive
signal family. -/
noncomputable def cycJointLaw {n m k : ℕ}
    (sig : ∀ i : Fin m, (Fin i.val → Fin (k + 1)) → Fin n → Fin (k + 1))
    (p : Fin (k + 1) → ℝ) : Fin n × (Fin m → Fin (k + 1)) → ℝ :=
  fun z => cycJointCuts sig p z.1 z.2

/-- The Boolean indicator that the cyclic program's guess differs from the hidden rank. -/
def cycError {n m k : ℕ} (prog : CycProgram n m k) (x : Fin n)
    (y : Fin m → Fin (k + 1)) : Bool :=
  decide (prog.guess y ≠ x)

/-- The total joint weight of rank-transcript pairs for which the cyclic program guesses
incorrectly. -/
noncomputable def cycErrorProb {n m k : ℕ} (prog : CycProgram n m k)
    (p : Fin (k + 1) → ℝ) : ℝ :=
  ∑ x, ∑ y, cycJointLaw prog.sig p (x, y) * (if cycError prog x y then 1 else 0)

/-- The mutual information expression associated with the cyclic joint weight function of a
signal family. -/
noncomputable def cycSigMutInfo {n m k : ℕ}
    (sig : ∀ i : Fin m, (Fin i.val → Fin (k + 1)) → Fin n → Fin (k + 1))
    (p : Fin (k + 1) → ℝ) : ℝ :=
  mutInfo (cycJointLaw sig p)

/-- The rank-transcript mutual information expression for a cyclic program. -/
noncomputable def cycMutInfo {n m k : ℕ} (prog : CycProgram n m k)
    (p : Fin (k + 1) → ℝ) : ℝ :=
  cycSigMutInfo prog.sig p

/-- The quotient of `fanoNumerator n δ` by the cyclic channel information expression `multiInfo
p`. -/
noncomputable def cycCapacityBound (n : ℕ) (k : ℕ) (p : Fin (k + 1) → ℝ) (δ : ℝ) : ℝ :=
  fanoNumerator n δ / multiInfo p

/-- The proposition that the cyclic program's mutual information is at most its query count
times `multiInfo p`. -/
def CycQueryInfoBound {n m k : ℕ} (prog : CycProgram n m k) (p : Fin (k + 1) → ℝ) : Prop :=
  cycMutInfo prog p ≤ (m : ℝ) * multiInfo p

/-- The implication from a legal error parameter and the cyclic program's error bound to its
capacity lower bound on the query count. -/
def CycSameRunBound {n m k : ℕ} (prog : CycProgram n m k) (p : Fin (k + 1) → ℝ)
    (δ : ℝ) : Prop :=
  FanoCapacityLegalDelta δ → cycErrorProb prog p ≤ δ →
    (m : ℝ) ≥ cycCapacityBound n k p δ

/-- The squared complex norm of the amplitude indexed by the Boolean outcome `b`. -/
noncomputable def bornProb (v : Fin 2 → ℂ) (b : Bool) : ℝ :=
  (v (boolIndex b)).normSq

/-- The answer-register vector with amplitude one at zero and zero at one. -/
noncomputable def answerReset : Fin 2 → ℂ :=
  fun i => if i.val = 0 then 1 else 0

/-- The answer-register amplitudes obtained from the noisy oracle at query index `x` with the
input answer register set to zero. -/
noncomputable def qStepState {n : ℕ} (rank : Fin n) (p : ℝ) (x : Fin n) : Fin 2 → ℂ :=
  fun b => noisyQueryOracle rank p (x, boolIndex (answerBit b)) (x, ⟨0, by decide⟩)

/-- The Born weight of outcome `b` in the answer-register state `qStepState`. -/
noncomputable def qStepProb {n : ℕ} (rank : Fin n) (p : ℝ) (x : Fin n) (b : Bool) : ℝ :=
  bornProb (qStepState rank p x) b

/-- An adaptive program that chooses each query index from earlier binary answers and returns a
rank guess after `q` queries. -/
structure QuantumQueryProgram (n q : ℕ) where
  cuts : ∀ i : Fin q, (Fin i.val → Bool) → Fin n
  guess : (Fin q → Bool) → Fin n

/-- View a `QuantumQueryProgram` as a binary symmetric channel program with the same cuts and
guess. -/
def toBscProg {n q : ℕ} (prog : QuantumQueryProgram n q) : BscProgram n q where
  cuts := prog.cuts
  guess := prog.guess

/-- The product of the one-query Born weights along a quantum query program's answer transcript. -/
noncomputable def qLik {n q : ℕ} (prog : QuantumQueryProgram n q) (p : ℝ) (rank : Fin n)
    (y : Fin q → Bool) : ℝ :=
  ∏ i, qStepProb rank p (prog.cuts i (answerPrefix y i)) (y i)

/-- The joint hidden-rank and transcript weight obtained from `qLik` with the uniform rank
factor `1 / n`. -/
noncomputable def qJoint {n q : ℕ} (prog : QuantumQueryProgram n q) (p : ℝ)
    (rank : Fin n) (y : Fin q → Bool) : ℝ :=
  (1 / (n : ℝ)) * qLik prog p rank y

/-- The Boolean indicator that the quantum query program's final guess differs from the hidden
rank. -/
def qError {n q : ℕ} (prog : QuantumQueryProgram n q) (rank : Fin n)
    (y : Fin q → Bool) : Bool :=
  decide (prog.guess y ≠ rank)

/-- The sum of `qJoint` over rank-transcript pairs with an incorrect final guess. -/
noncomputable def qErrorProb {n q : ℕ} (prog : QuantumQueryProgram n q) (p : ℝ) : ℝ :=
  ∑ rank, ∑ y, qJoint prog p rank y * (if qError prog rank y then 1 else 0)

/-- The parameter, unitarity, and normalization conditions identifying the one-query Born
probabilities with the corresponding binary symmetric channel probabilities. -/
def QuantumQueryBackend (n : ℕ) (p : ℝ) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧
    (∀ rank : Fin n, noisyQueryOracle rank p ∈ Matrix.unitaryGroup (Fin n × Fin 2) ℂ) ∧
    (∀ rank : Fin n, ∀ x : Fin n, ∀ b : Bool,
      qStepProb rank p x b = bscProb p (truthBit rank x) b) ∧
    (∀ rank : Fin n, ∀ x : Fin n, ∑ b, qStepProb rank p x b = 1)

/-- The proposition that the quantum query count `q` is at least `fanoCapacityBound n p δ`. -/
def QuantumQueryLowerBound (n q : ℕ) (p δ : ℝ) : Prop :=
  (q : ℝ) ≥ fanoCapacityBound n p δ

/-- An adaptive binary-query program with a bounded stopping rule determined by the answers
preceding its stopping time, and a transcript-dependent final guess. -/
structure BscStopProgram (n k : ℕ) where
  cuts : ∀ i : Fin k, (Fin i.val → Bool) → Fin n
  stop : (Fin k → Bool) → Fin (k + 1)
  guess : (Fin k → Bool) → Fin n

  prefixDetermined : ∀ y : Fin k → Bool, ∀ y' : Fin k → Bool,
    (∀ j : Fin k, j.val < (stop y).val → y j = y' j) → stop y = stop y'

/-- Forget the stopping rule of a `BscStopProgram`, retaining its cuts and final guess. -/
def stopToBscProg {n k : ℕ} (prog : BscStopProgram n k) : BscProgram n k where
  cuts := prog.cuts
  guess := prog.guess

/-- The stopping time of a transcript, regarded as a real number. -/
noncomputable def stopCost {n k : ℕ} (prog : BscStopProgram n k) (y : Fin k → Bool) : ℝ :=
  (prog.stop y).val

/-- The transcript marginal weight obtained by summing `bscJoint` over all hidden ranks. -/
noncomputable def bscTransMarginal {n k : ℕ} (prog : BscProgram n k) (p : ℝ)
    (y : Fin k → Bool) : ℝ :=
  ∑ x, bscJoint prog p x y

/-- The stopping cost weighted by the transcript marginal and summed over all transcripts. -/
noncomputable def expectedStopCost {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ) : ℝ :=
  ∑ y, bscTransMarginal (stopToBscProg prog) p y * stopCost prog y

/-- The total joint weight of rank-transcript pairs for which the stopped program's final guess
is incorrect. -/
noncomputable def stopErrorProb {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ) : ℝ :=
  ∑ x, ∑ y, bscJoint (stopToBscProg prog) p x y * (if prog.guess y ≠ x then 1 else 0)

/-- The real-valued indicator that the stopping cost is at least the threshold `t`. -/
noncomputable def stopCostTail {n k : ℕ} (prog : BscStopProgram n k) (t : ℝ)
    (y : Fin k → Bool) : ℝ :=
  if stopCost prog y ≥ t then 1 else 0

/-- The transcript marginal weight of the event that the stopping cost is at least `t`. -/
noncomputable def stopTailProb {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (t : ℝ) : ℝ :=
  ∑ y, bscTransMarginal (stopToBscProg prog) p y * stopCostTail prog t y

/-- Restrict a binary transcript to its first `i` entries, using the bound `i ≤ k`. -/
def stopPrefix {k : ℕ} (i : ℕ) (hk : i ≤ k) (y : Fin k → Bool) : Fin i → Bool :=
  fun j => y ⟨j.val, lt_of_lt_of_le j.isLt hk⟩

/-- Extend a binary prefix to length `k`, filling positions outside the prefix with false. -/
def stopExt {k : ℕ} (i : ℕ) (pfx : Fin i → Bool) : Fin k → Bool :=
  fun j => if h : j.val < i then pfx ⟨j.val, h⟩ else false

/-- The condition that the stopping rule evaluated on the false-filled prefix extension is
strictly greater than the prefix length. -/
def stopAlive {n k : ℕ} (prog : BscStopProgram n k) (i : ℕ) (pfx : Fin i → Bool) : Prop :=
  (prog.stop (stopExt i pfx)).val > i

/-- The total transcript weight of prefixes satisfying `stopAlive` at time `i`. -/
noncomputable def stopAliveProb {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (i : ℕ) (hk : i ≤ k) : ℝ :=
  ∑ y : Fin k → Bool, bscTransMarginal (stopToBscProg prog) p y
    * (if stopAlive prog i (stopPrefix i hk y) then 1 else 0)

/-- The family of survival weights `stopAliveProb` indexed by the times from zero through `k`. -/
noncomputable def stopSurvivalProfile {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ) :
    Fin (k + 1) → ℝ :=
  fun i => stopAliveProb prog p i.val (by omega)

/-- The identity equating expected stopping cost with the sum of the survival profile. -/
def StopSurvivalContract {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ) : Prop :=
  expectedStopCost prog p = ∑ i, stopSurvivalProfile prog p i

/-- Keep the binary answers strictly before the stopping time and replace the remaining entries
by the unit marker. -/
def stopPad {n k : ℕ} (prog : BscStopProgram n k) (y : Fin k → Bool) : Fin k → (Sum Bool Unit) :=
  fun i => if i.val < (prog.stop y).val then Sum.inl (y i) else Sum.inr ()

/-- Decode a padded transcript by retaining binary answers and replacing unit markers with
false. -/
def stopPadDecode {k : ℕ} (e : Fin k → (Sum Bool Unit)) : Fin k → Bool :=
  fun i => match e i with
    | Sum.inl b => b
    | Sum.inr _ => false

/-- The joint rank and padded-transcript weight obtained by summing the full transcript weights
over the fibres of `stopPad`. -/
noncomputable def stopUsedJoint {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (x : Fin n) (e : Fin k → (Sum Bool Unit)) : ℝ :=
  ∑ y : Fin k → Bool, bscJointCuts prog.cuts p x y * (if stopPad prog y = e then 1 else 0)

/-- The joint weight function on hidden ranks and padded transcripts of a stopped program. -/
noncomputable def stopUsedJointLaw {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ) :
    Fin n × (Fin k → (Sum Bool Unit)) → ℝ :=
  fun z => stopUsedJoint prog p z.1 z.2

/-- The mutual information expression between the hidden rank and the padded transcript. -/
noncomputable def stopUsedMutInfo {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ) : ℝ :=
  mutInfo (stopUsedJointLaw prog p)

/-- Apply the program's guess function to the transcript obtained by replacing padding markers
with false. -/
def stopUsedGuess {n k : ℕ} (prog : BscStopProgram n k) (e : Fin k → (Sum Bool Unit)) : Fin n :=
  prog.guess (stopPadDecode e)

/-- The condition that transcripts with the same padded transcript have the same final guess. -/
def StopGuessFromUsed {n k : ℕ} (prog : BscStopProgram n k) : Prop :=
  ∀ y y' : Fin k → Bool, stopPad prog y = stopPad prog y' → prog.guess y = prog.guess y'

/-- Restrict a finite transcript to its first `i` entries using the bound `i ≤ k`. -/
def tPrefix {k : ℕ} (i : ℕ) (hk : i ≤ k) {α : Type} (y : Fin k → α) : Fin i → α :=
  fun j => y ⟨j.val, lt_of_lt_of_le j.isLt hk⟩

/-- Restrict an adaptive binary cut family to its first `i` query positions. -/
def cutsPrefix {n : ℕ} {k : ℕ} (i : ℕ)
    (cuts : ∀ j : Fin k, (Fin j.val → Bool) → Fin n) (hk : i ≤ k) :
    ∀ j : Fin i, (Fin j.val → Bool) → Fin n :=
  fun j => cuts ⟨j.val, lt_of_lt_of_le j.isLt hk⟩

/-- Sum a transcript weight function over all transcripts whose first `i` entries equal the
specified prefix. -/
noncomputable def sumOverPrefix {k i : ℕ} {α : Type} [Fintype α]
    [DecidableEq α] (g : (Fin k → α) → ℝ) (w : Fin i → α) (hk : i ≤ k) : ℝ :=
  ∑ y : Fin k → α, g y * (if tPrefix i hk y = w then 1 else 0)

/-- The joint weight of the hidden rank and a prefix of the padded transcript, obtained by
summing full transcript weights. -/
noncomputable def stopUsedPrefixLaw {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (i : ℕ) (hk : i ≤ k) : Fin n × (Fin i → (Sum Bool Unit)) → ℝ :=
  fun z => ∑ y : Fin k → Bool, bscJointCuts prog.cuts p z.1 y
    * (if tPrefix i hk (stopPad prog y) = z.2 then 1 else 0)

/-- The condition that every entry of a padded prefix is a binary answer rather than a unit
marker. -/
def padAllInl {i : ℕ} (pfx : Fin i → (Sum Bool Unit)) : Prop :=
  ∀ j : Fin i, ∃ b : Bool, pfx j = Sum.inl b

/-- The condition that a padded prefix contains only binary answers and its decoded prefix
satisfies `stopAlive`. -/
def padAlive {n k : ℕ} (prog : BscStopProgram n k) {i : ℕ}
    (pfx : Fin i → (Sum Bool Unit)) : Prop :=
  padAllInl pfx ∧ stopAlive prog i (stopPadDecode pfx)

/-- The joint weight function of a padded prefix and its next entry, with the hidden rank summed
out. -/
noncomputable def stopSlotMargLaw {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    {i : ℕ} (hi : i + 1 ≤ k) : (Fin i → (Sum Bool Unit)) × (Sum Bool Unit) → ℝ :=
  fun z => ∑ x, stopUsedPrefixLaw prog p (i + 1) hi (x, tExt z.1 z.2)

/-- The joint weight function of the hidden rank, a padded prefix, and its next entry. -/
noncomputable def stopSlotPostLaw {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    {i : ℕ} (hi : i + 1 ≤ k) :
    (Fin n × (Fin i → (Sum Bool Unit))) × (Sum Bool Unit) → ℝ :=
  fun z => stopUsedPrefixLaw prog p (i + 1) hi (z.1.1, tExt z.1.2 z.2)

/-- The total marginal weight of padded prefixes satisfying `padAlive`. -/
noncomputable def stopLiveMass {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    {i : ℕ} (hi : i ≤ k) : ℝ :=
  ∑ pfx : Fin i → (Sum Bool Unit),
    (if padAlive prog pfx then (∑ x, stopUsedPrefixLaw prog p i hi (x, pfx)) else 0)

/-- The difference between the next-slot conditional entropy given the padded prefix and that
given the rank and prefix; it is zero outside the query range. -/
noncomputable def stopSlotChainTerm {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (i : ℕ) : ℝ :=
  if h : i + 1 ≤ k then
    condEntH (stopSlotMargLaw prog p h) - condEntH (stopSlotPostLaw prog p h)
  else 0

/-- The condition that the finite query weights are nonnegative and sum to one. -/
def RecQueryProb {n : ℕ} (μ : Fin n → ℝ) : Prop :=
  (∀ c, 0 ≤ μ c) ∧ (∑ c, μ c = 1)

/-- The weight function equal to one at `c` and zero at every other query index. -/
def recPointMass {n : ℕ} (c : Fin n) : Fin n → ℝ :=
  fun d => if d = c then 1 else 0

/-- The binary symmetric channel answer weight averaged over the query weights `μ`. -/
noncomputable def recMixProb {n : ℕ} (μ : Fin n → ℝ) (p : ℝ) (x : Fin n)
    (b : Bool) : ℝ :=
  ∑ c, μ c * bscProb p (truthBit x c) b

/-- The total query weight of indices for which `truthBit x` is true. -/
noncomputable def recTrueMass {n : ℕ} (μ : Fin n → ℝ) (x : Fin n) : ℝ :=
  ∑ c, μ c * (if truthBit x c then 1 else 0)

/-- The mixed answer weight `recMixProb μ p x true`. -/
noncomputable def recMixTrue {n : ℕ} (μ : Fin n → ℝ) (p : ℝ) (x : Fin n) : ℝ :=
  recMixProb μ p x true

/-- The binary entropy of the mixed true-answer weight `recMixTrue μ p x`. -/
noncomputable def recPostEnt {n : ℕ} (μ : Fin n → ℝ) (p : ℝ) (x : Fin n) : ℝ :=
  binEntropy (recMixTrue μ p x)

/-- The expression `1 - recPostEnt μ p x` associated with a mixed query slot. -/
noncomputable def recSlotInfo {n : ℕ} (μ : Fin n → ℝ) (p : ℝ) (x : Fin n) : ℝ :=
  1 - recPostEnt μ p x

/-- The quotient of `fanoNumerator n δ` by the mixed-slot information expression `recSlotInfo μ
p x`. -/
noncomputable def recFanoCapacityBound {n : ℕ} (μ : Fin n → ℝ) (p : ℝ) (x : Fin n)
    (δ : ℝ) : ℝ :=
  fanoNumerator n δ / recSlotInfo μ p x

/-- A family of stopped binary-query programs with a specified number of levels, a shared
stopping rule, and guesses determined by the used answers at every level. -/
structure RecBscProgram (n k : ℕ) where

  levels : ℕ

  levelProg : ℕ → BscStopProgram n k

  sharedStop : ∀ L L' : ℕ, (levelProg L).stop = (levelProg L').stop

  guessFromUsed : ∀ L : ℕ, StopGuessFromUsed (levelProg L)

/-- The common stopping rule represented by the stopping rule of level zero. -/
def recSharedStop {n k : ℕ} (prog : RecBscProgram n k) : (Fin k → Bool) → Fin (k + 1) :=
  (prog.levelProg 0).stop

/-- The natural number `prog.levels - 1`, using truncated subtraction. -/
def recLastLevel {n k : ℕ} (prog : RecBscProgram n k) : ℕ :=
  prog.levels - 1

/-- The sum of the expected stopping costs of all levels below `prog.levels`. -/
noncomputable def recExpectedCost {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) : ℝ :=
  ∑ L ∈ Finset.range prog.levels, expectedStopCost (prog.levelProg L) p

/-- The error weight of the final level of a recursive program with a positive number of levels. -/
noncomputable def recErrorProb {n k : ℕ} (prog : RecBscProgram n k)
    (_h : 0 < prog.levels) (p : ℝ) : ℝ :=
  stopErrorProb (prog.levelProg (recLastLevel prog)) p

/-- The recursively nested product of `L` padded binary transcripts, with `Unit` at level zero. -/
@[reducible] def RecTower (n k : ℕ) : ℕ → Type
  | 0 => Unit
  | L + 1 => RecTower n k L × (Fin k → (Sum Bool Unit))

instance (n k : ℕ) (L : ℕ) : Fintype (RecTower n k L) := by
  induction L with
  | zero => exact inferInstance
  | succ L ih =>
    letI : Fintype (RecTower n k L) := ih
    exact inferInstance

/-- The recursively nested product of `L` full binary transcripts, with `Unit` at level zero. -/
@[reducible] def RecRawTower (n k : ℕ) : ℕ → Type
  | 0 => Unit
  | L + 1 => RecRawTower n k L × (Fin k → Bool)

instance (n k : ℕ) (L : ℕ) : Fintype (RecRawTower n k L) := by
  induction L with
  | zero => exact inferInstance
  | succ L ih =>
    letI : Fintype (RecRawTower n k L) := ih
    exact inferInstance

/-- The real-valued indicator that padding the full transcript `y` gives `e`. -/
noncomputable def stopPadEq {n k : ℕ} (prog : BscStopProgram n k) (y : Fin k → Bool)
    (e : Fin k → (Sum Bool Unit)) : ℝ :=
  if stopPad prog y = e then 1 else 0

/-- The sum of full transcript likelihoods over the fibre of a padded transcript at a fixed
hidden rank. -/
noncomputable def stopUsedCond {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (x : Fin n) (e : Fin k → (Sum Bool Unit)) : ℝ :=
  ∑ y : Fin k → Bool, bscLikPre prog.cuts p x y * stopPadEq prog y e

/-- Pad each level of a raw transcript tower with that level's stopping program. -/
def recPadTower {n k : ℕ} (prog : RecBscProgram n k) :
    (L : ℕ) → RecRawTower n k L → RecTower n k L
  | 0, _ => ()
  | L + 1, y => (recPadTower prog L y.1, stopPad (prog.levelProg L) y.2)

/-- The product of the levelwise binary transcript likelihoods at a fixed hidden rank, defined
recursively from the value one at level zero. -/
noncomputable def recLikTower {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) :
    (L : ℕ) → Fin n → RecRawTower n k L → ℝ
  | 0, _, _ => 1
  | L + 1, x, y => recLikTower prog p L x y.1 * bscLikPre (prog.levelProg L).cuts p x y.2

/-- The joint weight of a hidden rank and a raw transcript tower, using a uniform prior on the
hidden rank. -/
noncomputable def recRawJointLaw {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) (L : ℕ) :
    Fin n × RecRawTower n k L → ℝ :=
  fun z => (1 / (n : ℝ)) * recLikTower prog p L z.1 z.2

/-- The real-valued indicator that the raw tower `y` is mapped to the padded tower `e` by
`recPadTower`. -/
noncomputable def recPadEq {n k : ℕ} (prog : RecBscProgram n k) (L : ℕ)
    (y : RecRawTower n k L) (e : RecTower n k L) : ℝ :=
  if recPadTower prog L y = e then 1 else 0

/-- The joint weight of the hidden rank and a padded tower obtained by summing raw joint weights
over the fibres of `recPadTower`. -/
noncomputable def recUsedJointLaw {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) (L : ℕ) :
    Fin n × RecTower n k L → ℝ :=
  fun z => ∑ y : RecRawTower n k L, recRawJointLaw prog p L (z.1, y)
    * recPadEq prog L y z.2

/-- The recursively defined product of the levelwise padded-transcript conditional weights at a
fixed hidden rank. -/
noncomputable def recUsedTowerProd {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) :
    (L : ℕ) → Fin n → RecTower n k L → ℝ
  | 0, _, _ => 1
  | L + 1, x, e => recUsedTowerProd prog p L x e.1 * stopUsedCond (prog.levelProg L) p x e.2

/-- The sum of raw tower likelihoods over all raw towers that pad to the specified tower. -/
noncomputable def recLikFibre {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) :
    (L : ℕ) → Fin n → RecTower n k L → ℝ :=
  fun L x e => ∑ y : RecRawTower n k L, recLikTower prog p L x y * recPadEq prog L y e

/-- The supplied guess function on padded transcript towers, viewed with the recursive program
parameters. -/
def recTowerGuess {n k : ℕ} (_prog : RecBscProgram n k) (L : ℕ)
    (g : RecTower n k L → Fin n) : RecTower n k L → Fin n :=
  g

/-- The total joint weight on which the supplied padded-tower guess differs from the hidden
rank. -/
noncomputable def recCombinedErrorProb {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) (L : ℕ)
    (g : RecTower n k L → Fin n) : ℝ :=
  ∑ x, ∑ e, recUsedJointLaw prog p L (x, e) * (if g e = x then 0 else 1)

/-- The mutual information expression between the hidden rank and a padded transcript tower. -/
noncomputable def recUsedMutInfo {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) (L : ℕ) : ℝ :=
  mutInfo (recUsedJointLaw prog p L)

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
