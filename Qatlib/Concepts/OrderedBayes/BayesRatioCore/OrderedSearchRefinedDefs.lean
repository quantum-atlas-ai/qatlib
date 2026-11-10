/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.OrderedSearch
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

open scoped BigOperators Classical
open Qatlib.Concepts.OrderedBayes.BayesRatioCore
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels.OrderedSearch2007

noncomputable def CorrectEqualCutPosterior {n : ℕ} (a : Fin n → ℝ) (c : Fin n)
    (p : ℝ) : ℝ :=
  bayesTruePost a c p c

def PrintedUpdateIsNotThePosterior {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (p : ℝ) : Prop :=
  updateTrue a c p c ≠ bayesTruePost a c p c

def CrossPairCalibration {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u v : Fin n) (δ : ℝ) : Prop :=
  0 < p ∧ p < 1 ∧ 0 < δ ∧
    ∀ m : ℕ, treeCross hn p ε u v (1 / δ) m [] ≤ δ

def truthBit {n : ℕ} (rank : Fin n) (x : Fin n) : Bool := decide (x.val ≤ rank.val)

def boolIndex (b : Bool) : Fin 2 := if b then ⟨1, by decide⟩ else ⟨0, by decide⟩

def answerBit (a : Fin 2) : Bool := a.val = 1

noncomputable def noiseRotation (p : ℝ) (truth : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j =>
    if i.val = 0 then
      if j.val = 0 then (if truth then Real.sqrt (1 - p) else Real.sqrt p)
      else (if truth then Real.sqrt p else -(Real.sqrt (1 - p)))
    else
      if j.val = 0 then (if truth then Real.sqrt p else Real.sqrt (1 - p))
      else (if truth then -(Real.sqrt (1 - p)) else Real.sqrt p)

noncomputable def noisyQueryOracle {n : ℕ} (rank : Fin n) (p : ℝ) :
    Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ :=
  fun b a => if b.1 = a.1 then noiseRotation p (truthBit rank a.1) b.2 a.2 else 0

noncomputable def noiseAmplitude (p : ℝ) (truth answer : Bool) : ℝ :=
  if answer = truth then Real.sqrt p else Real.sqrt (1 - p)

noncomputable def noiseAnswerProb (p : ℝ) (truth answer : Bool) : ℝ :=
  (noiseAmplitude p truth answer) ^ 2

def InNoiseField (p : ℝ) (z : ℂ) : Prop :=
  ∃ a b c d : ℚ,
    z = ((a : ℝ) + (b : ℝ) * Real.sqrt p + (c : ℝ) * Real.sqrt (1 - p)
      + (d : ℝ) * (Real.sqrt p * Real.sqrt (1 - p)) : ℝ)

def NoisyQueryBackend (n : ℕ) (rank : Fin n) (p : ℝ) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧
    noisyQueryOracle rank p ∈ Matrix.unitaryGroup (Fin n × Fin 2) ℂ ∧
    (∀ truth answer : Bool, noiseAnswerProb p truth answer =
      if answer = truth then p else 1 - p) ∧
    (∀ b a : Fin n × Fin 2, InNoiseField p (noisyQueryOracle rank p b a))

noncomputable def fanoNumerator (n : ℕ) (δ : ℝ) : ℝ :=
  Real.log (n : ℝ) / Real.log 2 - binEntropy δ
    - δ * (Real.log ((n - 1 : ℕ) : ℝ) / Real.log 2)

noncomputable def fanoCapacityBound (n : ℕ) (p δ : ℝ) : ℝ :=
  fanoNumerator n δ / queryInfo p

def FanoCapacityContract (n : ℕ) (p δ : ℝ) : Prop :=
  2 ≤ n ∧ 1 / 2 < p ∧ p ≤ 1 ∧ 0 ≤ δ ∧ δ ≤ 1 - 1 / (n : ℝ) ∧
    0 < queryInfo p ∧
    fanoCapacityBound 2 p (1 / 2) = 0 ∧
    (∀ p' : ℝ, 1 / 2 < p' → p' < 1 → fanoCapacityBound 2 p' p' = 1)

noncomputable def xlog2 (x : ℝ) : ℝ := x * (Real.log x / Real.log 2)

noncomputable def entH {α : Type} [Fintype α] (w : α → ℝ) : ℝ := -∑ i, xlog2 (w i)

noncomputable def margL {α β : Type} [Fintype α] [Fintype β] (d : α × β → ℝ) : α → ℝ :=
  fun i => ∑ j, d (i, j)

noncomputable def margR {α β : Type} [Fintype α] [Fintype β] (d : α × β → ℝ) : β → ℝ :=
  fun j => ∑ i, d (i, j)

noncomputable def condW {α β : Type} [Fintype α] [Fintype β] (d : α × β → ℝ)
    (i : α) (j : β) : ℝ :=
  if _h : margL d i = 0 then 0 else d (i, j) / margL d i

noncomputable def condEntH {α β : Type} [Fintype α] [Fintype β] (d : α × β → ℝ) : ℝ :=
  -∑ i, ∑ j, d (i, j) * (Real.log (condW d i j) / Real.log 2)

noncomputable def condEntHR {α β : Type} [Fintype α] [Fintype β] (d : α × β → ℝ) : ℝ :=
  condEntH (fun p => d (p.2, p.1))

noncomputable def mutInfo {α β : Type} [Fintype α] [Fintype β] (d : α × β → ℝ) : ℝ :=
  entH (margL d) - condEntHR d

noncomputable def bscProb (p : ℝ) (truth answer : Bool) : ℝ :=
  if answer = truth then p else 1 - p

structure BscProgram (n k : ℕ) where
  cuts : ∀ i : Fin k, (Fin i.val → Bool) → Fin n
  guess : (Fin k → Bool) → Fin n

def answerPrefix {k : ℕ} (y : Fin k → Bool) (i : Fin k) : Fin i.val → Bool :=
  fun j => y (Fin.castLE (Nat.le_of_lt i.isLt) j)

noncomputable def bscLik {n k : ℕ} (prog : BscProgram n k) (p : ℝ) (x : Fin n)
    (y : Fin k → Bool) : ℝ :=
  ∏ i, bscProb p (truthBit x (prog.cuts i (answerPrefix y i))) (y i)

noncomputable def bscJoint {n k : ℕ} (prog : BscProgram n k) (p : ℝ)
    (x : Fin n) (y : Fin k → Bool) : ℝ :=
  (1 / (n : ℝ)) * bscLik prog p x y

def bscError {n k : ℕ} (prog : BscProgram n k) (x : Fin n) (y : Fin k → Bool) : Bool :=
  decide (prog.guess y ≠ x)

noncomputable def bscErrorProb {n k : ℕ} (prog : BscProgram n k) (p : ℝ) : ℝ :=
  ∑ x, ∑ y, bscJoint prog p x y * (if bscError prog x y then 1 else 0)

def FanoCapacityLowerBound (n k : ℕ) (p δ : ℝ) : Prop :=
  (k : ℝ) ≥ fanoCapacityBound n p δ

def tPre {m : ℕ} {α : Type} (y : Fin (m + 1) → α) : Fin m → α := fun j => y (j.castSucc)

def tLast {m : ℕ} {α : Type} (y : Fin (m + 1) → α) : α := y (Fin.last m)

def tExt {m : ℕ} {α : Type} (pfx : Fin m → α) (b : α) : Fin (m + 1) → α :=
  fun i => if h : i.val = m then b else pfx ⟨i.val, by omega⟩

def tRestrict {k : ℕ} {α : Type} (y : Fin k → α) (j : Fin k) : Fin j.val → α :=
  fun l => y ⟨l.val, by omega⟩

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

noncomputable def bscLikPre {n m : ℕ} (cuts : ∀ i : Fin m, (Fin i.val → Bool) → Fin n)
    (p : ℝ) (x : Fin n) (pfx : Fin m → Bool) : ℝ :=
  ∏ j, bscProb p (truthBit x (cuts j (tRestrict pfx j))) (pfx j)

noncomputable def bscJointCuts {n m : ℕ} (cuts : ∀ i : Fin m, (Fin i.val → Bool) → Fin n)
    (p : ℝ) (x : Fin n) (y : Fin m → Bool) : ℝ :=
  (1 / (n : ℝ)) * bscLikPre cuts p x y

noncomputable def bscStepCond {n m : ℕ} (cuts : ∀ i : Fin (m + 1), (Fin i.val → Bool) → Fin n)
    (p : ℝ) (x : Fin n) (pfx : Fin m → Bool) (b : Bool) : ℝ :=
  bscProb p (truthBit x (cuts (Fin.last m) pfx)) b

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

def cutsPre {n m : ℕ} (cuts : ∀ i : Fin (m + 1), (Fin i.val → Bool) → Fin n) :
    ∀ j : Fin m, (Fin j.val → Bool) → Fin n :=
  fun j => cuts (j.castSucc)

noncomputable def bscJointLaw {n m : ℕ}
    (cuts : ∀ i : Fin m, (Fin i.val → Bool) → Fin n) (p : ℝ) : Fin n × (Fin m → Bool) → ℝ :=
  fun z => bscJointCuts cuts p z.1 z.2

noncomputable def bscMutInfo {n m : ℕ}
    (cuts : ∀ i : Fin m, (Fin i.val → Bool) → Fin n) (p : ℝ) : ℝ :=
  mutInfo (bscJointLaw cuts p)

def BscQueryInfoBound {n m : ℕ}
    (cuts : ∀ i : Fin m, (Fin i.val → Bool) → Fin n) (p : ℝ) : Prop :=
  bscMutInfo cuts p ≤ (m : ℝ) * queryInfo p

def FanoCapacityLegalDelta (δ : ℝ) : Prop :=
  0 ≤ δ ∧ δ ≤ 1 / 2

def SameRunComparisonBound {n k : ℕ} (prog : BscProgram n k) (p δ : ℝ) : Prop :=
  FanoCapacityLegalDelta δ → bscErrorProb prog p ≤ δ → (k : ℝ) ≥ fanoCapacityBound n p δ

def FanoCapacitySmallN (n : ℕ) (p δ : ℝ) : Prop :=
  n ≤ 1 → fanoCapacityBound n p δ ≤ 0

noncomputable def cycProb {k : ℕ} (p : Fin (k + 1) → ℝ) (s h : Fin (k + 1)) : ℝ :=
  p (h - s)

structure CycProgram (n m k : ℕ) where
  sig : ∀ i : Fin m, (Fin i.val → Fin (k + 1)) → Fin n → Fin (k + 1)
  guess : (Fin m → Fin (k + 1)) → Fin n

noncomputable def cycLikCuts {n m k : ℕ}
    (sig : ∀ i : Fin m, (Fin i.val → Fin (k + 1)) → Fin n → Fin (k + 1))
    (p : Fin (k + 1) → ℝ) (x : Fin n) (y : Fin m → Fin (k + 1)) : ℝ :=
  ∏ i, cycProb p (sig i (tRestrict y i) x) (y i)

noncomputable def cycJointCuts {n m k : ℕ}
    (sig : ∀ i : Fin m, (Fin i.val → Fin (k + 1)) → Fin n → Fin (k + 1))
    (p : Fin (k + 1) → ℝ) (x : Fin n) (y : Fin m → Fin (k + 1)) : ℝ :=
  (1 / (n : ℝ)) * cycLikCuts sig p x y

noncomputable def cycJointLaw {n m k : ℕ}
    (sig : ∀ i : Fin m, (Fin i.val → Fin (k + 1)) → Fin n → Fin (k + 1))
    (p : Fin (k + 1) → ℝ) : Fin n × (Fin m → Fin (k + 1)) → ℝ :=
  fun z => cycJointCuts sig p z.1 z.2

def cycError {n m k : ℕ} (prog : CycProgram n m k) (x : Fin n)
    (y : Fin m → Fin (k + 1)) : Bool :=
  decide (prog.guess y ≠ x)

noncomputable def cycErrorProb {n m k : ℕ} (prog : CycProgram n m k)
    (p : Fin (k + 1) → ℝ) : ℝ :=
  ∑ x, ∑ y, cycJointLaw prog.sig p (x, y) * (if cycError prog x y then 1 else 0)

noncomputable def cycSigMutInfo {n m k : ℕ}
    (sig : ∀ i : Fin m, (Fin i.val → Fin (k + 1)) → Fin n → Fin (k + 1))
    (p : Fin (k + 1) → ℝ) : ℝ :=
  mutInfo (cycJointLaw sig p)

noncomputable def cycMutInfo {n m k : ℕ} (prog : CycProgram n m k)
    (p : Fin (k + 1) → ℝ) : ℝ :=
  cycSigMutInfo prog.sig p

noncomputable def cycCapacityBound (n : ℕ) (k : ℕ) (p : Fin (k + 1) → ℝ) (δ : ℝ) : ℝ :=
  fanoNumerator n δ / multiInfo p

def CycQueryInfoBound {n m k : ℕ} (prog : CycProgram n m k) (p : Fin (k + 1) → ℝ) : Prop :=
  cycMutInfo prog p ≤ (m : ℝ) * multiInfo p

def CycSameRunBound {n m k : ℕ} (prog : CycProgram n m k) (p : Fin (k + 1) → ℝ)
    (δ : ℝ) : Prop :=
  FanoCapacityLegalDelta δ → cycErrorProb prog p ≤ δ →
    (m : ℝ) ≥ cycCapacityBound n k p δ

noncomputable def bornProb (v : Fin 2 → ℂ) (b : Bool) : ℝ :=
  (v (boolIndex b)).normSq

noncomputable def answerReset : Fin 2 → ℂ :=
  fun i => if i.val = 0 then 1 else 0

noncomputable def qStepState {n : ℕ} (rank : Fin n) (p : ℝ) (x : Fin n) : Fin 2 → ℂ :=
  fun b => noisyQueryOracle rank p (x, boolIndex (answerBit b)) (x, ⟨0, by decide⟩)

noncomputable def qStepProb {n : ℕ} (rank : Fin n) (p : ℝ) (x : Fin n) (b : Bool) : ℝ :=
  bornProb (qStepState rank p x) b

structure QuantumQueryProgram (n q : ℕ) where
  cuts : ∀ i : Fin q, (Fin i.val → Bool) → Fin n
  guess : (Fin q → Bool) → Fin n

def toBscProg {n q : ℕ} (prog : QuantumQueryProgram n q) : BscProgram n q where
  cuts := prog.cuts
  guess := prog.guess

noncomputable def qLik {n q : ℕ} (prog : QuantumQueryProgram n q) (p : ℝ) (rank : Fin n)
    (y : Fin q → Bool) : ℝ :=
  ∏ i, qStepProb rank p (prog.cuts i (answerPrefix y i)) (y i)

noncomputable def qJoint {n q : ℕ} (prog : QuantumQueryProgram n q) (p : ℝ)
    (rank : Fin n) (y : Fin q → Bool) : ℝ :=
  (1 / (n : ℝ)) * qLik prog p rank y

def qError {n q : ℕ} (prog : QuantumQueryProgram n q) (rank : Fin n)
    (y : Fin q → Bool) : Bool :=
  decide (prog.guess y ≠ rank)

noncomputable def qErrorProb {n q : ℕ} (prog : QuantumQueryProgram n q) (p : ℝ) : ℝ :=
  ∑ rank, ∑ y, qJoint prog p rank y * (if qError prog rank y then 1 else 0)

def QuantumQueryBackend (n : ℕ) (p : ℝ) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧
    (∀ rank : Fin n, noisyQueryOracle rank p ∈ Matrix.unitaryGroup (Fin n × Fin 2) ℂ) ∧
    (∀ rank : Fin n, ∀ x : Fin n, ∀ b : Bool,
      qStepProb rank p x b = bscProb p (truthBit rank x) b) ∧
    (∀ rank : Fin n, ∀ x : Fin n, ∑ b, qStepProb rank p x b = 1)

def QuantumQueryLowerBound (n q : ℕ) (p δ : ℝ) : Prop :=
  (q : ℝ) ≥ fanoCapacityBound n p δ

structure BscStopProgram (n k : ℕ) where
  cuts : ∀ i : Fin k, (Fin i.val → Bool) → Fin n
  stop : (Fin k → Bool) → Fin (k + 1)
  guess : (Fin k → Bool) → Fin n

  prefixDetermined : ∀ y : Fin k → Bool, ∀ y' : Fin k → Bool,
    (∀ j : Fin k, j.val < (stop y).val → y j = y' j) → stop y = stop y'

def stopToBscProg {n k : ℕ} (prog : BscStopProgram n k) : BscProgram n k where
  cuts := prog.cuts
  guess := prog.guess

noncomputable def stopCost {n k : ℕ} (prog : BscStopProgram n k) (y : Fin k → Bool) : ℝ :=
  (prog.stop y).val

noncomputable def bscTransMarginal {n k : ℕ} (prog : BscProgram n k) (p : ℝ)
    (y : Fin k → Bool) : ℝ :=
  ∑ x, bscJoint prog p x y

noncomputable def expectedStopCost {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ) : ℝ :=
  ∑ y, bscTransMarginal (stopToBscProg prog) p y * stopCost prog y

noncomputable def stopErrorProb {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ) : ℝ :=
  ∑ x, ∑ y, bscJoint (stopToBscProg prog) p x y * (if prog.guess y ≠ x then 1 else 0)

noncomputable def stopCostTail {n k : ℕ} (prog : BscStopProgram n k) (t : ℝ)
    (y : Fin k → Bool) : ℝ :=
  if stopCost prog y ≥ t then 1 else 0

noncomputable def stopTailProb {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (t : ℝ) : ℝ :=
  ∑ y, bscTransMarginal (stopToBscProg prog) p y * stopCostTail prog t y

def stopPrefix {k : ℕ} (i : ℕ) (hk : i ≤ k) (y : Fin k → Bool) : Fin i → Bool :=
  fun j => y ⟨j.val, lt_of_lt_of_le j.isLt hk⟩

def stopExt {k : ℕ} (i : ℕ) (pfx : Fin i → Bool) : Fin k → Bool :=
  fun j => if h : j.val < i then pfx ⟨j.val, h⟩ else false

def stopAlive {n k : ℕ} (prog : BscStopProgram n k) (i : ℕ) (pfx : Fin i → Bool) : Prop :=
  (prog.stop (stopExt i pfx)).val > i

noncomputable def stopAliveProb {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (i : ℕ) (hk : i ≤ k) : ℝ :=
  ∑ y : Fin k → Bool, bscTransMarginal (stopToBscProg prog) p y
    * (if stopAlive prog i (stopPrefix i hk y) then 1 else 0)

noncomputable def stopSurvivalProfile {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ) :
    Fin (k + 1) → ℝ :=
  fun i => stopAliveProb prog p i.val (by omega)

def StopSurvivalContract {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ) : Prop :=
  expectedStopCost prog p = ∑ i, stopSurvivalProfile prog p i

def stopPad {n k : ℕ} (prog : BscStopProgram n k) (y : Fin k → Bool) : Fin k → (Sum Bool Unit) :=
  fun i => if i.val < (prog.stop y).val then Sum.inl (y i) else Sum.inr ()

def stopPadDecode {k : ℕ} (e : Fin k → (Sum Bool Unit)) : Fin k → Bool :=
  fun i => match e i with
    | Sum.inl b => b
    | Sum.inr _ => false

noncomputable def stopUsedJoint {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (x : Fin n) (e : Fin k → (Sum Bool Unit)) : ℝ :=
  ∑ y : Fin k → Bool, bscJointCuts prog.cuts p x y * (if stopPad prog y = e then 1 else 0)

noncomputable def stopUsedJointLaw {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ) :
    Fin n × (Fin k → (Sum Bool Unit)) → ℝ :=
  fun z => stopUsedJoint prog p z.1 z.2

noncomputable def stopUsedMutInfo {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ) : ℝ :=
  mutInfo (stopUsedJointLaw prog p)

def stopUsedGuess {n k : ℕ} (prog : BscStopProgram n k) (e : Fin k → (Sum Bool Unit)) : Fin n :=
  prog.guess (stopPadDecode e)

def StopGuessFromUsed {n k : ℕ} (prog : BscStopProgram n k) : Prop :=
  ∀ y y' : Fin k → Bool, stopPad prog y = stopPad prog y' → prog.guess y = prog.guess y'

def tPrefix {k : ℕ} (i : ℕ) (hk : i ≤ k) {α : Type} (y : Fin k → α) : Fin i → α :=
  fun j => y ⟨j.val, lt_of_lt_of_le j.isLt hk⟩

def cutsPrefix {n : ℕ} {k : ℕ} (i : ℕ)
    (cuts : ∀ j : Fin k, (Fin j.val → Bool) → Fin n) (hk : i ≤ k) :
    ∀ j : Fin i, (Fin j.val → Bool) → Fin n :=
  fun j => cuts ⟨j.val, lt_of_lt_of_le j.isLt hk⟩

noncomputable def sumOverPrefix {k i : ℕ} {α : Type} [Fintype α]
    [DecidableEq α] (g : (Fin k → α) → ℝ) (w : Fin i → α) (hk : i ≤ k) : ℝ :=
  ∑ y : Fin k → α, g y * (if tPrefix i hk y = w then 1 else 0)

noncomputable def stopUsedPrefixLaw {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (i : ℕ) (hk : i ≤ k) : Fin n × (Fin i → (Sum Bool Unit)) → ℝ :=
  fun z => ∑ y : Fin k → Bool, bscJointCuts prog.cuts p z.1 y
    * (if tPrefix i hk (stopPad prog y) = z.2 then 1 else 0)

def padAllInl {i : ℕ} (pfx : Fin i → (Sum Bool Unit)) : Prop :=
  ∀ j : Fin i, ∃ b : Bool, pfx j = Sum.inl b

def padAlive {n k : ℕ} (prog : BscStopProgram n k) {i : ℕ}
    (pfx : Fin i → (Sum Bool Unit)) : Prop :=
  padAllInl pfx ∧ stopAlive prog i (stopPadDecode pfx)

noncomputable def stopSlotMargLaw {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    {i : ℕ} (hi : i + 1 ≤ k) : (Fin i → (Sum Bool Unit)) × (Sum Bool Unit) → ℝ :=
  fun z => ∑ x, stopUsedPrefixLaw prog p (i + 1) hi (x, tExt z.1 z.2)

noncomputable def stopSlotPostLaw {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    {i : ℕ} (hi : i + 1 ≤ k) :
    (Fin n × (Fin i → (Sum Bool Unit))) × (Sum Bool Unit) → ℝ :=
  fun z => stopUsedPrefixLaw prog p (i + 1) hi (z.1.1, tExt z.1.2 z.2)

noncomputable def stopLiveMass {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    {i : ℕ} (hi : i ≤ k) : ℝ :=
  ∑ pfx : Fin i → (Sum Bool Unit),
    (if padAlive prog pfx then (∑ x, stopUsedPrefixLaw prog p i hi (x, pfx)) else 0)

noncomputable def stopSlotChainTerm {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (i : ℕ) : ℝ :=
  if h : i + 1 ≤ k then
    condEntH (stopSlotMargLaw prog p h) - condEntH (stopSlotPostLaw prog p h)
  else 0

def RecQueryProb {n : ℕ} (μ : Fin n → ℝ) : Prop :=
  (∀ c, 0 ≤ μ c) ∧ (∑ c, μ c = 1)

def recPointMass {n : ℕ} (c : Fin n) : Fin n → ℝ :=
  fun d => if d = c then 1 else 0

noncomputable def recMixProb {n : ℕ} (μ : Fin n → ℝ) (p : ℝ) (x : Fin n)
    (b : Bool) : ℝ :=
  ∑ c, μ c * bscProb p (truthBit x c) b

noncomputable def recTrueMass {n : ℕ} (μ : Fin n → ℝ) (x : Fin n) : ℝ :=
  ∑ c, μ c * (if truthBit x c then 1 else 0)

noncomputable def recMixTrue {n : ℕ} (μ : Fin n → ℝ) (p : ℝ) (x : Fin n) : ℝ :=
  recMixProb μ p x true

noncomputable def recPostEnt {n : ℕ} (μ : Fin n → ℝ) (p : ℝ) (x : Fin n) : ℝ :=
  binEntropy (recMixTrue μ p x)

noncomputable def recSlotInfo {n : ℕ} (μ : Fin n → ℝ) (p : ℝ) (x : Fin n) : ℝ :=
  1 - recPostEnt μ p x

noncomputable def recFanoCapacityBound {n : ℕ} (μ : Fin n → ℝ) (p : ℝ) (x : Fin n)
    (δ : ℝ) : ℝ :=
  fanoNumerator n δ / recSlotInfo μ p x

structure RecBscProgram (n k : ℕ) where

  levels : ℕ

  levelProg : ℕ → BscStopProgram n k

  sharedStop : ∀ L L' : ℕ, (levelProg L).stop = (levelProg L').stop

  guessFromUsed : ∀ L : ℕ, StopGuessFromUsed (levelProg L)

def recSharedStop {n k : ℕ} (prog : RecBscProgram n k) : (Fin k → Bool) → Fin (k + 1) :=
  (prog.levelProg 0).stop

def recLastLevel {n k : ℕ} (prog : RecBscProgram n k) : ℕ :=
  prog.levels - 1

noncomputable def recExpectedCost {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) : ℝ :=
  ∑ L ∈ Finset.range prog.levels, expectedStopCost (prog.levelProg L) p

noncomputable def recErrorProb {n k : ℕ} (prog : RecBscProgram n k)
    (_h : 0 < prog.levels) (p : ℝ) : ℝ :=
  stopErrorProb (prog.levelProg (recLastLevel prog)) p

@[reducible] def RecTower (n k : ℕ) : ℕ → Type
  | 0 => Unit
  | L + 1 => RecTower n k L × (Fin k → (Sum Bool Unit))

instance (n k : ℕ) (L : ℕ) : Fintype (RecTower n k L) := by
  induction L with
  | zero => exact inferInstance
  | succ L ih =>
    letI : Fintype (RecTower n k L) := ih
    exact inferInstance

@[reducible] def RecRawTower (n k : ℕ) : ℕ → Type
  | 0 => Unit
  | L + 1 => RecRawTower n k L × (Fin k → Bool)

instance (n k : ℕ) (L : ℕ) : Fintype (RecRawTower n k L) := by
  induction L with
  | zero => exact inferInstance
  | succ L ih =>
    letI : Fintype (RecRawTower n k L) := ih
    exact inferInstance

noncomputable def stopPadEq {n k : ℕ} (prog : BscStopProgram n k) (y : Fin k → Bool)
    (e : Fin k → (Sum Bool Unit)) : ℝ :=
  if stopPad prog y = e then 1 else 0

noncomputable def stopUsedCond {n k : ℕ} (prog : BscStopProgram n k) (p : ℝ)
    (x : Fin n) (e : Fin k → (Sum Bool Unit)) : ℝ :=
  ∑ y : Fin k → Bool, bscLikPre prog.cuts p x y * stopPadEq prog y e

def recPadTower {n k : ℕ} (prog : RecBscProgram n k) :
    (L : ℕ) → RecRawTower n k L → RecTower n k L
  | 0, _ => ()
  | L + 1, y => (recPadTower prog L y.1, stopPad (prog.levelProg L) y.2)

noncomputable def recLikTower {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) :
    (L : ℕ) → Fin n → RecRawTower n k L → ℝ
  | 0, _, _ => 1
  | L + 1, x, y => recLikTower prog p L x y.1 * bscLikPre (prog.levelProg L).cuts p x y.2

noncomputable def recRawJointLaw {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) (L : ℕ) :
    Fin n × RecRawTower n k L → ℝ :=
  fun z => (1 / (n : ℝ)) * recLikTower prog p L z.1 z.2

noncomputable def recPadEq {n k : ℕ} (prog : RecBscProgram n k) (L : ℕ)
    (y : RecRawTower n k L) (e : RecTower n k L) : ℝ :=
  if recPadTower prog L y = e then 1 else 0

noncomputable def recUsedJointLaw {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) (L : ℕ) :
    Fin n × RecTower n k L → ℝ :=
  fun z => ∑ y : RecRawTower n k L, recRawJointLaw prog p L (z.1, y)
    * recPadEq prog L y z.2

noncomputable def recUsedTowerProd {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) :
    (L : ℕ) → Fin n → RecTower n k L → ℝ
  | 0, _, _ => 1
  | L + 1, x, e => recUsedTowerProd prog p L x e.1 * stopUsedCond (prog.levelProg L) p x e.2

noncomputable def recLikFibre {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) :
    (L : ℕ) → Fin n → RecTower n k L → ℝ :=
  fun L x e => ∑ y : RecRawTower n k L, recLikTower prog p L x y * recPadEq prog L y e

def recTowerGuess {n k : ℕ} (_prog : RecBscProgram n k) (L : ℕ)
    (g : RecTower n k L → Fin n) : RecTower n k L → Fin n :=
  g

noncomputable def recCombinedErrorProb {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) (L : ℕ)
    (g : RecTower n k L → Fin n) : ℝ :=
  ∑ x, ∑ e, recUsedJointLaw prog p L (x, e) * (if g e = x then 0 else 1)

noncomputable def recUsedMutInfo {n k : ℕ} (prog : RecBscProgram n k) (p : ℝ) (L : ℕ) : ℝ :=
  mutInfo (recUsedJointLaw prog p L)

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
