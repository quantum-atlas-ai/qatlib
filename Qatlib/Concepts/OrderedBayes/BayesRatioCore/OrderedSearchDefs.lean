/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.NormNum
set_option warningAsError false

set_option autoImplicit false

noncomputable section

open scoped BigOperators Classical Matrix
open Qatlib
open Qatlib.Concepts.OrderedBayes.BayesRatioCore
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
open Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels.OrderedSearch2007
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

abbrev Comparison (n : ℕ) := Fin n × Bool

abbrev Record (n : ℕ) := List (Comparison n)

noncomputable def answerLikelihood {n : ℕ} (m c : Fin n) (p : ℝ) (b : Bool) : ℝ :=
  if b then bayesTrueLikelihood c m p else bayesFalseLikelihood c m p

noncomputable def correctPost {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (p : ℝ) (b : Bool) :
    Fin n → ℝ :=
  fun m => if b then bayesTruePost a c p m else bayesFalsePost a c p m

noncomputable def printedTrueLikelihood {n : ℕ} (c m : Fin n) (p : ℝ) : ℝ :=
  if (m : ℕ) ≤ (c : ℕ) then 1 - p else p

noncomputable def recordLikelihood {n : ℕ} (t : Record n) (m : Fin n) (p : ℝ) : ℝ :=
  t.foldr (fun obs acc => answerLikelihood m obs.1 p obs.2 * acc) 1

noncomputable def transportWeights {n : ℕ} : Record n → ℝ → Fin n → ℝ
  | [], _p, m => uniformPosterior (n := n) m
  | obs :: t, p, m => transportWeights t p m * answerLikelihood m obs.1 p obs.2

noncomputable def transportFold {n : ℕ} : Record n → ℝ → Fin n → ℝ
  | [], _p, m => uniformPosterior (n := n) m
  | obs :: t, p, m => correctPost (transportFold t p) obs.1 p obs.2 m

noncomputable def recordPosterior {n : ℕ} (t : Record n) (p : ℝ) (m : Fin n) : ℝ :=
  transportWeights t p m / (∑ m', transportWeights t p m')

noncomputable def offCellMass {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (m : Fin n) : ℝ :=
  if m = c then 0 else a m

def sourceRank {n : ℕ} (m : Fin n) : ℕ := m.val + 1

def rankIndex {n : ℕ} (r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) : Fin n := ⟨r - 1, by omega⟩

def sourceSide {n : ℕ} (c j : Fin n) : Prop := (c : ℕ) ≤ (j : ℕ)

structure SearchOutcome (n : ℕ) where

  posterior : Fin n → ℝ

  cut : Fin n

  report : Fin n

  clock : ℕ

noncomputable def runRecord {n : ℕ} (hn : 0 < n) (p ε : ℝ) (t : Record n) :
    SearchOutcome n :=
  { posterior := recordPosterior t p
    cut := stageTwoCut hn (recordPosterior t p) ε
    report := haltCut hn (recordPosterior t p) ε
    clock := t.length }

noncomputable def cutAt {n : ℕ} (hn : 0 < n) (p ε : ℝ) (t : Record n) : Fin n :=
  stageTwoCut hn (transportFold t p) ε

def WellFormed {n : ℕ} (hn : 0 < n) (p ε : ℝ) : Record n → Prop
  | [] => True
  | obs :: t => obs.1 = cutAt hn p ε t ∧ WellFormed hn p ε t

noncomputable def extend {n : ℕ} (hn : 0 < n) (p ε : ℝ) (t : Record n) (b : Bool) :
    Record n :=
  t ++ [(cutAt hn p ε t, b)]

noncomputable def stepWeight {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n) (t : Record n)
    (b : Bool) : ℝ :=
  answerLikelihood u (cutAt hn p ε t) p b

noncomputable def recordRatio {n : ℕ} (t : Record n) (u v : Fin n) (p : ℝ) : ℝ :=
  recordLikelihood t v p / recordLikelihood t u p

noncomputable def treeWeight {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n)
    (V : Record n → ℝ) : ℕ → Record n → ℝ
  | 0, t => V t
  | m + 1, t =>
      ∑ b : Bool, stepWeight hn p ε u t b
        * treeWeight hn p ε u V m (extend hn p ε t b)

noncomputable def treeCross {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u v : Fin n) (R : ℝ)
    : ℕ → Record n → ℝ
  | 0, t => if R ≤ recordRatio t u v p then 1 else 0
  | m + 1, t =>
      ∑ b : Bool, stepWeight hn p ε u t b
        * treeCross hn p ε u v R m (extend hn p ε t b)

noncomputable def treeDiff {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u v : Fin n) (R : ℝ)
    : ℕ → Record n → ℝ
  | 0, t => recordRatio t u v p - R * (if R ≤ recordRatio t u v p then 1 else 0)
  | m + 1, t =>
      ∑ b : Bool, stepWeight hn p ε u t b
        * treeDiff hn p ε u v R m (extend hn p ε t b)

noncomputable def treeCrossOf {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n) (v w : Fin n)
    (R : ℝ) : ℕ → Record n → ℝ
  | 0, t => if R ≤ recordRatio t v w p then 1 else 0
  | m + 1, t =>
      ∑ b : Bool, stepWeight hn p ε u t b
        * treeCrossOf hn p ε u v w R m (extend hn p ε t b)

noncomputable def treeDiffOf {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n) (v w : Fin n)
    (R : ℝ) : ℕ → Record n → ℝ
  | 0, t => recordRatio t v w p - R * (if R ≤ recordRatio t v w p then 1 else 0)
  | m + 1, t =>
      ∑ b : Bool, stepWeight hn p ε u t b
        * treeDiffOf hn p ε u v w R m (extend hn p ε t b)

noncomputable def treeCount {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n)
    (φ : Record n → Prop) : ℕ → Record n → ℝ
  | 0, t => if φ t then 1 else 0
  | m + 1, t =>
      ∑ b : Bool, stepWeight hn p ε u t b
        * treeCount hn p ε u φ m (extend hn p ε t b)

noncomputable def treeCountFinset {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n)
    (S : Finset (Fin n)) (φ : Fin n → Record n → Prop) : ℕ → Record n → ℝ
  | 0, t => ∑ k ∈ S, if φ k t then 1 else 0
  | m + 1, t =>
      ∑ b : Bool, stepWeight hn p ε u t b
        * treeCountFinset hn p ε u S φ m (extend hn p ε t b)

def windowCells {n : ℕ} (i : Fin n) (l : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun j => (i : ℕ) - l ≤ (j : ℕ) ∧ (j : ℕ) < (i : ℕ)

def haltCells {n : ℕ} (a : Fin n → ℝ) (ε : ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => ε ≤ a i

noncomputable def bscRotation (p : ℝ) : Bool → Bool → ℂ
  | false, false => Real.sqrt p
  | true, false => Real.sqrt (1 - p)
  | false, true => -(Real.sqrt (1 - p))
  | true, true => Real.sqrt p

noncomputable def bscRotationMatrix (p : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Real.sqrt p, -(Real.sqrt (1 - p)); Real.sqrt (1 - p), Real.sqrt p]

noncomputable def Blockwise {n : ℕ} (g : Fin n → Bool → Bool → ℂ) :
    Matrix (Fin n × Bool) (Fin n × Bool) ℂ :=
  fun b a => if b.1 = a.1 then g a.1 b.2 a.2 else 0

noncomputable def dilutedOracle {n : ℕ} (f : Fin n → Bool) (p : ℝ) :
    Matrix (Fin n × Bool) (Fin n × Bool) ℂ :=
  Blockwise (fun x out in_ => bscRotation p out (in_ != f x))

noncomputable def idealOracle {n : ℕ} (f : Fin n → Bool) :
    Matrix (Fin n × Bool) (Fin n × Bool) ℂ :=
  fun b a => if b.1 = a.1 && b.2 == (a.2 != f a.1) then 1 else 0

noncomputable def bscAnswerProb (p : ℝ) (ideal out : Bool) : ℝ :=
  if out = ideal then p else 1 - p

noncomputable def oracleApplications {n : ℕ} (t : Record n) : ℕ := t.length

noncomputable def recursiveOracleApplications {n : ℕ} (levels : List (Record n)) : ℕ :=
  (levels.map oracleApplications).sum

noncomputable def noisyAnswerProb {n : ℕ} (j c : Fin n) (p : ℝ) : ℝ :=
  if (c : ℕ) ≤ (j : ℕ) then p else 1 - p

noncomputable def noisyOutputProb {n : ℕ} (j : Fin n) (p : ℝ) :
    BoolQueryTree (Fin n) (Fin n) → Fin n → ℝ
  | .halt o, out => if o = out then 1 else 0
  | .ask c onFalse onTrue, out =>
      noisyAnswerProb j c p * noisyOutputProb j p onTrue out
        + (1 - noisyAnswerProb j c p) * noisyOutputProb j p onFalse out

noncomputable def noisyExpectedQueries {n : ℕ} (j : Fin n) (p : ℝ) :
    BoolQueryTree (Fin n) (Fin n) → ℝ
  | .halt _ => 0
  | .ask c onFalse onTrue =>
      1 + noisyAnswerProb j c p * noisyExpectedQueries j p onTrue
        + (1 - noisyAnswerProb j c p) * noisyExpectedQueries j p onFalse

noncomputable def noisyExpectedOracleApplications {n : ℕ} (j : Fin n) (p : ℝ)
    (tr : BoolQueryTree (Fin n) (Fin n)) : ℝ :=
  noisyExpectedQueries j p tr

noncomputable def noiselessOutput {n : ℕ} (j : Fin n) :
    BoolQueryTree (Fin n) (Fin n) → Fin n
  | .halt o => o
  | .ask c onFalse onTrue =>
      if (c : ℕ) ≤ (j : ℕ) then noiselessOutput j onTrue else noiselessOutput j onFalse

noncomputable def leafCountWithin {n : ℕ} : ℕ → BoolQueryTree (Fin n) (Fin n) → ℕ
  | 0, .halt _ => 1
  | 0, .ask _ _ _ => 0
  | d + 1, .halt _ => 1
  | d + 1, .ask _ onFalse onTrue => leafCountWithin d onFalse + leafCountWithin d onTrue

noncomputable def noiselessQueries {n : ℕ} (j : Fin n) :
    BoolQueryTree (Fin n) (Fin n) → ℕ
  | .halt _ => 0
  | .ask c onFalse onTrue =>
      1 + (if (c : ℕ) ≤ (j : ℕ) then noiselessQueries j onTrue
          else noiselessQueries j onFalse)

noncomputable def treeDepth {n : ℕ} (p : ℝ) :
    BoolQueryTree (Fin n) (Fin n) → (Fin n → ℝ) → ℝ → ℝ
  | .halt _, _, _ => 0
  | .ask c onFalse onTrue, a, W =>
      W +
        treeDepth p onFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p) +
        treeDepth p onTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p)

noncomputable def treeInfo {n : ℕ} (p : ℝ) :
    BoolQueryTree (Fin n) (Fin n) → (Fin n → ℝ) → ℝ → ℝ
  | .halt _, _, _ => 0
  | .ask c onFalse onTrue, a, W =>
      W * bayesFalseNorm a c p * (postInfo (bayesFalsePost a c p) - postInfo a) +
        W * bayesTrueNorm a c p * (postInfo (bayesTruePost a c p) - postInfo a) +
        treeInfo p onFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p) +
        treeInfo p onTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p)

noncomputable def treeLeaf {n : ℕ} (p : ℝ) (f : (Fin n → ℝ) → Fin n → ℝ) :
    BoolQueryTree (Fin n) (Fin n) → (Fin n → ℝ) → ℝ → ℝ
  | .halt o, a, W => W * f a o
  | .ask c onFalse onTrue, a, W =>
      treeLeaf p f onFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p) +
        treeLeaf p f onTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p)

noncomputable def uniformExpectedQueries {n : ℕ} (p : ℝ)
    (tr : BoolQueryTree (Fin n) (Fin n)) : ℝ :=
  treeDepth p tr (uniformPosterior (n := n)) 1

noncomputable def recursiveExpectedOracleApplications {n : ℕ} (p : ℝ)
    (levels : List (BoolQueryTree (Fin n) (Fin n))) : ℝ :=
  levels.foldr (fun tr acc => uniformExpectedQueries p tr + acc) 0

noncomputable def uniformPosteriorEntropy {n : ℕ} (p : ℝ)
    (tr : BoolQueryTree (Fin n) (Fin n)) : ℝ :=
  treeLeaf p (fun a _ => entropy a) tr (uniformPosterior (n := n)) 1

noncomputable def uniformPosteriorInfo {n : ℕ} (p : ℝ)
    (tr : BoolQueryTree (Fin n) (Fin n)) : ℝ :=
  treeLeaf p (fun a _ => postInfo a) tr (uniformPosterior (n := n)) 1

noncomputable def uniformErrorProb {n : ℕ} (p : ℝ)
    (tr : BoolQueryTree (Fin n) (Fin n)) : ℝ :=
  treeLeaf p (fun a o => 1 - a o) tr (uniformPosterior (n := n)) 1

noncomputable def treeDeepProb {n : ℕ} (p : ℝ) (b : ℕ) :
    BoolQueryTree (Fin n) (Fin n) → (Fin n → ℝ) → ℝ → ℝ
  | .halt _, _, W => if b = 0 then W else 0
  | .ask c onFalse onTrue, a, W =>
      if b = 0 then W
      else treeDeepProb p (b - 1) onFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p)
        + treeDeepProb p (b - 1) onTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p)

noncomputable def uniformTailProb {n : ℕ} (p : ℝ) (t : ℕ)
    (tr : BoolQueryTree (Fin n) (Fin n)) : ℝ :=
  treeDeepProb p t tr (uniformPosterior (n := n)) 1

noncomputable def answerLikelihoodRat {n : ℕ} (m c : Fin n) (p : ℚ) (b : Bool) : ℚ :=
  if b then (if (c : ℕ) ≤ (m : ℕ) then p else 1 - p) else (if (c : ℕ) ≤ (m : ℕ) then 1 - p else p)

noncomputable def recordLikelihoodRat {n : ℕ} (p : ℚ) (t : Record n) (m : Fin n) : ℚ :=
  t.foldr (fun obs acc => answerLikelihoodRat m obs.1 p obs.2 * acc) 1

noncomputable def recordPosteriorRat {n : ℕ} (p : ℚ) (t : Record n) (m : Fin n) : ℚ :=
  recordLikelihoodRat p t m / (∑ m', recordLikelihoodRat p t m')

noncomputable def haltCutRat {n : ℕ} (hn : 0 < n) (p ε : ℚ) (t : Record n) : Fin n :=
  if h : (Finset.univ.filter fun i : Fin n => ε ≤ recordPosteriorRat p t i).Nonempty then
    (Finset.univ.filter fun i : Fin n => ε ≤ recordPosteriorRat p t i).min' h
  else ⟨0, hn⟩

noncomputable def prefixMassRat {n : ℕ} (p : ℚ) (t : Record n) (i : Fin n) : ℚ :=
  ∑ j : Fin n, if j.val ≤ i.val then recordPosteriorRat p t j else 0

noncomputable def cutSetRat {n : ℕ} (p : ℚ) (ε : ℚ) (t : Record n) : Finset (Fin n) :=
  Finset.univ.filter fun i => 1 / 2 - ε ≤ prefixMassRat p t i ∧ prefixMassRat p t i < 1 / 2

noncomputable def stageTwoCutRat {n : ℕ} (hn : 0 < n) (p ε : ℚ) (t : Record n) : Fin n :=
  if h : (cutSetRat p ε t).Nonempty then (cutSetRat p ε t).min' h else ⟨0, hn⟩

noncomputable def cutAtRat {n : ℕ} (hn : 0 < n) (p ε : ℚ) (t : Record n) : Fin n :=
  stageTwoCutRat hn p ε t

def IsCrossing {n : ℕ} (k i : Fin n) (obs : Comparison n) : Prop :=
  k.val < obs.1.val ∧ obs.1.val ≤ i.val

noncomputable def crossTrue {n : ℕ} (k i : Fin n) : Record n → ℕ
  | [] => 0
  | obs :: t => (if IsCrossing k i obs ∧ obs.2 = true then 1 else 0) + crossTrue k i t

noncomputable def crossFalse {n : ℕ} (k i : Fin n) : Record n → ℕ
  | [] => 0
  | obs :: t => (if IsCrossing k i obs ∧ obs.2 = false then 1 else 0) + crossFalse k i t

noncomputable def correctCells {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun j => noiselessOutput j tr = j

noncomputable def noiselessDepthSumW {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n))
    (w : Fin n → ℝ) : ℝ :=
  ∑ j, w j * noiselessQueries j tr

noncomputable def noiselessDepthSum {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n)) : ℝ :=
  noiselessDepthSumW tr (fun _ => 1)

noncomputable def noiselessMeanQueries {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n)) : ℝ :=
  noiselessDepthSum tr / n

noncomputable def cellsAboveDepth {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n)) (t : ℕ) :
    Finset (Fin n) :=
  Finset.univ.filter fun j => t < noiselessQueries j tr

noncomputable def crossScore {n : ℕ} (k i : Fin n) (t : Record n) : ℝ :=
  (crossTrue k i t : ℝ) - (crossFalse k i t : ℝ)

noncomputable def crossCount {n : ℕ} (k i : Fin n) (t : Record n) : ℝ :=
  (crossTrue k i t : ℝ) + (crossFalse k i t : ℝ)

noncomputable def stepScore {n : ℕ} (k i : Fin n) (obs : Comparison n) : ℝ :=
  if IsCrossing k i obs then (if obs.2 then 1 else -1) else 0

noncomputable def stepCount {n : ℕ} (k i : Fin n) (obs : Comparison n) : ℝ :=
  if IsCrossing k i obs then 1 else 0

noncomputable def crossMartingale {n : ℕ} (p : ℝ) (k i : Fin n) (t : Record n) : ℝ :=
  crossScore k i t - (1 - 2 * p) * crossCount k i t

noncomputable def treeCrossVar {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u k i : Fin n)
    : ℕ → Record n → ℝ
  | 0, t => 0
  | m + 1, t =>
      ∑ b : Bool, stepWeight hn p ε u t b
        * treeCrossVar hn p ε u k i m (extend hn p ε t b)
      + (if IsCrossing k i (cutAt hn p ε t, true) then 4 * p * (1 - p) else 0)

def windowCellsAbove {n : ℕ} (i : Fin n) (l : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun j => (i : ℕ) < (j : ℕ) ∧ (j : ℕ) ≤ (i : ℕ) + l

noncomputable def upperScore {n : ℕ} (i k : Fin n) (t : Record n) : ℝ :=
  (crossFalse i k t : ℝ) - (crossTrue i k t : ℝ)

noncomputable def stepUpperScore {n : ℕ} (i k : Fin n) (obs : Comparison n) : ℝ :=
  if IsCrossing i k obs then (if obs.2 then -1 else 1) else 0

noncomputable def upperMartingale {n : ℕ} (p : ℝ) (i k : Fin n) (t : Record n) : ℝ :=
  upperScore i k t + (2 * p - 1) * crossCount i k t

noncomputable def cutList {n : ℕ} : Record n → List (Fin n)
  | [] => []
  | obs :: t => obs.1 :: cutList t

def NoDupCuts {n : ℕ} : Record n → Prop
  | [] => True
  | obs :: t => obs.1 ∉ cutList t ∧ NoDupCuts t

abbrev TruthBelowWindow {n : ℕ} (u i : Fin n) (l : ℕ) : Prop :=
  (u : ℕ) + l < (i : ℕ)

abbrev TruthAboveWindow {n : ℕ} (u i : Fin n) (l : ℕ) : Prop :=
  (i : ℕ) + l < (u : ℕ)

abbrev TruthOutsideWindow {n : ℕ} (u i : Fin n) (l : ℕ) : Prop :=
  TruthBelowWindow u i l ∨ TruthAboveWindow u i l

structure Level (n : ℕ) where

  program : BoolQueryTree (Fin n) (Fin n)

  record : Record n

abbrev RecursiveRun (n : ℕ) := List (Level n)

noncomputable def programRun {n : ℕ} :
    BoolQueryTree (Fin n) (Fin n) → Record n → Option (Fin n × ℕ)
  | .halt o, [] => some (o, 0)
  | .halt _, _ :: _ => none
  | .ask _ _ _, [] => none
  | .ask c onFalse onTrue, obs :: rest =>
      if obs.1 = c then
        (programRun (if obs.2 then onTrue else onFalse) rest).map (fun (o, k) => (o, k + 1))
      else none

def LevelExecuted {n : ℕ} (l : Level n) : Prop :=
  ∃ o : Fin n, programRun l.program l.record = some (o, l.record.length)

noncomputable def recursivePathOracleApplications {n : ℕ} (run : RecursiveRun n) : ℕ :=
  (run.map fun l => l.record.length).sum

noncomputable def recursivePathExpectedOracleApplications {n : ℕ} (p : ℝ)
    (run : RecursiveRun n) : ℝ :=
  (run.map fun l => uniformExpectedQueries p l.program).sum

def fggsThreshold {N : ℕ} (j : ℕ) (x : Fin N) : ℝ := if x.val < j then -1 else 1

def fggsFull {N : ℕ} (j : ℕ) (x : Fin (2 * N)) : ℝ :=
  if x.val < N then (if x.val < j then -1 else 1) else (if x.val - N < j then 1 else -1)

def fggsPred {N : ℕ} (hN : 0 < N) (x : Fin (2 * N)) : Fin (2 * N) :=
  if 0 < x.val then ⟨x.val - 1, Nat.sub_lt_of_lt x.isLt⟩ else
    ⟨2 * N - 1, by omega⟩

def fggsSucc {N : ℕ} (hN : 0 < N) (x : Fin (2 * N)) : Fin (2 * N) :=
  ⟨(x.val + 1) % (2 * N), Nat.mod_lt _ (by omega)⟩

def fggsSuccN {N : ℕ} (hN : 0 < N) : ℕ → Fin (2 * N) → Fin (2 * N)
  | 0, x => x
  | k + 1, x => fggsSuccN hN k (fggsSucc hN x)

noncomputable def fggsReportProb {K : ℕ} (Q : Fin K → ℝ) (iv h : Fin K) : ℝ := Q (h - iv)

noncomputable def fggsPosterior {K : ℕ} (a : Fin K → ℝ) (Q : Fin K → ℝ) (h : Fin K) :
    Fin K → ℝ :=
  fun iv => a iv * Q (h - iv) / (∑ iv', a iv' * Q (h - iv'))

noncomputable def fggsReportMarginal {K : ℕ} (a : Fin K → ℝ) (Q : Fin K → ℝ) : Fin K → ℝ :=
  fun h => ∑ iv, a iv * Q (h - iv)

noncomputable def fggsUniformPrior {K : ℕ} : Fin K → ℝ := fun _ => 1 / K

noncomputable def fggsEntropyNat {K : ℕ} (P : Fin K → ℝ) : ℝ := -(∑ i, P i * Real.log (P i))

noncomputable def fggsEntropy {K : ℕ} (P : Fin K → ℝ) : ℝ := fggsEntropyNat P / Real.log 2

noncomputable def fggsMultiInfo {K : ℕ} (Q : Fin K → ℝ) : ℝ :=
  Real.log K / Real.log 2 - fggsEntropy Q

noncomputable def fggsMutualInfoNat {K : ℕ} (a : Fin K → ℝ) (Q : Fin K → ℝ) : ℝ :=
  ∑ h, fggsReportMarginal a Q h *
    (∑ iv, fggsPosterior a Q h iv * Real.log (fggsPosterior a Q h iv / a iv))

noncomputable def fggsMutualInfo {K : ℕ} (a : Fin K → ℝ) (Q : Fin K → ℝ) : ℝ :=
  fggsMutualInfoNat a Q / Real.log 2

end Qatlib.Concepts.OrderedBayes.BayesRatioCore

end

set_option autoImplicit false
