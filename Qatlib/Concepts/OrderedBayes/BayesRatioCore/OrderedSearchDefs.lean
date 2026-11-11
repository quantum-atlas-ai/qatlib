/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedBayes.BayesRatioCore.ContractModels
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.NormNum

/-!
# Records and costs for noisy ordered search

This module defines comparison records, likelihoods, and Bayesian updates for noisy ordered
search as studied in [BenOrHassidim2007]. `recordPosterior` normalizes likelihood weights from a
uniform prior, while `transportFold` iterates posterior updates. The finite tree functionals
`treeWeight`, `treeCross`, and `treeCount` aggregate terminal quantities using adaptive
comparison weights.

The module also defines noisy oracle matrices, query counts, exact rational posterior
calculations, crossing statistics, and cyclic report channels. `programRun` checks a record
against a query tree, and `fggsPosterior` describes Bayesian inference for cyclic reports
associated with invariant ordered search [FarhiEtAl1999].

## Main definitions

* `recordPosterior`: normalized posterior associated with a comparison record.
* `treeWeight`: finite adaptive tree evaluation of a terminal function.
* `uniformExpectedQueries`: expected query count from the uniform prior.
* `crossMartingale`: crossing score with its drift subtracted.
* `fggsMutualInfo`: cyclic report information in bits.

## References

* [Ben-Or and Hassidim, 2007][BenOrHassidim2007]
* [Farhi et al., 1999][FarhiEtAl1999]
-/

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

/-- A comparison observation consisting of a cut index and a Boolean answer. -/
abbrev Comparison (n : ℕ) := Fin n × Bool

/-- A finite list of comparison observations on `Fin n`. -/
abbrev Record (n : ℕ) := List (Comparison n)

/-- The likelihood of answer `b` at cut `c` when the hidden cell is `m`, selected from the true
and false Bayesian likelihoods. -/
noncomputable def answerLikelihood {n : ℕ} (m c : Fin n) (p : ℝ) (b : Bool) : ℝ :=
  if b then bayesTrueLikelihood c m p else bayesFalseLikelihood c m p

/-- The posterior update at cut `c` selected by the observed Boolean answer `b`. -/
noncomputable def correctPost {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (p : ℝ) (b : Bool) :
    Fin n → ℝ :=
  fun m => if b then bayesTruePost a c p m else bayesFalsePost a c p m

/-- The printed true-answer likelihood, equal to `1 - p` for `m ≤ c` and to `p` otherwise. -/
noncomputable def printedTrueLikelihood {n : ℕ} (c m : Fin n) (p : ℝ) : ℝ :=
  if (m : ℕ) ≤ (c : ℕ) then 1 - p else p

/-- The product of the answer likelihoods in a comparison record for the hidden cell `m`. -/
noncomputable def recordLikelihood {n : ℕ} (t : Record n) (m : Fin n) (p : ℝ) : ℝ :=
  t.foldr (fun obs acc => answerLikelihood m obs.1 p obs.2 * acc) 1

/-- Unnormalized weights obtained by multiplying the uniform prior by successive answer
likelihoods. -/
noncomputable def transportWeights {n : ℕ} : Record n → ℝ → Fin n → ℝ
  | [], _p, m => uniformPosterior (n := n) m
  | obs :: t, p, m => transportWeights t p m * answerLikelihood m obs.1 p obs.2

/-- The posterior obtained by recursively updating the tail of a record and then processing its
head observation. -/
noncomputable def transportFold {n : ℕ} : Record n → ℝ → Fin n → ℝ
  | [], _p, m => uniformPosterior (n := n) m
  | obs :: t, p, m => correctPost (transportFold t p) obs.1 p obs.2 m

/-- The normalized likelihood weights of a comparison record, starting from the uniform prior. -/
noncomputable def recordPosterior {n : ℕ} (t : Record n) (p : ℝ) (m : Fin n) : ℝ :=
  transportWeights t p m / (∑ m', transportWeights t p m')

/-- The weight function `a` with its value at the distinguished cell `c` replaced by zero. -/
noncomputable def offCellMass {n : ℕ} (a : Fin n → ℝ) (c : Fin n) (m : Fin n) : ℝ :=
  if m = c then 0 else a m

/-- The one-based rank of a cell in `Fin n`. -/
def sourceRank {n : ℕ} (m : Fin n) : ℕ := m.val + 1

/-- The cell with one-based rank `r`, given proofs that `1 ≤ r ≤ n`. -/
def rankIndex {n : ℕ} (r : ℕ) (hr : 1 ≤ r) (hrn : r ≤ n) : Fin n := ⟨r - 1, by omega⟩

/-- The comparison predicate asserting that the cut index `c` is at most the cell index `j`. -/
def sourceSide {n : ℕ} (c j : Fin n) : Prop := (c : ℕ) ≤ (j : ℕ)

/-- The posterior, selected cut, reported cell, and comparison clock associated with a search
state. -/
structure SearchOutcome (n : ℕ) where

  posterior : Fin n → ℝ

  cut : Fin n

  report : Fin n

  clock : ℕ

/-- Constructs a search outcome from the normalized record posterior, its stage-two and halting
cuts, and the record length. -/
noncomputable def runRecord {n : ℕ} (hn : 0 < n) (p ε : ℝ) (t : Record n) :
    SearchOutcome n :=
  { posterior := recordPosterior t p
    cut := stageTwoCut hn (recordPosterior t p) ε
    report := haltCut hn (recordPosterior t p) ε
    clock := t.length }

/-- The stage-two cut selected from the iterated posterior `transportFold` of a record. -/
noncomputable def cutAt {n : ℕ} (hn : 0 < n) (p ε : ℝ) (t : Record n) : Fin n :=
  stageTwoCut hn (transportFold t p) ε

/-- Requires each head observation to use the cut selected from the tail record, recursively. -/
def WellFormed {n : ℕ} (hn : 0 < n) (p ε : ℝ) : Record n → Prop
  | [] => True
  | obs :: t => obs.1 = cutAt hn p ε t ∧ WellFormed hn p ε t

/-- Appends the current selected cut and answer `b` to a record. -/
noncomputable def extend {n : ℕ} (hn : 0 < n) (p ε : ℝ) (t : Record n) (b : Bool) :
    Record n :=
  t ++ [(cutAt hn p ε t, b)]

/-- The likelihood of the next answer at the selected cut under hidden cell `u`. -/
noncomputable def stepWeight {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n) (t : Record n)
    (b : Bool) : ℝ :=
  answerLikelihood u (cutAt hn p ε t) p b

/-- The record likelihood under `v` divided by the record likelihood under `u`. -/
noncomputable def recordRatio {n : ℕ} (t : Record n) (u v : Fin n) (p : ℝ) : ℝ :=
  recordLikelihood t v p / recordLikelihood t u p

/-- Evaluates a terminal function after a fixed number of adaptive comparisons, weighting
branches by their likelihoods under `u`. -/
noncomputable def treeWeight {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n)
    (V : Record n → ℝ) : ℕ → Record n → ℝ
  | 0, t => V t
  | m + 1, t =>
      ∑ b : Bool, stepWeight hn p ε u t b
        * treeWeight hn p ε u V m (extend hn p ε t b)

/-- The finite tree weight of the terminal event that the likelihood ratio of `v` to `u` is at
least `R`. -/
noncomputable def treeCross {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u v : Fin n) (R : ℝ)
    : ℕ → Record n → ℝ
  | 0, t => if R ≤ recordRatio t u v p then 1 else 0
  | m + 1, t =>
      ∑ b : Bool, stepWeight hn p ε u t b
        * treeCross hn p ε u v R m (extend hn p ε t b)

/-- The finite tree weight of the terminal likelihood ratio minus `R` times its threshold
indicator. -/
noncomputable def treeDiff {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u v : Fin n) (R : ℝ)
    : ℕ → Record n → ℝ
  | 0, t => recordRatio t u v p - R * (if R ≤ recordRatio t u v p then 1 else 0)
  | m + 1, t =>
      ∑ b : Bool, stepWeight hn p ε u t b
        * treeDiff hn p ε u v R m (extend hn p ε t b)

/-- The finite tree weight under hidden cell `u` of the terminal event that the likelihood ratio
of `w` to `v` is at least `R`. -/
noncomputable def treeCrossOf {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n) (v w : Fin n)
    (R : ℝ) : ℕ → Record n → ℝ
  | 0, t => if R ≤ recordRatio t v w p then 1 else 0
  | m + 1, t =>
      ∑ b : Bool, stepWeight hn p ε u t b
        * treeCrossOf hn p ε u v w R m (extend hn p ε t b)

/-- The finite tree weight under `u` of the terminal ratio of `w` to `v` minus `R` times its
threshold indicator. -/
noncomputable def treeDiffOf {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n) (v w : Fin n)
    (R : ℝ) : ℕ → Record n → ℝ
  | 0, t => recordRatio t v w p - R * (if R ≤ recordRatio t v w p then 1 else 0)
  | m + 1, t =>
      ∑ b : Bool, stepWeight hn p ε u t b
        * treeDiffOf hn p ε u v w R m (extend hn p ε t b)

/-- The finite tree weight of a terminal predicate on comparison records. -/
noncomputable def treeCount {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n)
    (φ : Record n → Prop) : ℕ → Record n → ℝ
  | 0, t => if φ t then 1 else 0
  | m + 1, t =>
      ∑ b : Bool, stepWeight hn p ε u t b
        * treeCount hn p ε u φ m (extend hn p ε t b)

/-- The finite tree weight of the number of indices in `S` satisfying a terminal predicate. -/
noncomputable def treeCountFinset {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u : Fin n)
    (S : Finset (Fin n)) (φ : Fin n → Record n → Prop) : ℕ → Record n → ℝ
  | 0, t => ∑ k ∈ S, if φ k t then 1 else 0
  | m + 1, t =>
      ∑ b : Bool, stepWeight hn p ε u t b
        * treeCountFinset hn p ε u S φ m (extend hn p ε t b)

/-- The cells in the interval from the truncated index `i - l` up to, but excluding, `i`. -/
def windowCells {n : ℕ} (i : Fin n) (l : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun j => (i : ℕ) - l ≤ (j : ℕ) ∧ (j : ℕ) < (i : ℕ)

/-- The cells whose weight under `a` is at least the halting threshold `ε`. -/
def haltCells {n : ℕ} (a : Fin n → ℝ) (ε : ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => ε ≤ a i

/-- The real two-state rotation with diagonal entries `sqrt p` and off-diagonal entries of
opposite signs and magnitude `sqrt (1 - p)`, viewed over `ℂ`. -/
noncomputable def bscRotation (p : ℝ) : Bool → Bool → ℂ
  | false, false => Real.sqrt p
  | true, false => Real.sqrt (1 - p)
  | false, true => -(Real.sqrt (1 - p))
  | true, true => Real.sqrt p

/-- The two-by-two complex matrix with rows `(sqrt p, -sqrt (1 - p))` and `(sqrt (1 - p), sqrt
p)`. -/
noncomputable def bscRotationMatrix (p : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Real.sqrt p, -(Real.sqrt (1 - p)); Real.sqrt (1 - p), Real.sqrt p]

/-- Forms a block diagonal matrix from a family of Boolean-indexed two-by-two matrices. -/
noncomputable def Blockwise {n : ℕ} (g : Fin n → Bool → Bool → ℂ) :
    Matrix (Fin n × Bool) (Fin n × Bool) ℂ :=
  fun b a => if b.1 = a.1 then g a.1 b.2 a.2 else 0

/-- The block diagonal oracle obtained by applying `bscRotation` after the Boolean oracle action
in each address block. -/
noncomputable def dilutedOracle {n : ℕ} (f : Fin n → Bool) (p : ℝ) :
    Matrix (Fin n × Bool) (Fin n × Bool) ℂ :=
  Blockwise (fun x out in_ => bscRotation p out (in_ != f x))

/-- The Boolean oracle matrix that preserves the address and flips the answer register according
to `f`. -/
noncomputable def idealOracle {n : ℕ} (f : Fin n → Bool) :
    Matrix (Fin n × Bool) (Fin n × Bool) ℂ :=
  fun b a => if b.1 = a.1 && b.2 == (a.2 != f a.1) then 1 else 0

/-- The binary symmetric channel answer probability, equal to `p` for the ideal answer and `1 -
p` otherwise. -/
noncomputable def bscAnswerProb (p : ℝ) (ideal out : Bool) : ℝ :=
  if out = ideal then p else 1 - p

/-- The number of oracle applications represented by a comparison record, defined as its length. -/
noncomputable def oracleApplications {n : ℕ} (t : Record n) : ℕ := t.length

/-- The sum of the record lengths over a list of search levels. -/
noncomputable def recursiveOracleApplications {n : ℕ} (levels : List (Record n)) : ℕ :=
  (levels.map oracleApplications).sum

/-- The probability of a true comparison answer, equal to `p` when `c ≤ j` and to `1 - p`
otherwise. -/
noncomputable def noisyAnswerProb {n : ℕ} (j c : Fin n) (p : ℝ) : ℝ :=
  if (c : ℕ) ≤ (j : ℕ) then p else 1 - p

/-- Recursively computes the output weight of a Boolean query tree for hidden cell `j` and
comparison parameter `p`. -/
noncomputable def noisyOutputProb {n : ℕ} (j : Fin n) (p : ℝ) :
    BoolQueryTree (Fin n) (Fin n) → Fin n → ℝ
  | .halt o, out => if o = out then 1 else 0
  | .ask c onFalse onTrue, out =>
      noisyAnswerProb j c p * noisyOutputProb j p onTrue out
        + (1 - noisyAnswerProb j c p) * noisyOutputProb j p onFalse out

/-- Recursively computes the expected query count for hidden cell `j`, charging one at each
query node. -/
noncomputable def noisyExpectedQueries {n : ℕ} (j : Fin n) (p : ℝ) :
    BoolQueryTree (Fin n) (Fin n) → ℝ
  | .halt _ => 0
  | .ask c onFalse onTrue =>
      1 + noisyAnswerProb j c p * noisyExpectedQueries j p onTrue
        + (1 - noisyAnswerProb j c p) * noisyExpectedQueries j p onFalse

/-- The expected oracle application count, defined as `noisyExpectedQueries`. -/
noncomputable def noisyExpectedOracleApplications {n : ℕ} (j : Fin n) (p : ℝ)
    (tr : BoolQueryTree (Fin n) (Fin n)) : ℝ :=
  noisyExpectedQueries j p tr

/-- The output reached by following the exact comparison answers for hidden cell `j`. -/
noncomputable def noiselessOutput {n : ℕ} (j : Fin n) :
    BoolQueryTree (Fin n) (Fin n) → Fin n
  | .halt o => o
  | .ask c onFalse onTrue =>
      if (c : ℕ) ≤ (j : ℕ) then noiselessOutput j onTrue else noiselessOutput j onFalse

/-- The number of leaves of a Boolean query tree at depth at most the given bound. -/
noncomputable def leafCountWithin {n : ℕ} : ℕ → BoolQueryTree (Fin n) (Fin n) → ℕ
  | 0, .halt _ => 1
  | 0, .ask _ _ _ => 0
  | d + 1, .halt _ => 1
  | d + 1, .ask _ onFalse onTrue => leafCountWithin d onFalse + leafCountWithin d onTrue

/-- The number of queries on the noiseless path for hidden cell `j`. -/
noncomputable def noiselessQueries {n : ℕ} (j : Fin n) :
    BoolQueryTree (Fin n) (Fin n) → ℕ
  | .halt _ => 0
  | .ask c onFalse onTrue =>
      1 + (if (c : ℕ) ≤ (j : ℕ) then noiselessQueries j onTrue
          else noiselessQueries j onFalse)

/-- Aggregates query-node weights using Bayesian branch updates from an initial posterior and
weight. -/
noncomputable def treeDepth {n : ℕ} (p : ℝ) :
    BoolQueryTree (Fin n) (Fin n) → (Fin n → ℝ) → ℝ → ℝ
  | .halt _, _, _ => 0
  | .ask c onFalse onTrue, a, W =>
      W +
        treeDepth p onFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p) +
        treeDepth p onTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p)

/-- Aggregates weighted increments of `postInfo` along the Bayesian branches of a query tree. -/
noncomputable def treeInfo {n : ℕ} (p : ℝ) :
    BoolQueryTree (Fin n) (Fin n) → (Fin n → ℝ) → ℝ → ℝ
  | .halt _, _, _ => 0
  | .ask c onFalse onTrue, a, W =>
      W * bayesFalseNorm a c p * (postInfo (bayesFalsePost a c p) - postInfo a) +
        W * bayesTrueNorm a c p * (postInfo (bayesTruePost a c p) - postInfo a) +
        treeInfo p onFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p) +
        treeInfo p onTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p)

/-- Aggregates a function of the posterior and reported output at leaves, using Bayesian branch
weights. -/
noncomputable def treeLeaf {n : ℕ} (p : ℝ) (f : (Fin n → ℝ) → Fin n → ℝ) :
    BoolQueryTree (Fin n) (Fin n) → (Fin n → ℝ) → ℝ → ℝ
  | .halt o, a, W => W * f a o
  | .ask c onFalse onTrue, a, W =>
      treeLeaf p f onFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p) +
        treeLeaf p f onTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p)

/-- The query-node weight sum for a query tree initialized with the uniform prior and unit
weight. -/
noncomputable def uniformExpectedQueries {n : ℕ} (p : ℝ)
    (tr : BoolQueryTree (Fin n) (Fin n)) : ℝ :=
  treeDepth p tr (uniformPosterior (n := n)) 1

/-- The sum of the uniform-prior expected query counts over a list of query trees. -/
noncomputable def recursiveExpectedOracleApplications {n : ℕ} (p : ℝ)
    (levels : List (BoolQueryTree (Fin n) (Fin n))) : ℝ :=
  levels.foldr (fun tr acc => uniformExpectedQueries p tr + acc) 0

/-- The leaf-weighted posterior entropy for a query tree initialized with the uniform prior. -/
noncomputable def uniformPosteriorEntropy {n : ℕ} (p : ℝ)
    (tr : BoolQueryTree (Fin n) (Fin n)) : ℝ :=
  treeLeaf p (fun a _ => entropy a) tr (uniformPosterior (n := n)) 1

/-- The leaf-weighted value of `postInfo` for a query tree initialized with the uniform prior. -/
noncomputable def uniformPosteriorInfo {n : ℕ} (p : ℝ)
    (tr : BoolQueryTree (Fin n) (Fin n)) : ℝ :=
  treeLeaf p (fun a _ => postInfo a) tr (uniformPosterior (n := n)) 1

/-- The leaf-weighted posterior error `1 - a o` of the reported output under the uniform prior. -/
noncomputable def uniformErrorProb {n : ℕ} (p : ℝ)
    (tr : BoolQueryTree (Fin n) (Fin n)) : ℝ :=
  treeLeaf p (fun a o => 1 - a o) tr (uniformPosterior (n := n)) 1

/-- Aggregates the weight of paths whose query count is at least the specified depth, using
Bayesian branch updates. -/
noncomputable def treeDeepProb {n : ℕ} (p : ℝ) (b : ℕ) :
    BoolQueryTree (Fin n) (Fin n) → (Fin n → ℝ) → ℝ → ℝ
  | .halt _, _, W => if b = 0 then W else 0
  | .ask c onFalse onTrue, a, W =>
      if b = 0 then W
      else treeDeepProb p (b - 1) onFalse (bayesFalsePost a c p) (W * bayesFalseNorm a c p)
        + treeDeepProb p (b - 1) onTrue (bayesTruePost a c p) (W * bayesTrueNorm a c p)

/-- The weight of query paths reaching depth `t` from the uniform prior and unit initial weight. -/
noncomputable def uniformTailProb {n : ℕ} (p : ℝ) (t : ℕ)
    (tr : BoolQueryTree (Fin n) (Fin n)) : ℝ :=
  treeDeepProb p t tr (uniformPosterior (n := n)) 1

/-- The rational likelihood of a Boolean comparison answer, with correctness parameter `p`. -/
noncomputable def answerLikelihoodRat {n : ℕ} (m c : Fin n) (p : ℚ) (b : Bool) : ℚ :=
  if b then (if (c : ℕ) ≤ (m : ℕ) then p else 1 - p) else (if (c : ℕ) ≤ (m : ℕ) then 1 - p else p)

/-- The product of rational answer likelihoods along a comparison record. -/
noncomputable def recordLikelihoodRat {n : ℕ} (p : ℚ) (t : Record n) (m : Fin n) : ℚ :=
  t.foldr (fun obs acc => answerLikelihoodRat m obs.1 p obs.2 * acc) 1

/-- The rational record likelihood normalized by its sum over all hidden cells. -/
noncomputable def recordPosteriorRat {n : ℕ} (p : ℚ) (t : Record n) (m : Fin n) : ℚ :=
  recordLikelihoodRat p t m / (∑ m', recordLikelihoodRat p t m')

/-- The least cell whose rational posterior is at least `ε`, with cell zero as a fallback. -/
noncomputable def haltCutRat {n : ℕ} (hn : 0 < n) (p ε : ℚ) (t : Record n) : Fin n :=
  if h : (Finset.univ.filter fun i : Fin n => ε ≤ recordPosteriorRat p t i).Nonempty then
    (Finset.univ.filter fun i : Fin n => ε ≤ recordPosteriorRat p t i).min' h
  else ⟨0, hn⟩

/-- The sum of rational posterior weights over cells with index at most `i`. -/
noncomputable def prefixMassRat {n : ℕ} (p : ℚ) (t : Record n) (i : Fin n) : ℚ :=
  ∑ j : Fin n, if j.val ≤ i.val then recordPosteriorRat p t j else 0

/-- The cells whose rational prefix mass lies in the interval `[1 / 2 - ε, 1 / 2)`. -/
noncomputable def cutSetRat {n : ℕ} (p : ℚ) (ε : ℚ) (t : Record n) : Finset (Fin n) :=
  Finset.univ.filter fun i => 1 / 2 - ε ≤ prefixMassRat p t i ∧ prefixMassRat p t i < 1 / 2

/-- The least cell in the rational stage-two cut set, with cell zero as a fallback. -/
noncomputable def stageTwoCutRat {n : ℕ} (hn : 0 < n) (p ε : ℚ) (t : Record n) : Fin n :=
  if h : (cutSetRat p ε t).Nonempty then (cutSetRat p ε t).min' h else ⟨0, hn⟩

/-- The rational stage-two cut selected for a comparison record. -/
noncomputable def cutAtRat {n : ℕ} (hn : 0 < n) (p ε : ℚ) (t : Record n) : Fin n :=
  stageTwoCutRat hn p ε t

/-- The predicate that an observation cut lies strictly above `k` and at most `i`. -/
def IsCrossing {n : ℕ} (k i : Fin n) (obs : Comparison n) : Prop :=
  k.val < obs.1.val ∧ obs.1.val ≤ i.val

/-- The number of true answers in a record whose cuts cross the interval from `k` to `i`. -/
noncomputable def crossTrue {n : ℕ} (k i : Fin n) : Record n → ℕ
  | [] => 0
  | obs :: t => (if IsCrossing k i obs ∧ obs.2 = true then 1 else 0) + crossTrue k i t

/-- The number of false answers in a record whose cuts cross the interval from `k` to `i`. -/
noncomputable def crossFalse {n : ℕ} (k i : Fin n) : Record n → ℕ
  | [] => 0
  | obs :: t => (if IsCrossing k i obs ∧ obs.2 = false then 1 else 0) + crossFalse k i t

/-- The cells for which the noiseless output of a query tree equals the hidden cell. -/
noncomputable def correctCells {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun j => noiselessOutput j tr = j

/-- The weighted sum of noiseless query depths over all hidden cells. -/
noncomputable def noiselessDepthSumW {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n))
    (w : Fin n → ℝ) : ℝ :=
  ∑ j, w j * noiselessQueries j tr

/-- The sum of noiseless query depths over all hidden cells. -/
noncomputable def noiselessDepthSum {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n)) : ℝ :=
  noiselessDepthSumW tr (fun _ => 1)

/-- The sum of noiseless query depths divided by the number of cells. -/
noncomputable def noiselessMeanQueries {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n)) : ℝ :=
  noiselessDepthSum tr / n

/-- The cells whose noiseless query depth is strictly greater than `t`. -/
noncomputable def cellsAboveDepth {n : ℕ} (tr : BoolQueryTree (Fin n) (Fin n)) (t : ℕ) :
    Finset (Fin n) :=
  Finset.univ.filter fun j => t < noiselessQueries j tr

/-- The number of true crossing answers minus the number of false crossing answers, as a real
number. -/
noncomputable def crossScore {n : ℕ} (k i : Fin n) (t : Record n) : ℝ :=
  (crossTrue k i t : ℝ) - (crossFalse k i t : ℝ)

/-- The total number of crossing answers, as a real number. -/
noncomputable def crossCount {n : ℕ} (k i : Fin n) (t : Record n) : ℝ :=
  (crossTrue k i t : ℝ) + (crossFalse k i t : ℝ)

/-- The crossing score of one observation: one for a true crossing answer, negative one for a
false crossing answer, and zero otherwise. -/
noncomputable def stepScore {n : ℕ} (k i : Fin n) (obs : Comparison n) : ℝ :=
  if IsCrossing k i obs then (if obs.2 then 1 else -1) else 0

/-- The indicator that one observation cut crosses the interval from `k` to `i`. -/
noncomputable def stepCount {n : ℕ} (k i : Fin n) (obs : Comparison n) : ℝ :=
  if IsCrossing k i obs then 1 else 0

/-- The crossing score minus `(1 - 2 * p)` times the crossing count. -/
noncomputable def crossMartingale {n : ℕ} (p : ℝ) (k i : Fin n) (t : Record n) : ℝ :=
  crossScore k i t - (1 - 2 * p) * crossCount k i t

/-- Recursively accumulates the crossing variance contribution `4 * p * (1 - p)` along the
adaptive tree under hidden cell `u`. -/
noncomputable def treeCrossVar {n : ℕ} (hn : 0 < n) (p ε : ℝ) (u k i : Fin n)
    : ℕ → Record n → ℝ
  | 0, t => 0
  | m + 1, t =>
      ∑ b : Bool, stepWeight hn p ε u t b
        * treeCrossVar hn p ε u k i m (extend hn p ε t b)
      + (if IsCrossing k i (cutAt hn p ε t, true) then 4 * p * (1 - p) else 0)

/-- The cells with index strictly above `i` and at most `i + l`. -/
def windowCellsAbove {n : ℕ} (i : Fin n) (l : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun j => (i : ℕ) < (j : ℕ) ∧ (j : ℕ) ≤ (i : ℕ) + l

/-- The number of false crossing answers minus the number of true crossing answers above `i`. -/
noncomputable def upperScore {n : ℕ} (i k : Fin n) (t : Record n) : ℝ :=
  (crossFalse i k t : ℝ) - (crossTrue i k t : ℝ)

/-- The upper crossing score of one observation, equal to negative one for a true crossing
answer and one for a false crossing answer. -/
noncomputable def stepUpperScore {n : ℕ} (i k : Fin n) (obs : Comparison n) : ℝ :=
  if IsCrossing i k obs then (if obs.2 then -1 else 1) else 0

/-- The upper crossing score plus `(2 * p - 1)` times the crossing count. -/
noncomputable def upperMartingale {n : ℕ} (p : ℝ) (i k : Fin n) (t : Record n) : ℝ :=
  upperScore i k t + (2 * p - 1) * crossCount i k t

/-- The list of cut indices appearing in a comparison record. -/
noncomputable def cutList {n : ℕ} : Record n → List (Fin n)
  | [] => []
  | obs :: t => obs.1 :: cutList t

/-- Requires every observation cut to be absent from the remaining tail, recursively. -/
def NoDupCuts {n : ℕ} : Record n → Prop
  | [] => True
  | obs :: t => obs.1 ∉ cutList t ∧ NoDupCuts t

/-- The predicate `u + l < i` on cell indices. -/
abbrev TruthBelowWindow {n : ℕ} (u i : Fin n) (l : ℕ) : Prop :=
  (u : ℕ) + l < (i : ℕ)

/-- The predicate `i + l < u` on cell indices. -/
abbrev TruthAboveWindow {n : ℕ} (u i : Fin n) (l : ℕ) : Prop :=
  (i : ℕ) + l < (u : ℕ)

/-- The disjunction that the hidden cell lies strictly below or strictly above the specified
window. -/
abbrev TruthOutsideWindow {n : ℕ} (u i : Fin n) (l : ℕ) : Prop :=
  TruthBelowWindow u i l ∨ TruthAboveWindow u i l

/-- A query tree together with a comparison record for one search level. -/
structure Level (n : ℕ) where

  program : BoolQueryTree (Fin n) (Fin n)

  record : Record n

/-- A finite list of search levels, each containing a program and a record. -/
abbrev RecursiveRun (n : ℕ) := List (Level n)

/-- Checks a record against successive query cuts and branches, returning the output and query
count exactly when the record ends at a leaf. -/
noncomputable def programRun {n : ℕ} :
    BoolQueryTree (Fin n) (Fin n) → Record n → Option (Fin n × ℕ)
  | .halt o, [] => some (o, 0)
  | .halt _, _ :: _ => none
  | .ask _ _ _, [] => none
  | .ask c onFalse onTrue, obs :: rest =>
      if obs.1 = c then
        (programRun (if obs.2 then onTrue else onFalse) rest).map (fun (o, k) => (o, k + 1))
      else none

/-- Requires a level's record to execute its program to some output with query count equal to
the record length. -/
def LevelExecuted {n : ℕ} (l : Level n) : Prop :=
  ∃ o : Fin n, programRun l.program l.record = some (o, l.record.length)

/-- The sum of record lengths along a recursive run. -/
noncomputable def recursivePathOracleApplications {n : ℕ} (run : RecursiveRun n) : ℕ :=
  (run.map fun l => l.record.length).sum

/-- The sum of uniform-prior expected query counts of the programs along a recursive run. -/
noncomputable def recursivePathExpectedOracleApplications {n : ℕ} (p : ℝ)
    (run : RecursiveRun n) : ℝ :=
  (run.map fun l => uniformExpectedQueries p l.program).sum

/-- The sign-valued threshold function equal to negative one below `j` and one otherwise. -/
def fggsThreshold {N : ℕ} (j : ℕ) (x : Fin N) : ℝ := if x.val < j then -1 else 1

/-- The doubled threshold function whose second half is the negative of its first half. -/
def fggsFull {N : ℕ} (j : ℕ) (x : Fin (2 * N)) : ℝ :=
  if x.val < N then (if x.val < j then -1 else 1) else (if x.val - N < j then 1 else -1)

/-- The cyclic predecessor on `Fin (2 * N)`, wrapping zero to `2 * N - 1`. -/
def fggsPred {N : ℕ} (hN : 0 < N) (x : Fin (2 * N)) : Fin (2 * N) :=
  if 0 < x.val then ⟨x.val - 1, Nat.sub_lt_of_lt x.isLt⟩ else
    ⟨2 * N - 1, by omega⟩

/-- The cyclic successor on `Fin (2 * N)`. -/
def fggsSucc {N : ℕ} (hN : 0 < N) (x : Fin (2 * N)) : Fin (2 * N) :=
  ⟨(x.val + 1) % (2 * N), Nat.mod_lt _ (by omega)⟩

/-- Iterates the cyclic successor the specified number of times. -/
def fggsSuccN {N : ℕ} (hN : 0 < N) : ℕ → Fin (2 * N) → Fin (2 * N)
  | 0, x => x
  | k + 1, x => fggsSuccN hN k (fggsSucc hN x)

/-- The cyclic report weight `Q (h - iv)` for hidden index `iv` and report `h`. -/
noncomputable def fggsReportProb {K : ℕ} (Q : Fin K → ℝ) (iv h : Fin K) : ℝ := Q (h - iv)

/-- The posterior proportional to `a iv * Q (h - iv)` after observing cyclic report `h`. -/
noncomputable def fggsPosterior {K : ℕ} (a : Fin K → ℝ) (Q : Fin K → ℝ) (h : Fin K) :
    Fin K → ℝ :=
  fun iv => a iv * Q (h - iv) / (∑ iv', a iv' * Q (h - iv'))

/-- The report weights obtained by summing `a iv * Q (h - iv)` over hidden indices. -/
noncomputable def fggsReportMarginal {K : ℕ} (a : Fin K → ℝ) (Q : Fin K → ℝ) : Fin K → ℝ :=
  fun h => ∑ iv, a iv * Q (h - iv)

/-- The constant prior weight `1 / K` on `Fin K`. -/
noncomputable def fggsUniformPrior {K : ℕ} : Fin K → ℝ := fun _ => 1 / K

/-- The entropy expression `-∑ i, P i * log (P i)` in natural logarithm units. -/
noncomputable def fggsEntropyNat {K : ℕ} (P : Fin K → ℝ) : ℝ := -(∑ i, P i * Real.log (P i))

/-- The entropy expression `fggsEntropyNat` converted to bits. -/
noncomputable def fggsEntropy {K : ℕ} (P : Fin K → ℝ) : ℝ := fggsEntropyNat P / Real.log 2

/-- The cyclic channel information expression `log₂ K - fggsEntropy Q`. -/
noncomputable def fggsMultiInfo {K : ℕ} (Q : Fin K → ℝ) : ℝ :=
  Real.log K / Real.log 2 - fggsEntropy Q

/-- The report-weighted posterior relative entropy with respect to the prior, using natural
logarithms. -/
noncomputable def fggsMutualInfoNat {K : ℕ} (a : Fin K → ℝ) (Q : Fin K → ℝ) : ℝ :=
  ∑ h, fggsReportMarginal a Q h *
    (∑ iv, fggsPosterior a Q h iv * Real.log (fggsPosterior a Q h iv / a iv))

/-- The report-weighted posterior relative entropy with respect to the prior, converted to bits. -/
noncomputable def fggsMutualInfo {K : ℕ} (a : Fin K → ℝ) (Q : Fin K → ℝ) : ℝ :=
  fggsMutualInfoNat a Q / Real.log 2

end Qatlib.Concepts.OrderedBayes.BayesRatioCore

end

set_option autoImplicit false
