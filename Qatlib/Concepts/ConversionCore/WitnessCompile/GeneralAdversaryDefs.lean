/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.LinearLearning.ConcisePipeline.RandomizedCost
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
import Qatlib.Concepts.StoppingCore.BranchCostCore.UnboundedFiniteExecution
import Qatlib.Concepts.ClassicalTape.TapeCompilation.BitMachineTime
import Qatlib.Concepts.QueryWordCore.QueryMachinery.NegativeAdversary
import Qatlib.Concepts.QueryComplexity.DegreeMethod.AlphabetInterrogation
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription

/-!
# Definitions for general adversary bookkeeping

This module introduces records for alphabet-adaptive rounds, probabilistic unbounded executions,
resource counts, and families of native Turing machines. Their accompanying predicates express
parameter positivity, mass conservation, nontermination-tail bounds, finite total expected cost,
and polynomial bounds.

These definitions support the execution-accounting statements surrounding the general adversary
framework of [LeeEtAl2011]. `AlphabetAdaptive.Correct` records only positivity of the alphabet
parameter, coordinate count, and state dimension.

## Main statements

* `AlphabetAdaptive` and `AlphabetAdaptive.Correct`: finite round data and parameter positivity.
* `UnboundedAdversary`: probabilistic continuation data.
* `NativeTMFamily.UniformPolyTime`: a uniform polynomial halting-time bound.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

set_option autoImplicit false

noncomputable section

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.ClassicalTape.TapeCompilation

namespace Qatlib.Concepts.ConversionCore.WitnessCompile

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RandomizedExecution
open scoped Classical ENNReal

/-- An adaptive round consisting of a quantum instrument and an outcome-dependent choice of
input coordinate. -/
structure AdaptiveRound (O : Type*) [Fintype O] (n D : ℕ) where

  inst : Instrument O D D

  coord : O → Fin n

/-- A finite sequence of adaptive rounds together with a natural alphabet parameter. -/
structure AlphabetAdaptive (O : Type*) [Fintype O] (n D : ℕ) where

  rounds : ℕ

  round : Fin rounds → AdaptiveRound O n D

  alpha : ℕ

/-- Positivity of the alphabet parameter, input coordinate count, and state dimension of an
alphabet-adaptive object. -/
def AlphabetAdaptive.Correct {O : Type*} [Fintype O] {n D : ℕ}
    (s : AlphabetAdaptive O n D) : Prop :=
  0 < s.alpha ∧ 0 < n ∧ 0 < D

/-- A probabilistic continuation rule assigning a distribution of configurations to each
internal state. -/
structure UnboundedAdversary (S O : Type) [Fintype S] [DecidableEq S]
    [Fintype O] [DecidableEq O] where

  next : S → PMF (Configuration S O)

/-- The condition that the total unbounded execution mass, including all optional
outcome-and-cost values, equals one. -/
def UnboundedAdversary.MassConserved {S O : Type} [Fintype S] [DecidableEq S]
    [Fintype O] [DecidableEq O] (u : UnboundedAdversary S O)
    (cfg : Configuration S O) : Prop :=
  (∑' z : Option (O × ℕ), unboundedMass u.next cfg z) = 1

/-- The condition that the nontermination mass from `cfg` is at most the specified tolerance. -/
def UnboundedAdversary.TailTruncated {S O : Type} [Fintype S] [DecidableEq S]
    [Fintype O] [DecidableEq O] (u : UnboundedAdversary S O)
    (cfg : Configuration S O) (tol : ℝ≥0∞) : Prop :=
  nonterminationMass u.next cfg ≤ tol

/-- The condition that each step law along the state sequence has nonempty support and that the
sum of its expected costs is finite. -/
def ZenoRun {S : Type*} (step : S → CostedLaw S) (s : ℕ → S) : Prop :=
  (∀ k : ℕ, (step (s k)).support.Nonempty) ∧
    (∑' k : ℕ, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (step (s k))) < ⊤

/-- A resource record containing the input length, gate count, and space count. -/
structure AdversaryResources where

  inputLen : ℕ

  gates : ℕ

  space : ℕ

/-- The existence of natural constants bounding both gate count and space count by a polynomial
in one plus the recorded input length. -/
def AdversaryResources.PolyBounded (x : AdversaryResources) : Prop :=
  ∃ C e : ℕ, x.gates ≤ C * (x.inputLen + 1) ^ e ∧ x.space ≤ C * (x.inputLen + 1) ^ e

/-- A family of native Turing machines indexed by input length. -/
structure NativeTMFamily (Γ Λ : Type*) [Inhabited Γ] [Inhabited Λ] where

  machine : ℕ → Turing.TM0.Machine Γ Λ

/-- The existence of common natural constants `c` and `k` such that the machine for length `len`
halts on every input of that length within `c*len^k+c` steps. -/
def NativeTMFamily.UniformPolyTime {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    [Fintype Γ] [Fintype Λ] (f : NativeTMFamily Γ Λ) : Prop :=
  ∃ c k : ℕ, ∀ (len : ℕ) (input : List Γ), input.length = len →
    ∃ t : ℕ, t ≤ c * len ^ k + c ∧ BitMachineHaltsAt (f.machine len) input t

/-- A Boolean-valued function on a finite input type together with a natural depth parameter. -/
structure BooleanSlice (X : Type*) [Fintype X] where

  f : X → Bool

  depth : ℕ

/-- The statement that every positive coordinate count and state dimension possess an
alphabet-adaptive object satisfying `AlphabetAdaptive.Correct`. -/
def fixedTreeNotGeneralEndpoint : Prop :=
  ∀ (n D : ℕ) (O : Type) [Fintype O], 0 < n → 0 < D →
    ∃ s : AlphabetAdaptive O n D, AlphabetAdaptive.Correct s

end Qatlib.Concepts.ConversionCore.WitnessCompile
