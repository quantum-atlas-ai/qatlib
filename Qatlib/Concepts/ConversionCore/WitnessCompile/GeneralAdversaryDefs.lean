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
set_option warningAsError false
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

structure AdaptiveRound (O : Type*) [Fintype O] (n D : ℕ) where

  inst : Instrument O D D

  coord : O → Fin n

structure AlphabetAdaptive (O : Type*) [Fintype O] (n D : ℕ) where

  rounds : ℕ

  round : Fin rounds → AdaptiveRound O n D

  alpha : ℕ

def AlphabetAdaptive.Correct {O : Type*} [Fintype O] {n D : ℕ}
    (s : AlphabetAdaptive O n D) : Prop :=
  0 < s.alpha ∧ 0 < n ∧ 0 < D

structure UnboundedAdversary (S O : Type) [Fintype S] [DecidableEq S]
    [Fintype O] [DecidableEq O] where

  next : S → PMF (Configuration S O)

def UnboundedAdversary.MassConserved {S O : Type} [Fintype S] [DecidableEq S]
    [Fintype O] [DecidableEq O] (u : UnboundedAdversary S O)
    (cfg : Configuration S O) : Prop :=
  (∑' z : Option (O × ℕ), unboundedMass u.next cfg z) = 1

def UnboundedAdversary.TailTruncated {S O : Type} [Fintype S] [DecidableEq S]
    [Fintype O] [DecidableEq O] (u : UnboundedAdversary S O)
    (cfg : Configuration S O) (tol : ℝ≥0∞) : Prop :=
  nonterminationMass u.next cfg ≤ tol

def ZenoRun {S : Type*} (step : S → CostedLaw S) (s : ℕ → S) : Prop :=
  (∀ k : ℕ, (step (s k)).support.Nonempty) ∧
    (∑' k : ℕ, Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectedCost (step (s k))) < ⊤

structure AdversaryResources where

  inputLen : ℕ

  gates : ℕ

  space : ℕ

def AdversaryResources.PolyBounded (x : AdversaryResources) : Prop :=
  ∃ C e : ℕ, x.gates ≤ C * (x.inputLen + 1) ^ e ∧ x.space ≤ C * (x.inputLen + 1) ^ e

structure NativeTMFamily (Γ Λ : Type*) [Inhabited Γ] [Inhabited Λ] where

  machine : ℕ → Turing.TM0.Machine Γ Λ

def NativeTMFamily.UniformPolyTime {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    [Fintype Γ] [Fintype Λ] (f : NativeTMFamily Γ Λ) : Prop :=
  ∃ c k : ℕ, ∀ (len : ℕ) (input : List Γ), input.length = len →
    ∃ t : ℕ, t ≤ c * len ^ k + c ∧ BitMachineHaltsAt (f.machine len) input t

structure BooleanSlice (X : Type*) [Fintype X] where

  f : X → Bool

  depth : ℕ

def fixedTreeNotGeneralEndpoint : Prop :=
  ∀ (n D : ℕ) (O : Type) [Fintype O], 0 < n → 0 < D →
    ∃ s : AlphabetAdaptive O n D, AlphabetAdaptive.Correct s

end Qatlib.Concepts.ConversionCore.WitnessCompile
