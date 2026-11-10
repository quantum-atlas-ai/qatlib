/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState
open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Papers.AdaptiveTest26.MainResults

set_option autoImplicit false

open scoped BigOperators
open scoped ComplexOrder

variable {D O : ℕ}

noncomputable def RootFidelity (ρ σ : Operator D) : ℝ :=
  SchattenOne (cfc Real.sqrt ρ * cfc Real.sqrt σ)

def IsH1 (ε : ℝ) (ρ σ : Operator D) : Prop :=
  RootFidelity ρ σ ≤ 1 - ε

noncomputable def SuccessFloor : ℝ := (99 : ℝ) / 100

abbrev PovmEffects (D O : ℕ) := Fin O → Operator D

def IsPovmEffects {D O : ℕ} (E : PovmEffects D O) : Prop :=
  (∀ i : Fin O, (E i).PosSemidef) ∧ ∑ i : Fin O, E i = 1

noncomputable def outcomeProb {D O : ℕ} (E : PovmEffects D O)
    (ρ : Operator D) (i : Fin O) : ℝ :=
  ((E i * ρ).trace).re

inductive StreamTag where
  | rho
  | sigma
  deriving DecidableEq, Repr

def stateFor {D : ℕ} (tag : StreamTag) (ρ σ : Operator D) : Operator D :=
  match tag with
  | .rho => ρ
  | .sigma => σ

abbrev OutcomeRecord (O steps : ℕ) := Fin steps → Fin O

structure NonAdaptiveStrategy (D O : ℕ) where

  steps : ℕ

  stream : Fin steps → StreamTag

  povm : Fin steps → PovmEffects D O

  decide : OutcomeRecord O steps → Bool

def IsAdmissibleNonAdaptive {D O : ℕ} (S : NonAdaptiveStrategy D O) : Prop :=
  ∀ t : Fin S.steps, IsPovmEffects (S.povm t)

noncomputable def nonAdaptiveAcceptProb {D O : ℕ} (S : NonAdaptiveStrategy D O)
    (ρ σ : Operator D) : ℝ :=
  ∑ h : OutcomeRecord O S.steps,
    (if S.decide h then 1 else 0) *
      ∏ t : Fin S.steps,
        outcomeProb (S.povm t) (stateFor (S.stream t) ρ σ) (h t)

noncomputable def sharedNullAcceptProb {D O : ℕ} (S : NonAdaptiveStrategy D O)
    (ρ : Operator D) : ℝ :=
  nonAdaptiveAcceptProb S ρ ρ

structure RandomizedNonAdaptiveStrategy (D O : ℕ) where

  support : ℕ

  weight : Fin support → ℝ

  component : Fin support → NonAdaptiveStrategy D O

  weight_nonneg : ∀ i : Fin support, 0 ≤ weight i

  weight_sum : ∑ i : Fin support, weight i = 1

def IsAdmissibleRandomizedNonAdaptive {D O : ℕ}
    (S : RandomizedNonAdaptiveStrategy D O) : Prop :=
  ∀ i : Fin S.support, IsAdmissibleNonAdaptive (S.component i)

noncomputable def randomizedAcceptProb {D O : ℕ}
    (S : RandomizedNonAdaptiveStrategy D O) (ρ σ : Operator D) : ℝ :=
  ∑ i : Fin S.support, S.weight i * nonAdaptiveAcceptProb (S.component i) ρ σ

noncomputable def randomizedSharedNullAcceptProb {D O : ℕ}
    (S : RandomizedNonAdaptiveStrategy D O) (ρ : Operator D) : ℝ :=
  randomizedAcceptProb S ρ ρ

def IsCorrectNonAdaptiveEquivalenceTester {D O : ℕ}
    (S : RandomizedNonAdaptiveStrategy D O) (ε : ℝ) : Prop :=
  IsAdmissibleRandomizedNonAdaptive S ∧
    (∀ ρ : Operator D, IsDensityOperator ρ →
      SuccessFloor ≤ randomizedSharedNullAcceptProb S ρ) ∧
    (∀ ρ σ : Operator D, IsDensityOperator ρ → IsDensityOperator σ →
      IsH1 ε ρ σ → randomizedAcceptProb S ρ σ ≤ 1 - SuccessFloor)

structure CopyLedger where

  rho : ℕ

  sigma : ℕ

def CopyLedger.total (c : CopyLedger) : ℕ := c.rho + c.sigma

def NonAdaptiveStrategy.ledger {D O : ℕ} (S : NonAdaptiveStrategy D O) : CopyLedger where
  rho := (Finset.univ.filter (fun t : Fin S.steps => S.stream t = .rho)).card
  sigma := (Finset.univ.filter (fun t : Fin S.steps => S.stream t = .sigma)).card

def RandomizedNonAdaptiveStrategy.worstLedger {D O : ℕ}
    (S : RandomizedNonAdaptiveStrategy D O) : CopyLedger where
  rho := Finset.univ.sup (fun i : Fin S.support => (S.component i).ledger.rho)
  sigma := Finset.univ.sup (fun i : Fin S.support => (S.component i).ledger.sigma)

def RandomizedNonAdaptiveStrategy.worstTotalCopies {D O : ℕ}
    (S : RandomizedNonAdaptiveStrategy D O) : ℕ :=
  Finset.univ.sup (fun i : Fin S.support => (S.component i).steps)

structure AdaptiveStrategy (D O : ℕ) where

  steps : ℕ

  stream : (t : Fin steps) → (Fin t.val → Fin O) → StreamTag

  povm : (t : Fin steps) → (Fin t.val → Fin O) → PovmEffects D O

  decide : OutcomeRecord O steps → Bool

def recordPrefix {O steps : ℕ} (h : OutcomeRecord O steps) (t : Fin steps) :
    Fin t.val → Fin O :=
  fun u => h ⟨u.val, lt_trans u.2 t.2⟩

def IsAdmissibleAdaptive {D O : ℕ} (S : AdaptiveStrategy D O) : Prop :=
  ∀ (t : Fin S.steps) (hist : Fin t.val → Fin O), IsPovmEffects (S.povm t hist)

noncomputable def adaptiveAcceptProb {D O : ℕ} (S : AdaptiveStrategy D O)
    (ρ σ : Operator D) : ℝ :=
  ∑ h : OutcomeRecord O S.steps,
    (if S.decide h then 1 else 0) *
      ∏ t : Fin S.steps,
        outcomeProb (S.povm t (recordPrefix h t))
          (stateFor (S.stream t (recordPrefix h t)) ρ σ) (h t)

noncomputable def adaptiveSharedNullAcceptProb {D O : ℕ} (S : AdaptiveStrategy D O)
    (ρ : Operator D) : ℝ :=
  adaptiveAcceptProb S ρ ρ

def IsCorrectAdaptiveEquivalenceTester {D O : ℕ} (S : AdaptiveStrategy D O)
    (ε : ℝ) : Prop :=
  IsAdmissibleAdaptive S ∧
    (∀ ρ : Operator D, IsDensityOperator ρ →
      SuccessFloor ≤ adaptiveSharedNullAcceptProb S ρ) ∧
    (∀ ρ σ : Operator D, IsDensityOperator ρ → IsDensityOperator σ →
      IsH1 ε ρ σ → adaptiveAcceptProb S ρ σ ≤ 1 - SuccessFloor)

def AdaptiveStrategy.rhoUses {D O : ℕ} (S : AdaptiveStrategy D O)
    (h : OutcomeRecord O S.steps) : ℕ :=
  (Finset.univ.filter
    (fun t : Fin S.steps => S.stream t (recordPrefix h t) = .rho)).card

def AdaptiveStrategy.sigmaUses {D O : ℕ} (S : AdaptiveStrategy D O)
    (h : OutcomeRecord O S.steps) : ℕ :=
  (Finset.univ.filter
    (fun t : Fin S.steps => S.stream t (recordPrefix h t) = .sigma)).card

def AdaptiveStrategy.worstLedger {D O : ℕ} (S : AdaptiveStrategy D O) : CopyLedger where
  rho := Finset.univ.sup (fun h : OutcomeRecord O S.steps => S.rhoUses h)
  sigma := Finset.univ.sup (fun h : OutcomeRecord O S.steps => S.sigmaUses h)

def IsTildeOBound (N : ℕ) (B : ℝ) (d ε : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, (N : ℝ) ≤ C * B * (Real.log (d / ε)) ^ k

def IsTildeOmegaLowerBound (N : ℕ) (B : ℝ) (d ε : ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ k : ℕ, c * B / (Real.log (d / ε)) ^ k ≤ (N : ℝ)

def InPowerLawRegime (d : ℕ) (ε α : ℝ) : Prop :=
  2 ≤ d ∧ ε = (d : ℝ) ^ (-α)

noncomputable def nonAdaptiveLowerBoundTarget (d : ℕ) (ε : ℝ) : ℝ :=
  (d : ℝ) ^ ((3 : ℝ) / 2) / ε ^ 2

noncomputable def adaptiveEquivalenceBudget (d : ℕ) (ε : ℝ) : ℝ :=
  min (nonAdaptiveLowerBoundTarget d ε) ((d : ℝ) ^ ((9 : ℝ) / 4) / ε)

end Qatlib.Papers.AdaptiveTest26.MainResults
