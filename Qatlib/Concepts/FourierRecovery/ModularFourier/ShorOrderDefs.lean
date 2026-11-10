/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FourierRecovery.ModularFourier.ShorOrder
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PeriodSampling.OrderRecovery
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation
open Qatlib.Concepts.FourierRecovery.ModularFourier.ShorOrder
open Qatlib.Concepts.PeriodSampling.OrderRecovery

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Qatlib.Concepts.FourierRecovery.ModularFourier

open Qatlib
open Matrix
open scoped Classical BigOperators ComplexConjugate ENNReal

def shorUnitThree : (ZMod 4)ˣ := ⟨3, 3, by decide, by decide⟩

def shorFermatScreen (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) : Bool :=
  decide (a ^ (N - 1) = 1)

def shorFermatScreenBitCost (N : ℕ) : ℕ :=
  schoolbookMulModCost (orderBitLength N) * (orderBitLength N + 1)

def shorModExpBitCost (N : ℕ) : ℕ :=
  (orderBitLength N + 1) * schoolbookMulModCost (orderBitLength N)

def shorCfStepBound (N : ℕ) : ℕ := N + 1

def shorCfBitCost (N : ℕ) : ℕ :=
  shorCfStepBound N * euclidStepBound (orderBitLength N) * orderBitLength N

structure ShorSuccessReceipt (N M : ℕ) [NeZero N] where

  index : ℕ

  factor : ℕ

  attempts : ℕ
  deriving DecidableEq, Repr

def shorSuccessReceipt {N M R : ℕ} [NeZero N] (ω : Fin R → AttemptOutcome N M)
    (j : Fin R) : ShorSuccessReceipt N M where
  index := j.val
  factor := (attemptOutcomeFactor N M (ω j)).getD 0
  attempts := j.val + 1

def shorCompactWidth (m : ℕ) : ℕ := compactRecordWidth m

def shorAspUniformCost (m : ℕ) : ℕ := m * (shorCompactWidth m + 1)

def shorSmallPrimePowers (m : ℕ) : ℕ := (smallPrimePowers m).card

def clause9_endpoint : Prop :=
  (∀ (N : ℕ) [NeZero N] (hp : Nat.Prime N) (a : (ZMod N)ˣ),
      shorFermatScreen N a = true)
  ∧ (shorFermatScreen 4 shorUnitThree = false)
  ∧ (∀ N : ℕ, shorFermatScreenBitCost N ≤ polyLogBound 1 6 N)
  ∧ (∀ N : ℕ, preprocessBitCost N ≤ polyLogBound 1 4 N)
  ∧ (∀ (N d : ℕ), evenDivisor N = some d → 1 < d ∧ d < N ∧ d ∣ N)
  ∧ (∀ (N d : ℕ), perfectPowerDivisor N = some d → 1 < d ∧ d < N ∧ d ∣ N)
  ∧ (∀ (N : ℕ) [NeZero N] (hp : Nat.Prime N) (a : (ZMod N)ˣ), PrimeDirectionWitness N a)

def thresholdGoal_endpoint : Prop :=
  (∀ n : ℕ, GateCount (localProgramCircuit (localQFT n)) = localQftGateCount n ∧
      QueryCount (localProgramCircuit (localQFT n)) = 0 ∧
      localQftSpaceCost n = n)
  ∧ (∀ (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0 < M),
      QueryCount (modularOrderCircuit N M a) = M * (M - 1) / 2 ∧
        GateCount (modularOrderCircuit N M a) = M * (M - 1) + 2)
  ∧ (∀ (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) (q : ℕ),
      orderVerificationProduct N a q = a ^ q)
  ∧ (∀ (a b : ℕ), (euclidCounted a b).1 = Nat.gcd a b ∧ (euclidCounted a b).2 ≤ b)
  ∧ (∀ N : ℕ, euclidBitCost (orderBitLength N) ≤ polyLogBound 1 5 N)
  ∧ (∀ N : ℕ, shorModExpBitCost N ≤ polyLogBound 1 6 N)
  ∧ (∀ N : ℕ, shorCfBitCost N
      = (N + 1) * euclidStepBound (orderBitLength N) * orderBitLength N)
  ∧ (∀ (N M k : ℕ), (rejectedLedger k).bits ≤ (attemptLedgerBound N M k).bits ∧
      (rejectedLedger k).queries ≤ (attemptLedgerBound N M k).queries ∧
      (rejectedLedger k).gates ≤ (attemptLedgerBound N M k).gates ∧
      (rejectedLedger k).space ≤ (attemptLedgerBound N M k).space)

def clause11_endpoint : Prop :=
  (∀ (N M : ℕ) [NeZero N] (t : AttemptOutcome N M) (d : ℕ),
      attemptOutcomeFactor N M t = some d → 1 < d ∧ d < N ∧ d ∣ N)
  ∧ (∀ (N M R : ℕ) [NeZero N] (ω : Fin R → AttemptOutcome N M) (j : Fin R),
      firstSuccessAt (N := N) (M := M) (R := R) ω j →
        (attemptOutcomeFactor N M (ω j)).isSome ∧
          (shorSuccessReceipt ω j).index = j.val ∧
          (shorSuccessReceipt ω j).attempts = j.val + 1 ∧
          1 < (shorSuccessReceipt ω j).factor ∧ (shorSuccessReceipt ω j).factor < N)
  ∧ (∀ (split : ∀ n, Option (ProperDivisor n)) (n : ℕ),
      (∀ m, 2 ≤ m → m ≤ n → ∀ h : ¬Nat.Prime m, split m ≠ none) →
        (factorTreeOf split n).complete)

def clause12_endpoint : Prop :=
  (∀ (G : Type) [Fintype G] [DecidableEq G], HasCompactEncoding G)
  ∧ (∀ (Ω H : Type) [Fintype Ω] [Fintype H] (V : Matrix H Ω ℂ) (T : Matrix Ω Ω ℂ),
      ComputationIsometry V → (V * T * Vᴴ) * V = V * T)
  ∧ (∀ (Ω H : Type) [Fintype Ω] [Fintype H] (V : Matrix H Ω ℂ) (T : Matrix Ω Ω ℂ)
      (φ : QState H),
      (V * T * Vᴴ) *ᵥ φ = V *ᵥ (T *ᵥ (Vᴴ *ᵥ φ)))
  ∧ (∀ (G : Type*) [AddCommGroup G] [Fintype G] [DecidableEq G],
      (orbitFourierMatrix G)ᴴ * orbitFourierMatrix G = (1 : Matrix G G ℂ))
  ∧ (∀ m : ℕ, m ≠ 0 → m ≤ 2 ^ shorCompactWidth m)
  ∧ (∀ m : ℕ, m ≠ 0 → shorAspUniformCost m = m * (shorCompactWidth m + 1))

def clause13_endpoint : Prop :=
  (∀ N : ℕ, 1 < N → ∃ q, OriginalClockWindow N q)
  ∧ (∀ (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0 < M) (hN : 1 < N)
      (hr : 1 < orderOf a) (hsize : 2 * N ^ 2 < M),
      0 < orderGoodMass N M a hM)
  ∧ (∀ (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0 < M) (hN : 1 < N)
      (hr : 1 < orderOf a) (hsize : 2 * N ^ 2 < M) (y : Fin M),
      (orderConditionalLaw N M a hM (orderGoodMass_pos N M a hM hN hr hsize)).prob y
        = if OrderGoodEvent N M a y then
            (modularOrderLaw N M a hM).prob y / orderGoodMass N M a hM else 0)
  ∧ (∀ (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0 < M) (hN : 1 < N)
      (hr : 1 < orderOf a) (hsize : 2 * N ^ 2 < M),
      (∑ y : Fin M, (orderConditionalLaw N M a hM
        (orderGoodMass_pos N M a hM hN hr hsize)).prob y) = 1)
  ∧ (∀ m w : ℕ, w ∈ smallPrimePowers m → w ∣ m)
  ∧ (∀ m : ℕ, shorSmallPrimePowers m = (smallPrimePowers m).card)

end Qatlib.Concepts.FourierRecovery.ModularFourier
