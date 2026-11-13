/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FourierRecovery.ModularFourier.ShorOrder

/-!
# Refined Shor bookkeeping definitions

This module defines `shorFermatScreen`, bit cost expressions, and `ShorSuccessReceipt` for
recording attempt indices and extracted factors in the order finding approach of [Shor1997]. It
also introduces aliases for compact record width and explicit counts for uniform preparation and
small prime powers.

The propositions `clause9_endpoint`, `thresholdGoal_endpoint`, and `clause11_endpoint` through
`clause13_endpoint` collect the screening, resource, factor extraction, encoding, and
conditional recovery statements proved in `ShorOrderRefined`.

## Main statements

* `shorFermatScreen`: tests whether a modular unit satisfies `a ^ (N - 1) = 1`.
* `ShorSuccessReceipt`: stores the attempt index, extracted factor, and number of attempts.
* `thresholdGoal_endpoint`: packages the circuit and classical processing resource statements.
* `clause13_endpoint`: packages the clock window and conditional recovery distribution
  statements.

## References

* [Shor, 1997][Shor1997]
-/

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

noncomputable section

namespace Qatlib.Concepts.FourierRecovery.ModularFourier

open Qatlib
open Matrix
open scoped Classical BigOperators ComplexConjugate ENNReal

/-- The unit represented by three modulo four, with inverse three. -/
def shorUnitThree : (ZMod 4)ˣ := ⟨3, 3, by decide, by decide⟩

/-- The Boolean test for the Fermat congruence `a ^ (N - 1) = 1` for a unit modulo the nonzero
modulus `N`. -/
def shorFermatScreen (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) : Bool :=
  decide (a ^ (N - 1) = 1)

/-- The screening bit cost modeled by the schoolbook modular multiplication cost times
`orderBitLength N + 1`. -/
def shorFermatScreenBitCost (N : ℕ) : ℕ :=
  schoolbookMulModCost (orderBitLength N) * (orderBitLength N + 1)

/-- The modular exponentiation bit cost modeled by `orderBitLength N + 1` schoolbook modular
multiplications. -/
def shorModExpBitCost (N : ℕ) : ℕ :=
  (orderBitLength N + 1) * schoolbookMulModCost (orderBitLength N)

/-- The continued fraction step bound `N + 1`. -/
def shorCfStepBound (N : ℕ) : ℕ := N + 1

/-- The continued fraction bit cost defined as the step bound times the Euclidean step bound at
the order bit length, times that bit length. -/
def shorCfBitCost (N : ℕ) : ℕ :=
  shorCfStepBound N * euclidStepBound (orderBitLength N) * orderBitLength N

/-- A record containing an attempt index, a candidate factor, and the number of attempts. -/
structure ShorSuccessReceipt (N M : ℕ) [NeZero N] where

  index : ℕ

  factor : ℕ

  attempts : ℕ
  deriving DecidableEq, Repr

/-- The receipt for attempt `j`, storing index `j.val`, attempt count `j.val + 1`, and the
extracted factor with default zero when extraction fails. -/
def shorSuccessReceipt {N M R : ℕ} [NeZero N] (ω : Fin R → AttemptOutcome N M)
    (j : Fin R) : ShorSuccessReceipt N M where
  index := j.val
  factor := (attemptOutcomeFactor N M (ω j)).getD 0
  attempts := j.val + 1

/-- The compact record width used in the refined Shor bookkeeping. -/
def shorCompactWidth (m : ℕ) : ℕ := compactRecordWidth m

/-- The uniform preparation cost expression `m * (shorCompactWidth m + 1)`. -/
def shorAspUniformCost (m : ℕ) : ℕ := m * (shorCompactWidth m + 1)

/-- The cardinality of the finite set `smallPrimePowers m`. -/
def shorSmallPrimePowers (m : ℕ) : ℕ := (smallPrimePowers m).card

/-- The conjunction of prime acceptance and the specified composite rejection by the Fermat
screen, screening and preprocessing cost bounds, preprocessing divisor soundness, and the
prime direction property. -/
def clause9_endpoint : Prop :=
  (∀ (N : ℕ) [NeZero N] (_hp : Nat.Prime N) (a : (ZMod N)ˣ),
      shorFermatScreen N a = true)
  ∧ (shorFermatScreen 4 shorUnitThree = false)
  ∧ (∀ N : ℕ, shorFermatScreenBitCost N ≤ polyLogBound 1 6 N)
  ∧ (∀ N : ℕ, preprocessBitCost N ≤ polyLogBound 1 4 N)
  ∧ (∀ (N d : ℕ), evenDivisor N = some d → 1 < d ∧ d < N ∧ d ∣ N)
  ∧ (∀ (N d : ℕ), perfectPowerDivisor N = some d → 1 < d ∧ d < N ∧ d ∣ N)
  ∧ (∀ (N : ℕ) [NeZero N] (_hp : Nat.Prime N) (a : (ZMod N)ˣ), PrimeDirectionWitness N a)

/-- The conjunction of local QFT and modular order resource counts, order verification and
Euclidean correctness, classical processing cost formulas and bounds, and domination of the
rejected attempt ledger. -/
def thresholdGoal_endpoint : Prop :=
  (∀ n : ℕ, GateCount (localProgramCircuit (localQFT n)) = localQftGateCount n ∧
      QueryCount (localProgramCircuit (localQFT n)) = 0 ∧
      localQftSpaceCost n = n)
  ∧ (∀ (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (_hM : 0 < M),
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

/-- The conjunction of attempt factor soundness, index and factor bounds for first success
receipts, and factor tree completeness under the splitter success hypothesis. -/
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
      (∀ m, 2 ≤ m → m ≤ n → ∀ _h : ¬Nat.Prime m, split m ≠ none) →
        (factorTreeOf split n).complete)

/-- The conjunction of finite compact encoding existence, compiled measurement identities, orbit
Fourier isometry, the compact width bound, and the uniform preparation cost formula. -/
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

/-- The conjunction of clock window existence, positive verified recovery mass and a normalized
conditional recovery law under the stated hypotheses, and divisibility and counting
properties of small prime powers. -/
def clause13_endpoint : Prop :=
  (∀ N : ℕ, 1 < N → ∃ q, OriginalClockWindow N q)
  ∧ (∀ (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0 < M) (_hN : 1 < N)
      (_hr : 1 < orderOf a) (_hsize : 2 * N ^ 2 < M),
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
