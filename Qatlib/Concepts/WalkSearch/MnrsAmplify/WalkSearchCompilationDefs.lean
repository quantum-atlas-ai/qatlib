/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.WalkSearchDefs
import Qatlib.Concepts.ClassicalTape.TapeCompilation.BitMachineTime
import Qatlib.Concepts.CoherentSim.CoherentOAA.QueryCircuit
import Qatlib.Concepts.SpectralFilter.BusySpectrum.BipartiteSpectrumConsumers
import Qatlib.Concepts.WalkSearch.CountedWalk.CountedSzegedyAccess
import Qatlib.Concepts.QuantumGibbs.FormAlgebra.DataAugmentedSearchConsumers

/-!
# Finite-word walk search accounts

Defines finite gate-word accounts and element-readout predicates for quantum walk search
[MagniezNayakRolandSantha2011]. `HasEffectiveWalkSUCAccount` records setup approximations and
update/check words, while `HasRealElementFind` combines search success, output masses, legal
words, and a setup/update/check ledger.

## Main statements

* `HasEffectiveWalkSUCAccount`: The existence of injective state encodings and legal finite
  update/check words, together with arbitrarily accurate row-state preparation words and the
  stated gate and query accounts.
* `HasRealElementFind`: The existence of phase-search parameters with success at least `1 / 24`,
  marked-vertex output masses, legal gate words and matching resource ledgers, the stated total
  cost bound, and zero success for an empty marked set.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option linter.unusedVariables false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.SpectralFilter.BusySpectrum
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.WalkSearch.CountedWalk
open Qatlib.Concepts.WalkSearch.Detection

namespace Qatlib.Concepts.WalkSearch.MnrsAmplify

open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Matrix
open scoped Classical BigOperators

/-- The state-space element with index `k` under the chosen equivalence with `Fin (Fintype.card
I)`. -/
noncomputable def rowIndex (I : Type) [Fintype I] (k : ℕ) (hk : k < Fintype.card I) : I :=
  (Fintype.equivFin I).symm ⟨k, hk⟩

/-- The `k`th listed positive-transition neighbor of `x`, defaulting to `x` when the index is
out of range. -/
noncomputable def rowNeighborOf {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (x : I) (k : ℕ) : I :=
  ((Finset.univ.filter fun y => 0 < P x y).toList.getD k) x

/-- The padded two-record superposition with amplitudes `sqrt (P x y)` and records encoding the
source `x` and destination `y`. -/
noncomputable def rowBasisRecordState {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (a w : ℕ) (enc : I → Reg a) (x : I) : QState (Reg w) :=
  ∑ y : I, ((Real.sqrt (P x y) : ℝ) : ℂ) •
    Qatlib.Foundations.PureStateMath.Ket (regPad w (a + a) (regCat (enc x) (enc y)))

/-- The existence of injective state encodings and legal finite update/check words, together
with arbitrarily accurate row-state preparation words and the stated gate and query
accounts. -/
def HasEffectiveWalkSUCAccount {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) : Prop :=
  ∃ (a w gateUpdate gateCheck : ℕ) (enc : I → Reg a)
      (updateWord checkWord : List FiniteGateCode) (C : ℕ → ℕ),
    Function.Injective enc ∧
      finiteWordLegal w updateWord = true ∧
      finiteWordLegal w checkWord = true ∧
      (∀ (x : I) (eps : ℝ), 0 < eps →
        ∃ (setupWord : List FiniteGateCode) (φ : QState (Reg w)),
          finiteWordLegal w setupWord = true ∧
            finiteWordRun w setupWord (Qatlib.Foundations.PureStateMath.Ket (regPad w a (enc x))) = some φ ∧
            (∑ i, ‖φ i - rowBasisRecordState P a w enc x i‖ ^ 2 ≤ eps ^ 2) ∧
            setupWord.length ≤ C (Nat.ceil ((1 / eps) ^ 2) + 1)) ∧
      (∀ (x : I) (j : Fin (Fintype.card I)),
        j.val < (Finset.univ.filter fun y => 0 < P x y).card →
        finiteWordRun w updateWord
            (Qatlib.Foundations.PureStateMath.Ket (regPad w (a + a)
              (regCat (enc x) (enc (rowIndex I j.val j.isLt))))) =
          some (Qatlib.Foundations.PureStateMath.Ket (regPad w (a + a)
            (regCat (enc x) (enc (rowNeighborOf P x j.val)))))) ∧
      (∀ x : I,
        finiteWordRun w checkWord
            (Qatlib.Foundations.PureStateMath.Ket (regPad w (a + 1) (regCat (enc x) (fun _ => false)))) =
          some (Qatlib.Foundations.PureStateMath.Ket (regPad w (a + 1) (regCat (enc x) (fun _ => x ∈ S))))) ∧
      updateWord.length ≤ gateUpdate ∧
      checkWord.length ≤ gateCheck ∧
      (∀ j : I, adjointQueryCount (countedSzegedyWord j) = 4 ∧
        adjointGateCount (countedSzegedyWord j) = 4)

/-- Evaluates a finite gate word as a matrix, with the empty word acting as the identity and
each head gate multiplied on the right of the tail evaluation. -/
noncomputable def finiteWordMatrix (w : ℕ) : List FiniteGateCode →
    Matrix (Reg w) (Reg w) ℂ
  | [] => 1
  | g :: gs => finiteWordMatrix w gs * finiteCodeMatrix w g

/-- The assertion that no natural-number-indexed sequence of legal finite gate words exactly
covers all two-qubit unitary matrices. -/
def noCountableExactGateCover : Prop :=
  ¬ ∃ eG : ℕ → List FiniteGateCode,
    ∀ U : Matrix (Reg 2) (Reg 2) ℂ, U ∈ Matrix.unitaryGroup (Reg 2) ℂ →
      ∃ n : ℕ, finiteWordLegal 2 (eG n) = true ∧ finiteWordMatrix 2 (eG n) = U

/-- The probability mass of phase-search outcomes whose designated vertex register equals `x`. -/
noncomputable def findElementMass {I : Type} [Fintype I] [DecidableEq I]
    (W : Matrix (I × I) (I × I) ℂ) (ψ : QState (I × I)) (S : Finset I)
    (Mq k t : ℕ) (x : I) : ℝ :=
  MeasureProb (phaseSearchState W ψ (edgeMarkedSet S) Mq k t)
    (Finset.univ.filter fun q => q.2.2.1 = x)

/-- Resource counts for one algorithmic part: fair random bits, elementary gates, and bit time. -/
structure PartLedger where

  fairBits : ℕ

  elementaryGates : ℕ

  bitTime : ℕ

/-- The setup, update, and check resource ledgers together with the number of space bits. -/
structure FindLedger where

  setup : PartLedger

  update : PartLedger

  check : PartLedger

  spaceBits : ℕ

/-- The bit-time charge of a gate word, defined as its length times `w + 1`. -/
def wordBitTime (w : ℕ) (gs : List FiniteGateCode) : ℕ := gs.length * (w + 1)

/-- The condition that the summed fair-bit, elementary-gate, and bit-time counts of each ledger
part are bounded by the corresponding setup, update, or check budget. -/
def FindCostAccount (Sc Uc Cc : ℝ) (L : FindLedger) : Prop :=
  ((L.setup.fairBits + L.setup.elementaryGates + L.setup.bitTime : ℕ) : ℝ) ≤ Sc ∧
    ((L.update.fairBits + L.update.elementaryGates + L.update.bitTime : ℕ) : ℝ) ≤ Uc ∧
    ((L.check.fairBits + L.check.elementaryGates + L.check.bitTime : ℕ) : ℝ) ≤ Cc

/-- The existence of phase-search parameters with success at least `1 / 24`, marked-vertex
output masses, legal gate words and matching resource ledgers, the stated total cost bound,
and zero success for an empty marked set. -/
def HasRealElementFind {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I) (Sc Uc Cc bound : ℝ) : Prop :=
  ∃ (Mq k t : ℕ) (L : FindLedger) (w : ℕ)
      (setupWord updateWord checkWord : List FiniteGateCode),
    2 ≤ Mq ∧
      1 / 24 ≤ walkFindSuccessProb (SzegedyWalk P) (detectionInitial P)
        (edgeMarkedSet S) Mq k t ∧
      walkFindSuccessProb (SzegedyWalk P) (detectionInitial P) (edgeMarkedSet S) Mq k t
        = ∑ x ∈ S, findElementMass (SzegedyWalk P) (detectionInitial P) S Mq k t x ∧
      finiteWordLegal w setupWord = true ∧
      finiteWordLegal w updateWord = true ∧
      finiteWordLegal w checkWord = true ∧
      L.setup.elementaryGates = setupWord.length ∧
      L.update.elementaryGates = updateWord.length ∧
      L.check.elementaryGates = checkWord.length ∧
      L.setup.bitTime = wordBitTime w setupWord ∧
      L.update.bitTime = wordBitTime w updateWord ∧
      L.check.bitTime = wordBitTime w checkWord ∧
      L.spaceBits = w ∧
      FindCostAccount Sc Uc Cc L ∧
      Sc + ((2 * k * t * (Mq - 1) : ℕ) : ℝ) * Uc + (t : ℝ) * Cc ≤ bound ∧
      (S = ∅ → walkFindSuccessProb (SzegedyWalk P) (detectionInitial P)
        (edgeMarkedSet S) Mq k t = 0)

end Qatlib.Concepts.WalkSearch.MnrsAmplify
