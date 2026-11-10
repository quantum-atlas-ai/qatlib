/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
import Qatlib.Concepts.WalkSearch.Detection.CorrectedSzegedyDetector
import Qatlib.Concepts.WalkSearch.CountedWalk.CountedSzegedyAccess
import Qatlib.Concepts.WalkSearch.MnrsAmplify.WalkSearchCompilationDefs
import Qatlib.Concepts.WalkSearch.FrameSpectral.WalkSpectralBounds
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option linter.unusedVariables false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.UniformBqp.FiniteGateWord Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.WalkSearch.CountedWalk
open Qatlib.Concepts.WalkSearch.MnrsAmplify
open Qatlib.Concepts.WalkSearch.ProjectorCS

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

open Matrix
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.WalkSearch.MnrsAmplify
open scoped Classical BigOperators

def lazyTopIndex (m : ℕ) (hm : 1 ≤ m) : Fin m := ⟨m - 1, by omega⟩

def lazyTopWire (m : ℕ) (hm : 1 ≤ m) : Fin (m + m) := ⟨m + m - 1, by omega⟩

def lazyFlagWire (m : ℕ) (hm : 1 ≤ m) : Fin (m + m) := ⟨m, by omega⟩

def lazyCtlWire (m : ℕ) (hm : 1 ≤ m) : Fin (m + m) := ⟨m - 1, by omega⟩

def lazyFlagIndex (m : ℕ) : Fin (m + 1) := ⟨m, by omega⟩

def lazyCtlIndex (m : ℕ) (hm : 1 ≤ m) : Fin (m + 1) := ⟨m - 1, by omega⟩

lemma lazyFlagIndex_val (m : ℕ) : (lazyFlagIndex m).val = m := rfl

lemma lazyCtlIndex_val {m : ℕ} (hm : 1 ≤ m) : (lazyCtlIndex m hm).val = m - 1 := rfl

lemma lazyTopIndex_val {m : ℕ} (hm : 1 ≤ m) : (lazyTopIndex m hm).val = m - 1 := rfl

lemma lazyTopWire_val {m : ℕ} (hm : 1 ≤ m) : (lazyTopWire m hm).val = m + m - 1 := rfl

lemma lazyFlagWire_val {m : ℕ} (hm : 1 ≤ m) : (lazyFlagWire m hm).val = m := rfl

lemma lazyCtlWire_val {m : ℕ} (hm : 1 ≤ m) : (lazyCtlWire m hm).val = m - 1 := rfl

lemma lazyTopIndex_eq {m : ℕ} (hm : 1 ≤ m) : lazyTopIndex m hm = ⟨m - 1, by omega⟩ := by
  apply Fin.ext
  exact (lazyTopIndex_val hm).symm

def lazyRowBasis {m : ℕ} (x : Reg m) (b : Bool) : Reg m :=
  fun i => if i.val + 1 = m then b else x i

def lazyLowAgrees {m : ℕ} (x y : Reg m) : Prop :=
  ∀ i : Fin m, i.val + 1 < m → y i = x i

instance (m : ℕ) (x : Reg m) : DecidablePred (fun y => lazyLowAgrees x y) :=
  fun y => by unfold lazyLowAgrees; infer_instance

noncomputable def lazyMatchingKernel (m : ℕ) (x y : Reg m) : ℝ :=
  if lazyLowAgrees x y then (1 / 2 : ℝ) else 0

def lazyMatchingNeighbourNat {m : ℕ} (x : Reg m) (j : ℕ) : Reg m :=
  fun i => if i.val + 1 = m then (decide (j % 2 = 1)) else x i

def lazyMatchingIndexNat {m : ℕ} (j : ℕ) : Reg m :=
  fun i => if i.val + 1 = m then (decide (j % 2 = 1)) else false

def lazySupport {m : ℕ} (x : Reg m) : Finset (Reg m) :=
  {lazyMatchingNeighbourNat x 0, lazyMatchingNeighbourNat x 1}

def highCnotPairs (m : ℕ) : List (Fin (m + m) × Fin (m + m)) :=
  List.ofFn fun i : Fin (m - 1) => (⟨i.val, by omega⟩, ⟨m + i.val, by omega⟩)

def cnotFold {n : ℕ} (L : List (Fin n × Fin n)) (r : Reg n) : Reg n :=
  L.foldl (fun s p => Function.update s p.2 (s p.2 ^^ s p.1)) r

def lazySetupWord (m : ℕ) : List FiniteGateCode :=
  (highCnotPairs m).map (fun p => FiniteGateCode.cx p.1.val p.2.val) ++
    [FiniteGateCode.h (m + m - 1)]

def lazyUpdateWord (m : ℕ) : List FiniteGateCode :=
  (highCnotPairs m).map (fun p => FiniteGateCode.cx p.1.val p.2.val)

def lazyCheckWord (m : ℕ) : List FiniteGateCode :=
  [FiniteGateCode.cx (m - 1) m]

def lazyMarkedSet (m : ℕ) (hm : 1 ≤ m) : Finset (Reg m) :=
  Finset.univ.filter fun x => x (lazyTopIndex m hm)

def HasPaidWalkAccess {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (P : I → I → ℝ) (S : Finset I)
    (a w : ℕ) (enc : I → Reg a)
    (support : I → Finset I) (idx : ℕ → I) (nbr : I → ℕ → I)
    (setupWord updateWord checkWord : List FiniteGateCode)
    (C : ℕ → ℕ) : Prop :=
  Function.Injective enc ∧
    finiteWordLegal w setupWord = true ∧
    finiteWordLegal w updateWord = true ∧
    finiteWordLegal w checkWord = true ∧
    (∀ (x : I) (eps : ℝ), 0 < eps →
      ∃ (φ : QState (Reg w)),
        finiteWordRun w setupWord (Qatlib.Foundations.PureStateMath.Ket (regPad w a (enc x))) = some φ ∧
        (∑ i, ‖φ i - rowBasisRecordState P a w enc x i‖ ^ 2 ≤ eps ^ 2) ∧
        setupWord.length ≤ C (Nat.ceil ((1 / eps) ^ 2) + 1)) ∧
    (∀ (x : I) (j : ℕ), j < (support x).card →
      finiteWordRun w updateWord
          (Qatlib.Foundations.PureStateMath.Ket (regPad w (a + a) (regCat (enc x) (enc (idx j))))) =
        some (Qatlib.Foundations.PureStateMath.Ket (regPad w (a + a) (regCat (enc x) (enc (nbr x j)))))) ∧
    (∀ (x : I),
      finiteWordRun w checkWord
          (Qatlib.Foundations.PureStateMath.Ket (regPad w (a + 1) (regCat (enc x) (fun _ => false)))) =
        some (Qatlib.Foundations.PureStateMath.Ket (regPad w (a + 1) (regCat (enc x) (fun _ => decide (x ∈ S)))))) ∧
    updateWord.length ≤ 2 * a + 2 ∧
    checkWord.length ≤ 2 * a + 2 ∧
    w ≤ 2 * a + 2 ∧
    (∀ j : I, adjointQueryCount (countedSzegedyWord j) = 4 ∧
      adjointGateCount (countedSzegedyWord j) = 4)

def HasPaidWalkAccessConstantThird : Prop :=
  ¬ HasPaidWalkAccess (I := Fin 2) (fun _ _ => (1 / 3 : ℝ)) (∅ : Finset (Fin 2))
    1 2 (fun _ => fun _ => false) (fun _ => ∅) (fun _ => ⟨0, by norm_num⟩)
    (fun _ _ => ⟨0, by norm_num⟩) [] [] [] (fun _ => 0)

def PrintedVariantPerKCounterexample {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (S : Finset I) (j : I) (U : Matrix (I × I) (I × I) ℂ) (δ : ℝ)
    (threshold : ℝ) : Prop :=
  IsTransitionMatrix P ∧ (∀ i y, P i y = P y i) ∧ 0 < δ ∧ δ ≤ 1 ∧
    SymmetricChainGap P δ ∧ S.Nonempty ∧ markedFraction S < threshold ∧
    RowPreservingAccess U ∧ j ∉ S ∧
    (∀ K : ℕ, plusIDetectionProbability U S j K < threshold)

def AnchoredRowPreservingConstantProfile {I : Type} [Fintype I] [DecidableEq I] : Prop :=
  ∀ (P : I → I → ℝ) (j : I) (U : Matrix (I × I) (I × I) ℂ),
    (∀ i : I, U *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket i) (Qatlib.Foundations.PureStateMath.Ket j) = SzegedyIsometry P *ᵥ Qatlib.Foundations.PureStateMath.Ket i) →
    RowPreservingAccess U →
    ∃ π : I → ℝ, ∀ i y, Real.sqrt (P i y) = π y

end Qatlib.Concepts.WalkSearch.FrameSpectral
