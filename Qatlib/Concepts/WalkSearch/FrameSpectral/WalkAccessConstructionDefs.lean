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

/-!
# Lazy matching gates and paid walk access

This module defines a lazy matching kernel on Boolean registers, its two-element neighbor
support, and finite setup, update, and marked check words. The circuit definitions use CNOT
gates to copy all coordinates below the top bit and a Hadamard gate to prepare the remaining
superposition.

`HasPaidWalkAccess` records injective encoding, legal finite words, approximate row preparation,
exact neighbor and marking actions, and explicit length and workspace bounds. Additional
propositions describe a printed detector counterexample condition and the constant profile
restriction on anchored row preserving access. These access constructions support the quantum
walk framework of [Szegedy2004].

## Main statements

* `lazyMatchingKernel`: The kernel with weight one half when lower register bits agree.
* `HasPaidWalkAccess`: Finite gate access semantics and resource requirements.
* `AnchoredRowPreservingConstantProfile`: The common square-root row profile requirement.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false

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

/-- The top coordinate `m - 1` of a nonempty `m`-bit register. -/
def lazyTopIndex (m : ℕ) (hm : 1 ≤ m) : Fin m := ⟨m - 1, by omega⟩

/-- The final wire `2 * m - 1` of the two-register workspace. -/
def lazyTopWire (m : ℕ) (hm : 1 ≤ m) : Fin (m + m) := ⟨m + m - 1, by omega⟩

/-- The wire at position `m` used for the marked flag in the two-register workspace. -/
def lazyFlagWire (m : ℕ) (hm : 1 ≤ m) : Fin (m + m) := ⟨m, by omega⟩

/-- The wire at position `m - 1` used to control the marked check. -/
def lazyCtlWire (m : ℕ) (hm : 1 ≤ m) : Fin (m + m) := ⟨m - 1, by omega⟩

/-- The final coordinate `m` of the vertex-plus-flag register. -/
def lazyFlagIndex (m : ℕ) : Fin (m + 1) := ⟨m, by omega⟩

/-- The vertex top coordinate `m - 1` in the vertex-plus-flag register. -/
def lazyCtlIndex (m : ℕ) (hm : 1 ≤ m) : Fin (m + 1) := ⟨m - 1, by omega⟩

/-- The natural value of the flag index is `m`. -/
lemma lazyFlagIndex_val (m : ℕ) : (lazyFlagIndex m).val = m := rfl

/-- The natural value of the control index is `m - 1`. -/
lemma lazyCtlIndex_val {m : ℕ} (hm : 1 ≤ m) : (lazyCtlIndex m hm).val = m - 1 := rfl

/-- The natural value of the top vertex index is `m - 1`. -/
lemma lazyTopIndex_val {m : ℕ} (hm : 1 ≤ m) : (lazyTopIndex m hm).val = m - 1 := rfl

/-- The natural value of the top workspace wire is `m + m - 1`. -/
lemma lazyTopWire_val {m : ℕ} (hm : 1 ≤ m) : (lazyTopWire m hm).val = m + m - 1 := rfl

/-- The natural value of the flag wire is `m`. -/
lemma lazyFlagWire_val {m : ℕ} (hm : 1 ≤ m) : (lazyFlagWire m hm).val = m := rfl

/-- The natural value of the control wire is `m - 1`. -/
lemma lazyCtlWire_val {m : ℕ} (hm : 1 ≤ m) : (lazyCtlWire m hm).val = m - 1 := rfl

/-- The top vertex index is the finite index with value `m - 1`. -/
lemma lazyTopIndex_eq {m : ℕ} (hm : 1 ≤ m) : lazyTopIndex m hm = ⟨m - 1, by omega⟩ := by
  apply Fin.ext
  exact (lazyTopIndex_val hm).symm

/-- The register obtained from `x` by replacing its top bit with `b`. -/
def lazyRowBasis {m : ℕ} (x : Reg m) (b : Bool) : Reg m :=
  fun i => if i.val + 1 = m then b else x i

/-- The condition that two registers agree at every coordinate strictly below the top bit. -/
def lazyLowAgrees {m : ℕ} (x y : Reg m) : Prop :=
  ∀ i : Fin m, i.val + 1 < m → y i = x i

instance (m : ℕ) (x : Reg m) : DecidablePred (fun y => lazyLowAgrees x y) :=
  fun y => by unfold lazyLowAgrees; infer_instance

/-- The real kernel equal to one half when the lower bits of the two registers agree and zero
otherwise. -/
noncomputable def lazyMatchingKernel (m : ℕ) (x y : Reg m) : ℝ :=
  if lazyLowAgrees x y then (1 / 2 : ℝ) else 0

/-- The neighbor register obtained by preserving the lower bits of `x` and setting the top bit
to the parity of `j`. -/
def lazyMatchingNeighbourNat {m : ℕ} (x : Reg m) (j : ℕ) : Reg m :=
  fun i => if i.val + 1 = m then (decide (j % 2 = 1)) else x i

/-- The register with all lower bits false and top bit equal to the parity of `j`. -/
def lazyMatchingIndexNat {m : ℕ} (j : ℕ) : Reg m :=
  fun i => if i.val + 1 = m then (decide (j % 2 = 1)) else false

/-- The finite set consisting of the neighbors obtained by setting the top bit to false and
true. -/
def lazySupport {m : ℕ} (x : Reg m) : Finset (Reg m) :=
  {lazyMatchingNeighbourNat x 0, lazyMatchingNeighbourNat x 1}

/-- The list of control-target pairs `(i, m + i)` for coordinates `i < m - 1` in the doubled
register. -/
def highCnotPairs (m : ℕ) : List (Fin (m + m) × Fin (m + m)) :=
  List.ofFn fun i : Fin (m - 1) => (⟨i.val, by omega⟩, ⟨m + i.val, by omega⟩)

/-- The register obtained by sequentially XORing each listed control bit into its target bit. -/
def cnotFold {n : ℕ} (L : List (Fin n × Fin n)) (r : Reg n) : Reg n :=
  L.foldl (fun s p => Function.update s p.2 (s p.2 ^^ s p.1)) r

/-- The finite gate word that copies lower vertex bits to the second register and applies a
Hadamard gate to its top wire. -/
def lazySetupWord (m : ℕ) : List FiniteGateCode :=
  (highCnotPairs m).map (fun p => FiniteGateCode.cx p.1.val p.2.val) ++
    [FiniteGateCode.h (m + m - 1)]

/-- The finite CNOT word copying each lower vertex bit into the corresponding second-register
wire. -/
def lazyUpdateWord (m : ℕ) : List FiniteGateCode :=
  (highCnotPairs m).map (fun p => FiniteGateCode.cx p.1.val p.2.val)

/-- The single CNOT word with control `m - 1` and target `m`, used for the marked flag. -/
def lazyCheckWord (m : ℕ) : List FiniteGateCode :=
  [FiniteGateCode.cx (m - 1) m]

/-- The finite set of registers whose top bit is true. -/
def lazyMarkedSet (m : ℕ) (hm : 1 ≤ m) : Finset (Reg m) :=
  Finset.univ.filter fun x => x (lazyTopIndex m hm)

/-- The access specification requiring an injective encoding, legal finite words, row
preparation at every positive tolerance, exact neighbor updates and marked checks, and the
stated resource bounds. -/
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

/-- The assertion that the specified constant one-third array with constant vertex encoding and
empty words fails `HasPaidWalkAccess`. -/
def HasPaidWalkAccessConstantThird : Prop :=
  ¬ HasPaidWalkAccess (I := Fin 2) (fun _ _ => (1 / 3 : ℝ)) (∅ : Finset (Fin 2))
    1 2 (fun _ => fun _ => false) (fun _ => ∅) (fun _ => ⟨0, by norm_num⟩)
    (fun _ _ => ⟨0, by norm_num⟩) [] [] [] (fun _ => 0)

/-- The condition that a symmetric gapped transition matrix with a nonempty small marked set and
row preserving access has printed plus-I detection probability below the given threshold for
every power. -/
def PrintedVariantPerKCounterexample {I : Type} [Fintype I] [DecidableEq I]
    (P : I → I → ℝ) (S : Finset I) (j : I) (U : Matrix (I × I) (I × I) ℂ) (δ : ℝ)
    (threshold : ℝ) : Prop :=
  IsTransitionMatrix P ∧ (∀ i y, P i y = P y i) ∧ 0 < δ ∧ δ ≤ 1 ∧
    SymmetricChainGap P δ ∧ S.Nonempty ∧ markedFraction S < threshold ∧
    RowPreservingAccess U ∧ j ∉ S ∧
    (∀ K : ℕ, plusIDetectionProbability U S j K < threshold)

/-- The requirement that any anchored access matrix satisfying `RowPreservingAccess` forces all
square-root transition rows to have a common profile. -/
def AnchoredRowPreservingConstantProfile {I : Type} [Fintype I] [DecidableEq I] : Prop :=
  ∀ (P : I → I → ℝ) (j : I) (U : Matrix (I × I) (I × I) ℂ),
    (∀ i : I, U *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket i) (Qatlib.Foundations.PureStateMath.Ket j) = SzegedyIsometry P *ᵥ Qatlib.Foundations.PureStateMath.Ket i) →
    RowPreservingAccess U →
    ∃ π : I → ℝ, ∀ i y, Real.sqrt (P i y) = π y

end Qatlib.Concepts.WalkSearch.FrameSpectral
