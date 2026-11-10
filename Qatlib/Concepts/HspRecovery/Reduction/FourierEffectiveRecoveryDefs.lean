/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Qatlib.Foundations.BornMetrics.EventProbability
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open Matrix
open scoped Classical

variable {I : Type} [Fintype I] [DecidableEq I]

abbrev RecordSpace (M N : ℕ) (I : Type) := Fin M × (Bool × (Fin N × I))

def recordSwap (M N : ℕ) : RecordSpace N M I ≃ RecordSpace M N I where
  toFun p := (p.2.2.1, p.2.1, p.1, p.2.2.2)
  invFun p := (p.2.2.1, p.2.1, p.1, p.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def recordOracle (M N : ℕ) (U : Matrix I I ℂ) :
    Matrix (RecordSpace M N I) (RecordSpace M N I) ℂ :=
  TensorGate (1 : Matrix (Fin M) (Fin M) ℂ)
    (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (TensorGate (1 : Matrix (Fin N) (Fin N) ℂ) U))

noncomputable def recordCircuit (M N : ℕ) : Circuit (RecordSpace M N I) :=
  countedPhaseCircuit M ++
    relabelCircuit (recordSwap M N) (countedPhaseCircuit N)

noncomputable def recordInput (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (ψ : QState I) : QState (RecordSpace M N I) :=
  TensorState (Ket (⟨0, hM⟩ : Fin M))
    (TensorState (Ket false) (TensorState (Ket (⟨0, hN⟩ : Fin N)) ψ))

noncomputable def recordRun (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (U : Matrix I I ℂ) (ψ : QState I) : QState (RecordSpace M N I) :=
  Run (recordOracle M N U) (recordCircuit M N) (recordInput M N hM hN ψ)

def recordEvent (M N : ℕ) (S : Finset (Fin M)) (T : Finset (Fin N)) :
    Finset (RecordSpace M N I) :=
  S ×ˢ (Finset.univ ×ˢ (T ×ˢ Finset.univ))

noncomputable def phaseWindow (M : ℕ) (φ : ℝ) : Finset (Fin M) :=
  Finset.univ.filter fun z => phaseDistance φ ((z.val : ℝ) / (M : ℝ)) ≤ 1 / (M : ℝ)

def bandLabel (M N lo hi : ℕ) (r : Fin M × Fin N) : Bool :=
  decide (lo ≤ r.2.val ∧ r.2.val < hi)

def classifierFlip (M N : ℕ) (label : Fin M × Fin N → Bool)
    (p : RecordSpace M N I) : RecordSpace M N I :=
  (p.1, p.2.1 ^^ label (p.1, p.2.2.1), p.2.2)

omit [Fintype I] [DecidableEq I] in

theorem classifierFlip_involutive (M N : ℕ) (label : Fin M × Fin N → Bool) :
    Function.Involutive (classifierFlip (I := I) M N label) := by
  rintro ⟨x, b, y, i⟩
  simp [classifierFlip]

noncomputable def classifiedCircuit (M N : ℕ) (label : Fin M × Fin N → Bool) :
    Circuit (RecordSpace M N I) :=
  recordCircuit M N ++ [.gate (permMatrix (classifierFlip M N label))]

def resolutionForTolerance (ε : ℚ) : ℕ := max 2 ⌈ε⁻¹⌉₊

noncomputable def radiusWindow (M : ℕ) (φ ε : ℝ) : Finset (Fin M) :=
  Finset.univ.filter fun z => phaseDistance φ ((z.val : ℝ) / (M : ℝ)) ≤ ε

end Qatlib.Concepts.HspRecovery.ReductionCore
