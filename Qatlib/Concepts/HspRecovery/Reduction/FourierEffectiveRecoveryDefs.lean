/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Qatlib.Foundations.BornMetrics.EventProbability

/-!
# Definitions for two-register Fourier records

`RecordSpace` contains two phase registers, a Boolean control register, and a target register.
`recordCircuit` composes two counted phase circuits, while `classifiedCircuit` appends a
reversible Boolean classification of their outcomes.

The phase windows and rational resolution choice support quantitative phase estimation as
described in [NielsenChuang2010].

## Main statements

* `recordRun`: runs the two-resolution record circuit on zero ancillary registers.
* `recordEvent`: specifies events in both phase registers.
* `classifiedCircuit`: appends the classifier permutation.
* `resolutionForTolerance`: chooses a natural resolution from a rational tolerance.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

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

/-- The product basis of two finite phase registers, a Boolean control register, and a target
register. -/
abbrev RecordSpace (M N : ℕ) (I : Type) := Fin M × (Bool × (Fin N × I))

/-- The equivalence interchanging the two phase registers while preserving the control and
target registers. -/
def recordSwap (M N : ℕ) : RecordSpace N M I ≃ RecordSpace M N I where
  toFun p := (p.2.2.1, p.2.1, p.1, p.2.2.2)
  invFun p := (p.2.2.1, p.2.1, p.1, p.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The controlled target operator extended by identities on both phase registers. -/
noncomputable def recordOracle (M N : ℕ) (U : Matrix I I ℂ) :
    Matrix (RecordSpace M N I) (RecordSpace M N I) ℂ :=
  TensorGate (1 : Matrix (Fin M) (Fin M) ℂ)
    (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle (TensorGate (1 : Matrix (Fin N) (Fin N) ℂ) U))

/-- The circuit composing counted phase estimation at resolutions `M` and `N`, with the second
circuit relabeled to its register. -/
noncomputable def recordCircuit (M N : ℕ) : Circuit (RecordSpace M N I) :=
  countedPhaseCircuit M ++
    relabelCircuit (recordSwap M N) (countedPhaseCircuit N)

/-- The tensor input with both phase registers at zero, control false, and target state `ψ`. -/
noncomputable def recordInput (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (ψ : QState I) : QState (RecordSpace M N I) :=
  TensorState (Ket (⟨0, hM⟩ : Fin M))
    (TensorState (Ket false) (TensorState (Ket (⟨0, hN⟩ : Fin N)) ψ))

/-- The state produced by the record circuit using the controlled oracle and the prescribed
tensor input. -/
noncomputable def recordRun (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (U : Matrix I I ℂ) (ψ : QState I) : QState (RecordSpace M N I) :=
  Run (recordOracle M N U) (recordCircuit M N) (recordInput M N hM hN ψ)

/-- The event restricting the two phase registers to `S` and `T`, with no restriction on the
control or target. -/
def recordEvent (M N : ℕ) (S : Finset (Fin M)) (T : Finset (Fin N)) :
    Finset (RecordSpace M N I) :=
  S ×ˢ (Finset.univ ×ˢ (T ×ˢ Finset.univ))

/-- The finite set of resolution-`M` outcomes at circular phase distance at most `1 / M` from
`φ`. -/
noncomputable def phaseWindow (M : ℕ) (φ : ℝ) : Finset (Fin M) :=
  Finset.univ.filter fun z => phaseDistance φ ((z.val : ℝ) / (M : ℝ)) ≤ 1 / (M : ℝ)

/-- The Boolean label testing whether the second phase register lies in the half-open interval
`[lo, hi)`. -/
def bandLabel (M N lo hi : ℕ) (r : Fin M × Fin N) : Bool :=
  decide (lo ≤ r.2.val ∧ r.2.val < hi)

/-- The basis map that XORs the label of the phase outcomes into the Boolean control register. -/
def classifierFlip (M N : ℕ) (label : Fin M × Fin N → Bool)
    (p : RecordSpace M N I) : RecordSpace M N I :=
  (p.1, p.2.1 ^^ label (p.1, p.2.2.1), p.2.2)

omit [Fintype I] [DecidableEq I] in

/-- Applying `classifierFlip` twice returns the original basis element. -/
theorem classifierFlip_involutive (M N : ℕ) (label : Fin M × Fin N → Bool) :
    Function.Involutive (classifierFlip (I := I) M N label) := by
  rintro ⟨x, b, y, i⟩
  simp [classifierFlip]

/-- The record circuit followed by the permutation gate that XORs the classifier label into the
control register. -/
noncomputable def classifiedCircuit (M N : ℕ) (label : Fin M × Fin N → Bool) :
    Circuit (RecordSpace M N I) :=
  recordCircuit M N ++ [.gate (permMatrix (classifierFlip M N label))]

/-- The resolution `max 2 ⌈ε⁻¹⌉₊` associated with a rational tolerance. -/
def resolutionForTolerance (ε : ℚ) : ℕ := max 2 ⌈ε⁻¹⌉₊

/-- The finite set of resolution-`M` outcomes at circular phase distance at most `ε` from `φ`. -/
noncomputable def radiusWindow (M : ℕ) (φ ε : ℝ) : Finset (Fin M) :=
  Finset.univ.filter fun z => phaseDistance φ ((z.val : ℝ) / (M : ℝ)) ≤ ε

end Qatlib.Concepts.HspRecovery.ReductionCore
