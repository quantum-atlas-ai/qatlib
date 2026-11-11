/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.QubitUniversal.UniversalQubitCompilationQuan

/-!
# Arbitrary qubit rotations by cluster measurements

This module exposes four-step cluster-word compilation for an arbitrary one-qubit unitary and
its determinant-one specialization. The equality is stated up to the explicitly supplied scalar
`mbqcQubitScalar`, with unit modulus established in `arbitrary_rotation_measurement`.

These results express one-qubit measurement universality in the cluster scheme of
[RaussendorfBriegel2000].

## Main statements

* `arbitrary_rotation_measurement`: four-step compilation of a unitary with unit-modulus
  parameters and scalar.
* `su2_rotation_by_measurement`: the corresponding equality for a determinant-one unitary.

## References

* [Raussendorf and Briegel, 2000][RaussendorfBriegel2000]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.InstrumentCore.PatternCompile
open Qatlib.Concepts.ClusterPatterns.AdaptiveEuler
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.ClusterPatterns.QubitUniversal

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.ClusterPatterns.QubitUniversal

open Matrix Qatlib

/-- Every one-qubit unitary has the prescribed four-step cluster word with unit-modulus
parameters and a unit-modulus scalar relating its matrix to the target unitary. See
[RaussendorfBriegel2000]. -/
theorem arbitrary_rotation_measurement
    (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    (mbqcQubitWord U).length = 4 ∧
    (∀ ζ ∈ mbqcQubitWord U, ‖ζ‖ = 1) ∧
    ‖mbqcQubitScalar U‖ = 1 ∧
    clusterSequenceUnitary (mbqcQubitWord U) =
      mbqcQubitScalar U • relabelGate boolEquivFin2 U :=
  universalQubitCompilation_answer U hU

/-- For a determinant-one one-qubit unitary, the prescribed cluster word has length four and
equals the relabeled unitary multiplied by `mbqcQubitScalar`. See [RaussendorfBriegel2000]. -/
theorem su2_rotation_by_measurement (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) (_hdet : U.det = 1) :
    (mbqcQubitWord U).length = 4 ∧
    clusterSequenceUnitary (mbqcQubitWord U) =
      mbqcQubitScalar U • relabelGate boolEquivFin2 U :=
  ⟨(universalQubitCompilation_answer U hU).1,
    (universalQubitCompilation_answer U hU).2.2.2⟩

end Qatlib.Concepts.ClusterPatterns.QubitUniversal
