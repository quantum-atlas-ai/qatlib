/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ClusterPatterns.QubitUniversal.UniversalQubitCompilationQuan
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

theorem arbitrary_rotation_measurement
    (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ) :
    (mbqcQubitWord U).length = 4 ∧
    (∀ ζ ∈ mbqcQubitWord U, ‖ζ‖ = 1) ∧
    ‖mbqcQubitScalar U‖ = 1 ∧
    clusterSequenceUnitary (mbqcQubitWord U) =
      mbqcQubitScalar U • relabelGate boolEquivFin2 U :=
  universalQubitCompilation_answer U hU

theorem su2_rotation_by_measurement (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) (_hdet : U.det = 1) :
    (mbqcQubitWord U).length = 4 ∧
    clusterSequenceUnitary (mbqcQubitWord U) =
      mbqcQubitScalar U • relabelGate boolEquivFin2 U :=
  ⟨(universalQubitCompilation_answer U hU).1,
    (universalQubitCompilation_answer U hU).2.2.2⟩

end Qatlib.Concepts.ClusterPatterns.QubitUniversal
