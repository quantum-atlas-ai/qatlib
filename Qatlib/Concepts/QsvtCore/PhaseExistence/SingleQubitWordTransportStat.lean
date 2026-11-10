/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.SingleQubitSignal
set_option warningAsError false


open Qatlib.Concepts.QsvtCore.QsVtMain

open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Matrix Polynomial Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

def SingleQubitWordTransport : Prop :=
  ∀ (Φ : List ℝ) (x : ℝ), x ∈ Set.Icc (-1 : ℝ) 1 →
    reflectionWord x Φ 0 0 = (sourcePhaseResponse Φ).eval (x : ℂ) ∧
    reflectionWord x Φ 1 0 =
      Real.sqrt (1 - x ^ 2) * (responseQ 1 (Φ.map anglePhase)).eval (x : ℂ)

end Qatlib.Concepts.QsvtCore.PhaseExistence
