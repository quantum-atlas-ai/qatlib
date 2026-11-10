/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QsVtStability.InteriorComplexQsvt
import Qatlib.Concepts.QsvtCore.QsVtStability.Lemma23OutputTransport
open Qatlib.Concepts.BlockEncoding.Postselection
set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.WalkSearch.Spectral

namespace Qatlib.Concepts.QsvtCore.QsVtStability

open Matrix Polynomial
open scoped Matrix.Norms.L2Operator

def Lemma23InteriorRobustness : Prop :=
  ∀ (I O : Type) [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A B : Matrix O I ℂ) (base : ℂ) (zs : List ℂ),
    Qatlib.Concepts.PhaseGeometry.Phase.IsPhase base →
    (∀ z ∈ zs, Qatlib.Concepts.PhaseGeometry.Phase.IsPhase z) →
    ‖A‖ ≤ 1 → ‖B‖ ≤ 1 →
    ‖A - B‖ + ‖(2 : ℂ)⁻¹ • (A + B)‖ ^ 2 ≤ 1 →
    (zs.length % 2 = 1 →
      ‖Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A
          (Qatlib.Concepts.QsvtCore.QsVtStability.interiorResponse base zs) -
        Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform B
          (Qatlib.Concepts.QsvtCore.QsVtStability.interiorResponse base zs)‖ ≤
      Qatlib.Concepts.QsvtCore.QsVtStability.interiorRate A B zs.length) ∧
    (zs.length % 2 = 0 →
      ‖Qatlib.Concepts.WalkSearch.Spectral.rightSingularTransform A
          (Qatlib.Concepts.QsvtCore.QsVtStability.interiorResponse base zs) -
        Qatlib.Concepts.WalkSearch.Spectral.rightSingularTransform B
          (Qatlib.Concepts.QsvtCore.QsVtStability.interiorResponse base zs)‖ ≤
      Qatlib.Concepts.QsvtCore.QsVtStability.interiorRate A B zs.length)

end Qatlib.Concepts.QsvtCore.QsVtStability
