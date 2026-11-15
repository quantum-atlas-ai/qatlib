/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.AmplitudeCore.InvFreeSampling.InvFreeAESemantics

@[expose] public section
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.PureStateMath Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

namespace Qatlib.Concepts.AmplitudeCore.InvFreeSampling

open Qatlib

def InverseFreeAESamplingBound : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (P : Matrix I I ℂ)
    (hP : IsOrthogonalProjector P) (j₀ : I) (ε : ℝ) (_hε0 : 0 < ε) (_hε1 : ε < 1)
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ),
    2 / 3 ≤ (invFreeBranchDist P j₀ hP U hU).probEvent
      (fun ω : Fin (invFreeSampleCount ε) → Bool =>
        |Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.avg invFreeReadout ω - invFreeAmplitude P j₀ U| ≤ ε)

end Qatlib.Concepts.AmplitudeCore.InvFreeSampling
