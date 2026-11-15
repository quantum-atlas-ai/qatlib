/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.NativeNumerics.NlfftPipeline.InverseNLFFTSU2Finite

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.NativeNumerics.NlfftPipeline Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT Qatlib.Concepts.LaurentPolys.CircleComplement Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

set_option autoImplicit false
open Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT

namespace Qatlib.Papers.InvFFTSU2Ni25.NlfftPipeline
open Polynomial

def Algorithm1Finite : Prop :=
  ∀ (d : ℕ) (A B : Polynomial ℂ),
    A.natDegree ≤ d → B.natDegree ≤ d →
    A * Qatlib.Concepts.NativeNumerics.NlfftPipeline.conjRevN d A + B * Qatlib.Concepts.NativeNumerics.NlfftPipeline.conjRevN d B = X ^ d →
    (A.coeff 0).im = 0 → 0 < (A.coeff 0).re →
    let r := Qatlib.Concepts.NativeNumerics.NlfftPipeline.inverseNLFFTFiniteSU2 A B (d + 1)
    r.gammas.length = d + 1 ∧
    Qatlib.Concepts.NativeNumerics.NlfftPipeline.nlftSU2 r.gammas = (A, B) ∧
    r.eta = A ∧ r.xi = B ∧
    r.operations ≤ 2048 * (d + 1) * (Nat.clog 2 (d + 1) + 5) ^ 2

end Qatlib.Papers.InvFFTSU2Ni25.NlfftPipeline
