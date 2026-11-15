/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.InvFFTSU2Ni25.NlfftPipeline.Algorithm1FiniteStat

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.NativeNumerics.NlfftPipeline Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Concepts.LaurentPolys.CanonicalComplementFFT Qatlib.Concepts.LaurentPolys.CircleComplement Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

namespace Qatlib.Papers.InvFFTSU2Ni25.NlfftPipeline

/-- The finite inverse nonlinear FFT reconstructs the normalized complementary polynomial pair,
returns `d+1` parameters, and satisfies the stated operation bound. -/
theorem algorithm1Finite : Algorithm1Finite := by
  intro d A B hA hB hid h0im h0re
  have hex :=
      Qatlib.Concepts.NativeNumerics.NlfftPipeline.layerStripExact_of_pos A B
      (d + 1) h0im h0re
  obtain ⟨hg, he, hx⟩ :=
      Qatlib.Concepts.NativeNumerics.NlfftPipeline.inverseNLFFTFiniteSU2_gammas A B
      (d + 1) hex
  obtain ⟨h1, -, -⟩ :=
      Qatlib.Concepts.NativeNumerics.NlfftPipeline.layerStripSU2_correct d A B hA hB hid h0im h0re
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hg]
    exact Qatlib.Concepts.NativeNumerics.NlfftPipeline.layerStripSU2_gammas_length A B (d + 1)
  · rw [hg]
    exact h1
  · rw [he, h1]
  · rw [hx, h1]
  · exact Qatlib.Concepts.NativeNumerics.NlfftPipeline.inverseNLFFTFiniteSU2_operations A B
      (d + 1) (Nat.succ_pos d)

end Qatlib.Papers.InvFFTSU2Ni25.NlfftPipeline
