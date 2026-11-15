/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.InvFFTSU2Ni25.NlfftPipeline.Algorithm1Stat

@[expose] public section
open Qatlib.Concepts.NativeNumerics.NlfftPipeline

namespace Qatlib.Papers.InvFFTSU2Ni25.NlfftPipeline

/-- The inverse nonlinear FFT reconstructs the normalized complementary polynomial pair, returns
`d+1` parameters, and satisfies the stated operation bound. -/
theorem algorithm1 : Algorithm1 := by
  intro d A B hA hB hid h0im h0re
  have hex :=
      Qatlib.Concepts.NativeNumerics.NlfftPipeline.layerStripExact_of_pos A B
      (d + 1) h0im h0re
  obtain ⟨hg, he, hx⟩ :=
      Qatlib.Concepts.NativeNumerics.NlfftPipeline.inverseNLFFTSU2_gammas A B (d + 1) hex
  obtain ⟨h1, -, -⟩ :=
      Qatlib.Concepts.NativeNumerics.NlfftPipeline.layerStripSU2_correct d A B hA hB hid h0im h0re
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hg]
    exact Qatlib.Concepts.NativeNumerics.NlfftPipeline.layerStripSU2_gammas_length A B (d + 1)
  · rw [hg]
    exact h1
  · rw [he, h1]
  · rw [hx, h1]
  · exact Qatlib.Concepts.NativeNumerics.NlfftPipeline.inverseNLFFTSU2_operations A B (d + 1)
      (Nat.succ_pos d)

end Qatlib.Papers.InvFFTSU2Ni25.NlfftPipeline
