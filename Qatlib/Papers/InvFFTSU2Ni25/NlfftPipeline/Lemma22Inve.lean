/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.InvFFTSU2Ni25.NlfftPipeline.Lemma22Stat

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.NativeNumerics.NlfftPipeline

namespace Qatlib.Papers.InvFFTSU2Ni25.NlfftPipeline

/-- Every complementary polynomial pair with the stated degree bounds and positive real constant
normalization has a unique nonlinear Fourier parameter list of length `d+1`. -/
theorem lemma2_2 : Lemma2_2 := by
  intro d A B hA hB hid h0im h0re
  obtain ⟨h1, -, -⟩ :=
      Qatlib.Concepts.NativeNumerics.NlfftPipeline.layerStripSU2_correct d A B hA hB hid h0im h0re
  have hlen :=
      Qatlib.Concepts.NativeNumerics.NlfftPipeline.layerStripSU2_gammas_length A B (d + 1)
  refine ⟨(Qatlib.Concepts.NativeNumerics.NlfftPipeline.layerStripSU2 A B (d + 1)).gammas,
      ⟨hlen, h1⟩, ?_⟩
  rintro γ' ⟨hγlen, hγ⟩
  exact Qatlib.Concepts.NativeNumerics.NlfftPipeline.nlftSU2_injective (by rw [hγlen, hlen])
      (by rw [hγ, h1])

end Qatlib.Papers.InvFFTSU2Ni25.NlfftPipeline
