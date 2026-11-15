/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.NativeNumerics.NlfftPipeline.NonlinearFourierSU2

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.NativeNumerics.NlfftPipeline

namespace Qatlib.Papers.InvFFTSU2Ni25.NlfftPipeline

open Polynomial

def Lemma2_2 : Prop :=
  ∀ (d : ℕ) (A B : Polynomial ℂ),
    A.natDegree ≤ d → B.natDegree ≤ d →
    A * Qatlib.Concepts.NativeNumerics.NlfftPipeline.conjRevN d A + B * Qatlib.Concepts.NativeNumerics.NlfftPipeline.conjRevN d B = X ^ d →
    (A.coeff 0).im = 0 → 0 < (A.coeff 0).re →
    ∃! γ : List ℂ, γ.length = d + 1 ∧ Qatlib.Concepts.NativeNumerics.NlfftPipeline.nlftSU2 γ = (A, B)

end Qatlib.Papers.InvFFTSU2Ni25.NlfftPipeline
