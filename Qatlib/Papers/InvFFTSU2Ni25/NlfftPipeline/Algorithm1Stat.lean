/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.NativeNumerics.NlfftPipeline.InverseNLFFTSU2

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.NativeNumerics.NlfftPipeline

namespace Qatlib.Papers.InvFFTSU2Ni25.NlfftPipeline

open Polynomial

def Algorithm1 : Prop :=
  ∀ (d : ℕ) (A B : Polynomial ℂ),
    A.natDegree ≤ d → B.natDegree ≤ d →
    A * Qatlib.Concepts.NativeNumerics.NlfftPipeline.conjRevN d A + B * Qatlib.Concepts.NativeNumerics.NlfftPipeline.conjRevN d B = X ^ d →
    (A.coeff 0).im = 0 → 0 < (A.coeff 0).re →
    let r := Qatlib.Concepts.NativeNumerics.NlfftPipeline.inverseNLFFTSU2 A B (d + 1)
    r.gammas.length = d + 1 ∧
    Qatlib.Concepts.NativeNumerics.NlfftPipeline.nlftSU2 r.gammas = (A, B) ∧
    r.eta = A ∧ r.xi = B ∧
    r.operations ≤ 2048 * (d + 1) * (Nat.clog 2 (d + 1) + 5) ^ 2

end Qatlib.Papers.InvFFTSU2Ni25.NlfftPipeline
