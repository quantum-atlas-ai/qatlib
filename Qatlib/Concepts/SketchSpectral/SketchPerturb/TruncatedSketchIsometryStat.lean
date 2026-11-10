/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation
import Qatlib.Concepts.CoherentSim.CoherentOAA.OddApproximation
import Qatlib.Concepts.RandCompile.ChannelBudget.SingularValues
set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError

namespace Qatlib.Concepts.SketchSpectral.SketchPerturb

open Matrix
open scoped Matrix.Norms.L2Operator

def TruncatedSketchIsometry : Prop :=
  ∀ (C RS CT : Type) [Fintype C] [DecidableEq C] [Fintype RS] [DecidableEq RS]
    [Fintype CT] [DecidableEq CT]
    (R : Matrix RS C ℂ) (Cc : Matrix RS CT ℂ) (τ α η₂ : ℝ),
    0 < τ → 0 ≤ α → 0 ≤ η₂ →
    Qatlib.Concepts.SpectralSketch.SpectrumPerturb.spectralFrobenius (Cc * Ccᴴ - R * Rᴴ) ≤ η₂ →
    η₂ ≤ τ * τ * α →
    ‖Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform Ccᴴ
          (fun x => if τ ≤ x then (x : ℂ)⁻¹ else 0) * R *
        (Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform Ccᴴ
          (fun x => if τ ≤ x then (x : ℂ)⁻¹ else 0) * R)ᴴ
      - Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform Ccᴴ
          (fun x => if τ ≤ x then (x : ℂ)⁻¹ else 0) * Cc * Ccᴴ *
        (Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform Ccᴴ
          (fun x => if τ ≤ x then (x : ℂ)⁻¹ else 0))ᴴ‖ ≤ α ∧
    Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform Ccᴴ
        (fun x => if τ ≤ x then (x : ℂ)⁻¹ else 0) * Cc * Ccᴴ *
      (Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform Ccᴴ
        (fun x => if τ ≤ x then (x : ℂ)⁻¹ else 0))ᴴ
      = Qatlib.Concepts.WalkSearch.Spectral.basisColumns (Qatlib.Concepts.RandCompile.ChannelBudget.rightSingularBasis Cc) *
        Matrix.diagonal
          (fun i : Fin (Fintype.card CT) =>
            if τ ≤ Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues Cc i then (1 : ℂ) else 0) *
        (Qatlib.Concepts.WalkSearch.Spectral.basisColumns (Qatlib.Concepts.RandCompile.ChannelBudget.rightSingularBasis Cc))ᴴ

end Qatlib.Concepts.SketchSpectral.SketchPerturb
