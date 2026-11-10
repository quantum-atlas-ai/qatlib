/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation
import Qatlib.Concepts.RandCompile.ChannelBudget.SingularValues
set_option warningAsError false

open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Concepts.SketchSpectral.EvenSVT

open Matrix
open scoped Matrix.Norms.L2Operator

def TruncatedSketchSecondIsometry : Prop :=
  ∀ (C RS CT : Type) [Fintype C] [DecidableEq C] [Fintype RS] [DecidableEq RS]
    [Fintype CT] [DecidableEq CT]
    (R : Matrix RS C ℂ) (Cc : Matrix RS CT ℂ) (τ α η₂ : ℝ),
    0 < τ → 0 ≤ α → 0 ≤ η₂ →
    Qatlib.Concepts.SpectralSketch.SpectrumPerturb.spectralFrobenius (Cc*Ccᴴ - R*Rᴴ) ≤ η₂ →
    η₂ ≤ τ*τ*α →
    ‖Matrix.diagonal
        (fun i : Fin (Fintype.card RS) =>
          if τ ≤ Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues Cc i
          then ((Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues Cc i)⁻¹ : ℂ) else 0) *
      (Qatlib.Concepts.WalkSearch.Spectral.basisColumns
        (Qatlib.Concepts.RandCompile.ChannelBudget.rightSingularBasis Ccᴴ))ᴴ *
      R*Rᴴ*
      Qatlib.Concepts.WalkSearch.Spectral.basisColumns
        (Qatlib.Concepts.RandCompile.ChannelBudget.rightSingularBasis Ccᴴ) *
      (Matrix.diagonal
        (fun i : Fin (Fintype.card RS) =>
          if τ ≤ Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues Cc i
          then ((Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues Cc i)⁻¹ : ℂ) else 0))ᴴ -
      Matrix.diagonal
        (fun i : Fin (Fintype.card RS) =>
          if τ ≤ Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues Cc i then (1:ℂ) else 0)‖
      ≤ α

end Qatlib.Concepts.SketchSpectral.EvenSVT
