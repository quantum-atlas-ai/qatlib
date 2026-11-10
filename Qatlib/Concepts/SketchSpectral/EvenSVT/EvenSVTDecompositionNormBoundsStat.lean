/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.HermitianFunctionStability
import Qatlib.Concepts.SketchArith.TransposeAccess.CompactSketchConsumers
set_option warningAsError false

open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SketchArith.SketchBuild

namespace Qatlib.Concepts.SketchSpectral.EvenSVT

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

def EvenSVTDecompositionNormBounds : Prop :=
  ∀ (K C RS CT : Type) [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    [Fintype RS] [DecidableEq RS] [Fintype CT] [DecidableEq CT]
    (A : Matrix K C ℂ) (R : Matrix RS C ℂ) (T : Matrix C CT ℂ)
    (g : ℝ → ℂ) (η₁ η₂ L : ℝ),
    0 ≤ η₁ → 0 ≤ η₂ →
    Qatlib.Concepts.SpectralSketch.SpectrumPerturb.spectralFrobenius (Rᴴ*R - Aᴴ*A) ≤ η₁ →
    Qatlib.Concepts.SpectralSketch.SpectrumPerturb.spectralFrobenius ((R*T)*(R*T)ᴴ - R*Rᴴ) ≤ η₂ →
    0 ≤ L →
    (∀ x y : ℝ,
      (∃ i : ℕ, i < Fintype.card RS ∧
        |x - (Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i)^2| ≤
          2*η₁ + 2*η₂) →
      (∃ i : ℕ, i < Fintype.card RS ∧
        |y - (Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i)^2| ≤
          2*η₁ + 2*η₂) →
      ‖g x - g y‖ ≤ L * |x-y|) →
    ‖Rᴴ*R‖ ≤ ‖Aᴴ*A‖ + η₁ ∧
    (∃ B : ℝ,
      (∀ x : ℝ,
        ((∃ i : ℕ, i < Fintype.card RS ∧
          |x - (Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i)^2| ≤
            2*η₁ + 2*η₂) ∨ x = 0) →
        ‖g x‖ ≤ B) ∧
      ‖Qatlib.Concepts.SpectralSketch.SpectrumPerturb.hermitianFunction ((R*T)*(R*T)ᴴ)
          (Matrix.isHermitian_mul_conjTranspose_self (R*T)) g‖ ≤ B) ∧
    ∀ B : ℝ, 0 ≤ B →
      (∀ x : ℝ,
        ((∃ i : ℕ, i < Fintype.card RS ∧
          |x - (Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i)^2| ≤
            2*η₁ + 2*η₂) ∨ x = 0) → ‖g x‖ ≤ B) →
      ‖Qatlib.Concepts.SpectralSketch.SpectrumPerturb.hermitianFunction ((R*T)*(R*T)ᴴ)
          (Matrix.isHermitian_mul_conjTranspose_self (R*T)) g‖ ≤ B

end Qatlib.Concepts.SketchSpectral.EvenSVT
