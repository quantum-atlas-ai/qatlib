/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation

/-!
# Statement of pointwise sketch singular value stability

This module defines `SketchSingularValueStability`, the fixed-matrix perturbation statement used
for two-stage sketches. Nonnegative Frobenius error bounds on RᴴR - AᴴA and CcCcᴴ - RRᴴ control
each squared singular value difference by 2η₁ + 2η₂ at indices below the minimum of the
row-sketch and source-column dimensions [ChiaEtAl2022].

## Main statements

* `SketchSingularValueStability`: the quantified two-Gram perturbation bound.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option warningAsError false

namespace Qatlib.Concepts.SketchSpectral.SketchPerturb

open Matrix
open scoped Matrix.Norms.L2Operator

/-- The statement that Frobenius errors at most `η₁` for RᴴR - AᴴA and `η₂` for CcCcᴴ - RRᴴ
bound the squared singular value difference by 2η₁ + 2η₂ at indices below the minimum of the
row-sketch and source-column dimensions. -/
def SketchSingularValueStability : Prop :=
  ∀ (K C RS CT : Type) [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    [Fintype RS] [DecidableEq RS] [Fintype CT] [DecidableEq CT]
    (A : Matrix K C ℂ) (R : Matrix RS C ℂ) (Cc : Matrix RS CT ℂ) (η₁ η₂ : ℝ),
    0 ≤ η₁ → 0 ≤ η₂ →
    Qatlib.Concepts.SpectralSketch.SpectrumPerturb.spectralFrobenius (Rᴴ * R - Aᴴ * A) ≤ η₁ →
    Qatlib.Concepts.SpectralSketch.SpectrumPerturb.spectralFrobenius (Cc * Ccᴴ - R * Rᴴ) ≤ η₂ →
    ∀ i : ℕ, i < min (Fintype.card RS) (Fintype.card C) →
      |(Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues Cc i) ^ 2 -
        (Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i) ^ 2| ≤ 2 * η₁ + 2 * η₂

end Qatlib.Concepts.SketchSpectral.SketchPerturb
