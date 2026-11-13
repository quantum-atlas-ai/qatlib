/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation
import Qatlib.Concepts.RandCompile.ChannelBudget.SingularValues

/-!
# Statement of threshold rank retention

`ThresholdRankRetention` states a sufficient condition for two successive Gram approximations to
retain the first `k` singular values above a given threshold. The condition compares `τ² + 2 *
η₁ + 2 * η₂` with the squared source singular value, supporting the truncated sketch analysis of
[ChiaEtAl2022].

## Main statements

* `ThresholdRankRetention`: The proposition that the stated dimension, positivity, Gram error,
  and squared-gap hypotheses force all sketch singular values indexed below `k` to be at least
  `τ`.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Concepts.SketchSpectral.EvenSVT

open Matrix
open scoped Matrix.Norms.L2Operator

/-- The proposition that the stated dimension, positivity, Gram error, and squared-gap
hypotheses force all sketch singular values indexed below `k` to be at least `τ`. -/
def ThresholdRankRetention : Prop :=
  ∀ (K C RS CT : Type) [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    [Fintype RS] [DecidableEq RS] [Fintype CT] [DecidableEq CT]
    (A : Matrix K C ℂ) (R : Matrix RS C ℂ) (Cc : Matrix RS CT ℂ) (k : ℕ) (η₁ η₂ τ : ℝ),
    0 ≤ η₁ → 0 ≤ η₂ → k ≤ Fintype.card RS → k ≤ Fintype.card C →
    0 < Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A k →
    Qatlib.Concepts.SpectralSketch.SpectrumPerturb.spectralFrobenius (Rᴴ*R - Aᴴ*A) ≤ η₁ →
    Qatlib.Concepts.SpectralSketch.SpectrumPerturb.spectralFrobenius (Cc*Ccᴴ - R*Rᴴ) ≤ η₂ →
    τ*τ + 2*η₁ + 2*η₂ ≤ (Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A k)^2 →
    ∀ i : ℕ, i < k → τ ≤ Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues Cc i

end Qatlib.Concepts.SketchSpectral.EvenSVT
