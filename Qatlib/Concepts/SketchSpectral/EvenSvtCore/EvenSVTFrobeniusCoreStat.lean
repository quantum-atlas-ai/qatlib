/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.HermitianFunctionStability

/-!
# Statement of the even SVT Frobenius core

`EvenSVTFrobeniusCore` packages a deterministic error bound for `Rᴴ * fbar(Cc * Ccᴴ) * R`
relative to the shifted function `f(Aᴴ * A) - f(0) I`. Consistency of `fbar`, cross-spectrum
Lipschitz estimates, two Gram errors, and an inner Gram norm bound give the additive error
formula used in [ChiaEtAl2022].

## Main statements

* `EvenSVTFrobeniusCore`: The proposition that the stated spectral consistency, cross-spectrum
  Lipschitz, Gram error, and norm hypotheses bound the shifted even-SVT sandwich's Frobenius
  error by `L * η₁ + W * (Lbar * η₂)`.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

namespace Qatlib.Concepts.SketchSpectral.EvenSvtCore

open Matrix
open scoped Matrix.Norms.L2Operator

/-- The proposition that the stated spectral consistency, cross-spectrum Lipschitz, Gram error,
and norm hypotheses bound the shifted even-SVT sandwich's Frobenius error by `L * η₁ + W *
(Lbar * η₂)`. -/
def EvenSVTFrobeniusCore : Prop :=
  ∀ (K C RS CT : Type) [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    [Fintype RS] [DecidableEq RS] [Fintype CT] [DecidableEq CT]
    (A : Matrix K C ℂ) (R : Matrix RS C ℂ) (Cc : Matrix RS CT ℂ)
    (f fbar : ℝ → ℂ) (L Lbar η₁ η₂ W : ℝ),
    0 ≤ L → 0 ≤ Lbar → 0 ≤ η₁ → 0 ≤ η₂ →
    (∀ i : Fin (Fintype.card C),
        fbar (Qatlib.Concepts.SpectralSketch.SpectrumPerturb.orderedHermitianValues
            (Matrix.isHermitian_conjTranspose_mul_self R) i) *
            (Qatlib.Concepts.SpectralSketch.SpectrumPerturb.orderedHermitianValues
            (Matrix.isHermitian_conjTranspose_mul_self R) i : ℝ)
          = f (Qatlib.Concepts.SpectralSketch.SpectrumPerturb.orderedHermitianValues
            (Matrix.isHermitian_conjTranspose_mul_self R) i) - (f 0 : ℂ)) →
    (∀ i j : Fin (Fintype.card C),
        ‖f (Qatlib.Concepts.SpectralSketch.SpectrumPerturb.orderedHermitianValues
              (Matrix.isHermitian_conjTranspose_mul_self R) i)
          - f (Qatlib.Concepts.SpectralSketch.SpectrumPerturb.orderedHermitianValues
              (Matrix.isHermitian_conjTranspose_mul_self A) j)‖
          ≤ L * |Qatlib.Concepts.SpectralSketch.SpectrumPerturb.orderedHermitianValues
              (Matrix.isHermitian_conjTranspose_mul_self R) i
            - Qatlib.Concepts.SpectralSketch.SpectrumPerturb.orderedHermitianValues
              (Matrix.isHermitian_conjTranspose_mul_self A) j|) →
    (∀ i j : Fin (Fintype.card RS),
        ‖fbar (Qatlib.Concepts.SpectralSketch.SpectrumPerturb.orderedHermitianValues
              (Matrix.isHermitian_mul_conjTranspose_self Cc) i)
          - fbar (Qatlib.Concepts.SpectralSketch.SpectrumPerturb.orderedHermitianValues
              (Matrix.isHermitian_mul_conjTranspose_self R) j)‖
          ≤ Lbar * |Qatlib.Concepts.SpectralSketch.SpectrumPerturb.orderedHermitianValues
              (Matrix.isHermitian_mul_conjTranspose_self Cc) i
            - Qatlib.Concepts.SpectralSketch.SpectrumPerturb.orderedHermitianValues
              (Matrix.isHermitian_mul_conjTranspose_self R) j|) →
    Qatlib.Concepts.SpectralSketch.SpectrumPerturb.spectralFrobenius (Rᴴ * R - Aᴴ * A) ≤ η₁ →
    Qatlib.Concepts.SpectralSketch.SpectrumPerturb.spectralFrobenius (Cc * Ccᴴ - R * Rᴴ) ≤ η₂ →
    ‖Rᴴ * R‖ ≤ W →
    Qatlib.Concepts.SpectralSketch.SpectrumPerturb.spectralFrobenius
        (Rᴴ * Qatlib.Concepts.SpectralSketch.SpectrumPerturb.hermitianFunction (Cc * Ccᴴ)
            (Matrix.isHermitian_mul_conjTranspose_self Cc) fbar * R
          - Qatlib.Concepts.SpectralSketch.SpectrumPerturb.hermitianFunction (Aᴴ * A)
            (Matrix.isHermitian_conjTranspose_mul_self A)
            (fun x => f x - (f 0 : ℂ)))
      ≤ L * η₁ + W * (Lbar * η₂)

end Qatlib.Concepts.SketchSpectral.EvenSvtCore
