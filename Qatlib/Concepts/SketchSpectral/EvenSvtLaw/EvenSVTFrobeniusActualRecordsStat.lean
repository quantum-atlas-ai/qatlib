/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.HermitianFunctionStability
import Qatlib.Concepts.SketchArith.TransposeAccess.CompactSketchConsumers

/-!
# Statement of actual-record SVT Frobenius accuracy

`EvenSVTFrobeniusActualRecords` specifies the joint distribution of exact row records and
conditional column records. Positive sample sizes, spectral-band regularity, and explicit Gram
error budgets imply that the two-sketch approximation to `f(Aᴴ * A)` exceeds Frobenius error `ε`
with probability at most `δ`, in the setting of [ChiaEtAl2022].

## Main statements

* `EvenSVTFrobeniusActualRecords`: The proposition that exact squared-norm sampling with
  positive sample sizes and the stated spectral regularity and error budgets yields a joint
  record law with even-SVT Frobenius failure probability at most `δ`.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option warningAsError false

open Qatlib.Concepts.SketchArith.SketchBuild

namespace Qatlib.Concepts.SketchSpectral.EvenSvtLaw

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The proposition that exact squared-norm sampling with positive sample sizes and the stated
spectral regularity and error budgets yields a joint record law with even-SVT Frobenius
failure probability at most `δ`. -/
def EvenSVTFrobeniusActualRecords : Prop :=
  ∀ (K C : Type) [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    (A : Matrix K C ℂ) (r c : ℕ) (f fbar : ℝ → ℂ) (L Lbar d ε δ η₁ η₂ : ℝ)
    (qs : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist K)
    (condQ : (Fin r → K) → Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist C),
    0 < r → 0 < c →
    0 < L → 0 < Lbar → 0 < d → 0 < ε → 0 < δ → δ < 1 →
    0 < Qatlib.Concepts.SketchArith.SketchBuild.sketchSquared A →
    η₁ = Real.sqrt (8 * Real.log (2 / (δ / 3)) / (r : ℝ)) * Qatlib.Concepts.SketchArith.SketchBuild.sketchSquared A →
    η₂ = Real.sqrt (8 * Real.log (2 / (δ / 3)) / (c : ℝ)) * (2 * Qatlib.Concepts.SketchArith.SketchBuild.sketchSquared A) →
    Real.log (2 / (δ / 3)) / (2 * r : ℝ) ≤ 1 →
    L * η₁ ≤ ε / 2 →
    (‖Aᴴ * A‖ + η₁) * Lbar * η₂ ≤ ε / 2 →
    η₁ + η₂ ≤ d →
    (∀ i, qs.prob i = Qatlib.Concepts.SketchArith.SketchBuild.sketchRowSquared A i / Qatlib.Concepts.SketchArith.SketchBuild.sketchSquared A) →
    (∀ (v : Fin r → K) (j : C),
        0 < Qatlib.Concepts.SketchArith.SketchBuild.sketchSquared
          ((Qatlib.Concepts.SketchArith.SketchBuild.compactSketched
              (Qatlib.Concepts.SketchArith.SketchBuild.compactSketchData qs r v) A)ᴴ) →
        (condQ v).prob j = Qatlib.Concepts.SketchArith.SketchBuild.sketchRowSquared
            ((Qatlib.Concepts.SketchArith.SketchBuild.compactSketched
                (Qatlib.Concepts.SketchArith.SketchBuild.compactSketchData qs r v) A)ᴴ) j /
          Qatlib.Concepts.SketchArith.SketchBuild.sketchSquared
            ((Qatlib.Concepts.SketchArith.SketchBuild.compactSketched
                (Qatlib.Concepts.SketchArith.SketchBuild.compactSketchData qs r v) A)ᴴ)) →
    (∀ x y : ℝ,
        ((∃ i : Fin (Fintype.card C), |x - Qatlib.Concepts.SpectralSketch.SpectrumPerturb.orderedHermitianValues
              (Matrix.isHermitian_conjTranspose_mul_self A) i| ≤ d) ∨ x = 0) →
        ((∃ j : Fin (Fintype.card C), |y - Qatlib.Concepts.SpectralSketch.SpectrumPerturb.orderedHermitianValues
              (Matrix.isHermitian_conjTranspose_mul_self A) j| ≤ d) ∨ y = 0) →
        ‖f x - f y‖ ≤ L * |x - y|) →
    (∀ x y : ℝ,
        ((∃ i : Fin (Fintype.card C), |x - Qatlib.Concepts.SpectralSketch.SpectrumPerturb.orderedHermitianValues
              (Matrix.isHermitian_conjTranspose_mul_self A) i| ≤ d) ∨ x = 0) →
        ((∃ j : Fin (Fintype.card C), |y - Qatlib.Concepts.SpectralSketch.SpectrumPerturb.orderedHermitianValues
              (Matrix.isHermitian_conjTranspose_mul_self A) j| ≤ d) ∨ y = 0) →
        ‖fbar x - fbar y‖ ≤ Lbar * |x - y|) →
    (∀ x : ℝ, 0 < x →
        (∃ i : Fin (Fintype.card C), |x - Qatlib.Concepts.SpectralSketch.SpectrumPerturb.orderedHermitianValues
              (Matrix.isHermitian_conjTranspose_mul_self A) i| ≤ d) →
        (fbar x * (x : ℝ)) = f x - (f 0 : ℂ)) →
    ∃ Q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist ((Fin r → K) × (Fin c → C)),
      (∀ (v : Fin r → K) (w : Fin c → C),
          Q.prob (v, w) = qs.probOf v * (condQ v).probOf w) ∧
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent Q
        (fun ω : Fin 1 → ((Fin r → K) × (Fin c → C)) =>
          ε < Qatlib.Concepts.SpectralSketch.SpectrumPerturb.spectralFrobenius
            ((Qatlib.Concepts.SketchArith.SketchBuild.compactSketched
                  (Qatlib.Concepts.SketchArith.SketchBuild.compactSketchData qs r (ω 0).1) A)ᴴ *
              Qatlib.Concepts.SpectralSketch.SpectrumPerturb.hermitianFunction
                ((Qatlib.Concepts.SketchArith.SketchBuild.compactSketched
                      (Qatlib.Concepts.SketchArith.SketchBuild.compactSketchData (condQ (ω 0).1) c (ω 0).2)
                    ((Qatlib.Concepts.SketchArith.SketchBuild.compactSketched
                        (Qatlib.Concepts.SketchArith.SketchBuild.compactSketchData qs r (ω 0).1) A)ᴴ))ᴴ *
                Qatlib.Concepts.SketchArith.SketchBuild.compactSketched
                  (Qatlib.Concepts.SketchArith.SketchBuild.compactSketchData (condQ (ω 0).1) c (ω 0).2)
                  ((Qatlib.Concepts.SketchArith.SketchBuild.compactSketched
                      (Qatlib.Concepts.SketchArith.SketchBuild.compactSketchData qs r (ω 0).1) A)ᴴ))
                (Matrix.isHermitian_conjTranspose_mul_self
                  (Qatlib.Concepts.SketchArith.SketchBuild.compactSketched
                    (Qatlib.Concepts.SketchArith.SketchBuild.compactSketchData (condQ (ω 0).1) c (ω 0).2)
                    ((Qatlib.Concepts.SketchArith.SketchBuild.compactSketched
                        (Qatlib.Concepts.SketchArith.SketchBuild.compactSketchData qs r (ω 0).1) A)ᴴ)))
                fbar *
              Qatlib.Concepts.SketchArith.SketchBuild.compactSketched
                (Qatlib.Concepts.SketchArith.SketchBuild.compactSketchData qs r (ω 0).1) A
              + (f 0 : ℂ) • (1 : Matrix C C ℂ)
            - Qatlib.Concepts.SpectralSketch.SpectrumPerturb.hermitianFunction (Aᴴ * A)
              (Matrix.isHermitian_conjTranspose_mul_self A) f)) ≤ δ

end Qatlib.Concepts.SketchSpectral.EvenSvtLaw
