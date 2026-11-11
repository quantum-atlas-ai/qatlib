/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchSpectral.EvenSvtLaw.OversampledEvenSVTProgram

/-!
# Statement of oversampled SVT record accuracy

`EvenSVTFrobeniusOversampledRecords` specifies a joint law for row records and conditional
column records with oversampling domination. Its conclusion bounds the probability of Frobenius
error greater than `ε` for `oversampledEvenSVTRun` under explicit concentration and spectral
regularity hypotheses, following [ChiaEtAl2022].

## Main statements

* `EvenSVTFrobeniusOversampledRecords`: The proposition that dominated row and
  conditional-column sampling, together with the stated spectral regularity and explicit error
  budgets, produces a joint record law whose even-SVT run output has Frobenius failure
  probability at most `δ`.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option warningAsError false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.SketchArith.SketchBuild
open Qatlib.Concepts.SketchSpectral.EvenSvtLaw
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.SketchSpectral.EvenSVT
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The proposition that dominated row and conditional-column sampling, together with the stated
spectral regularity and explicit error budgets, produces a joint record law whose even-SVT
run output has Frobenius failure probability at most `δ`. -/
def EvenSVTFrobeniusOversampledRecords : Prop :=
  ∀ (K C : Type) [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    (A : Matrix K C ℂ) (r c : ℕ) (f fbar : ℝ → ℂ) (L Lbar d ε δ η₁ η₂ φrow φcol : ℝ)
    (qs : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist K)
    (condQ : (Fin r → K) → Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist C),
    0 < r → 0 < c → 1 ≤ φrow → 1 ≤ φcol →
    0 < L → 0 < Lbar → 0 < d → 0 < ε → 0 < δ → δ < 1 →
    η₁ = Real.sqrt (8 * φrow ^ 2 * Real.log (2 / (δ / 3)) / (r : ℝ)) * Qatlib.Concepts.SketchArith.SketchBuild.sketchSquared A →
    η₂ = Real.sqrt (8 * φcol ^ 2 * Real.log (2 / (δ / 3)) / (c : ℝ)) * (2 * Qatlib.Concepts.SketchArith.SketchBuild.sketchSquared A) →
    φrow ^ 2 * Real.log (2 / (δ / 3)) / (2 * r : ℝ) ≤ 1 →
    L * η₁ ≤ ε / 2 →
    (‖Aᴴ * A‖ + η₁) * Lbar * η₂ ≤ ε / 2 →
    η₁ + η₂ ≤ d →
    (∀ i, Qatlib.Concepts.SketchArith.SketchBuild.sketchRowSquared A i / (φrow * Qatlib.Concepts.SketchArith.SketchBuild.sketchSquared A) ≤ qs.prob i) →
    (∀ (v : Fin r → K) (j : C),
        0 < Qatlib.Concepts.SketchArith.SketchBuild.sketchSquared
          ((Qatlib.Concepts.SketchArith.SketchBuild.compactSketched
              (Qatlib.Concepts.SketchArith.SketchBuild.compactSketchData qs r v) A)ᴴ) →
        Qatlib.Concepts.SketchArith.SketchBuild.sketchRowSquared
            ((Qatlib.Concepts.SketchArith.SketchBuild.compactSketched
                (Qatlib.Concepts.SketchArith.SketchBuild.compactSketchData qs r v) A)ᴴ) j /
          (φcol * Qatlib.Concepts.SketchArith.SketchBuild.sketchSquared
            ((Qatlib.Concepts.SketchArith.SketchBuild.compactSketched
                (Qatlib.Concepts.SketchArith.SketchBuild.compactSketchData qs r v) A)ᴴ)) ≤ (condQ v).prob j) →
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
            ((oversampledEvenSVTRun A r c f fbar qs condQ (ω 0).1 (ω 0).2).output -
              Qatlib.Concepts.SpectralSketch.SpectrumPerturb.hermitianFunction (Aᴴ * A)
                (Matrix.isHermitian_conjTranspose_mul_self A) f)) ≤ δ

end Qatlib.Concepts.SketchSpectral.EvenSVT
