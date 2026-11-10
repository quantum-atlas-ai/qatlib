/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchArith.TransposeAccess.CompactSketchConsumers
import Qatlib.Concepts.RandCompile.ChannelBudget.SingularValues
set_option warningAsError false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib.Concepts.SketchArith.SketchBuild

namespace Qatlib.Concepts.SketchSpectral.SketchAnalysis

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

def SketchSingularValueL2Stability : Prop :=
  ∀ (K C : Type) [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    (A : Matrix K C ℂ) (r c : ℕ) (ε δ φ₁ φ₂ : ℝ)
    (qs : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist K)
    (condQ : (Fin r → K) → Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist C),
    0 < r → 0 < c → 1 ≤ φ₁ → 1 ≤ φ₂ → 0 < ε → 0 < δ → δ < 1 →
    0 < Qatlib.Concepts.SketchArith.SketchBuild.sketchSquared A →
    (∀ i, Qatlib.Concepts.SketchArith.SketchBuild.sketchRowSquared A i/(φ₁*Qatlib.Concepts.SketchArith.SketchBuild.sketchSquared A) ≤
      qs.prob i) →
    (∀ (v : Fin r → K),
      0 < Qatlib.Concepts.SketchArith.SketchBuild.sketchSquared
        ((Qatlib.Concepts.SketchArith.SketchBuild.compactSketched (Qatlib.Concepts.SketchArith.SketchBuild.compactSketchData qs r v) A)ᴴ) →
      ∀ j, Qatlib.Concepts.SketchArith.SketchBuild.sketchRowSquared
          ((Qatlib.Concepts.SketchArith.SketchBuild.compactSketched (Qatlib.Concepts.SketchArith.SketchBuild.compactSketchData qs r v) A)ᴴ) j/
        (φ₂*Qatlib.Concepts.SketchArith.SketchBuild.sketchSquared
          ((Qatlib.Concepts.SketchArith.SketchBuild.compactSketched (Qatlib.Concepts.SketchArith.SketchBuild.compactSketchData qs r v) A)ᴴ)) ≤
        (condQ v).prob j) →
    (Real.sqrt (8*φ₁^2*Real.log (2/(δ/2))/(r : ℝ))*Qatlib.Concepts.SketchArith.SketchBuild.sketchSquared A +
      Real.sqrt (8*φ₂^2*Real.log (2/(δ/2))/(c : ℝ))*(φ₁*Qatlib.Concepts.SketchArith.SketchBuild.sketchSquared A) ≤
      ε*Qatlib.Concepts.SketchArith.SketchBuild.sketchSquared A) →
    ∃ Q : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist ((Fin r → K) × (Fin c → C)),
      (∀ (v : Fin r → K) (w : Fin c → C),
        Q.prob (v, w) = qs.probOf v*(condQ v).probOf w) ∧
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent Q
        (fun ω : Fin 1 → ((Fin r → K) × (Fin c → C)) =>
          ε*Qatlib.Concepts.SketchArith.SketchBuild.sketchSquared A <
          Real.sqrt (∑ i ∈ Finset.range (min (Fintype.card K) (Fintype.card C)),
            ((Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues
              ((Qatlib.Concepts.SketchArith.SketchBuild.compactSketched
                  (Qatlib.Concepts.SketchArith.SketchBuild.compactSketchData (condQ (ω 0).1) c (ω 0).2)
                  ((Qatlib.Concepts.SketchArith.SketchBuild.compactSketched
                      (Qatlib.Concepts.SketchArith.SketchBuild.compactSketchData qs r (ω 0).1) A)ᴴ))ᴴ) i)^2 -
              (Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i)^2)^2)) ≤ δ

end Qatlib.Concepts.SketchSpectral.SketchAnalysis
