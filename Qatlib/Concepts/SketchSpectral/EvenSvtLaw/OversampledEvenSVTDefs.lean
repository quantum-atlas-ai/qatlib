/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchSpectral.EvenSvtLaw.EvenSVTFrobeniusActualRecordsSamp
import Qatlib.Concepts.SketchArith.SketchBuild.SketchFrobeniusConcentration

/-!
# Oversampled even SVT run data

`OversampledEvenSVTRun` stores row and column records, their access counters, both sketch
matrices, and the final matrix-function output. `oversampledEvenSVTRun` constructs these values
from actual compact builders and forms `Rᴴ * fbar(Cc * Ccᴴ) * R + f(0) I`, following the
two-sketch construction in [ChiaEtAl2022].

## Main statements

* `OversampledEvenSVTRun`: The row and column records, indexed data, sampling counters, sketch
  matrices, and output matrix of an oversampled even-SVT run.
* `oversampledEvenSVTRun`: Constructs an even-SVT run from row and conditional-column samples,
  retrieving its indexed data from the built records and forming `Rᴴ * fbar(Cc * Ccᴴ) * R + f(0)
  I`.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option warningAsError false

set_option autoImplicit false
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SketchArith.SketchBuild

open Qatlib.Concepts.SpectralSketch.SpectrumPerturb

namespace Qatlib.Concepts.SketchSpectral.EvenSvtLaw
noncomputable section

/-- The row and column records, indexed data, sampling counters, sketch matrices, and output
matrix of an oversampled even-SVT run. -/
structure OversampledEvenSVTRun (K C : Type) (r c : ℕ) where
  rowRecords : List (K × ℝ)
  columnRecords : List (C × ℝ)
  rowData : Fin r → K × ℝ
  columnData : Fin c → C × ℝ
  rowSamplerCalls : ℕ
  rowProbabilityReads : ℕ
  columnSamplerCalls : ℕ
  columnProbabilityReads : ℕ
  rows : Matrix (Fin r) C ℂ
  columns : Matrix (Fin r) (Fin c) ℂ
  output : Matrix C C ℂ
end
noncomputable section

/-- Constructs an even-SVT run from row and conditional-column samples, retrieving its indexed
data from the built records and forming `Rᴴ * fbar(Cc * Ccᴴ) * R + f(0) I`. -/
def oversampledEvenSVTRun {K C : Type} [Fintype K] [DecidableEq K]
    [Fintype C] [DecidableEq C] (A : Matrix K C ℂ) (r c : ℕ)
    (f fbar : ℝ → ℂ) (qs : FinDist K)
    (condQ : (Fin r → K) → FinDist C) (v : Fin r → K) (w : Fin c → C) :
    OversampledEvenSVTRun K C r c :=
  let rowRun := compactSketchBuild qs r v
  let rowData : Fin r → K × ℝ := fun i => rowRun.1[i.val]'(by
    simpa only [rowRun, compactSketchBuild_eq, List.length_ofFn] using! i.isLt)
  let R := compactSketched rowData A
  let columnRun := compactSketchBuild (condQ v) c w
  let columnData : Fin c → C × ℝ := fun i => columnRun.1[i.val]'(by
    simpa only [columnRun, compactSketchBuild_eq, List.length_ofFn] using! i.isLt)
  let Cmat := (compactSketched columnData Rᴴ)ᴴ
  { rowRecords := rowRun.1
    columnRecords := columnRun.1
    rowData := rowData
    columnData := columnData
    rowSamplerCalls := rowRun.2.1
    rowProbabilityReads := rowRun.2.2
    columnSamplerCalls := columnRun.2.1
    columnProbabilityReads := columnRun.2.2
    rows := R
    columns := Cmat
    output := Rᴴ * hermitianFunction (Cmat * Cmatᴴ)
      (Matrix.isHermitian_mul_conjTranspose_self Cmat) fbar * R +
        (f 0 : ℂ) • (1 : Matrix C C ℂ) }
end
end Qatlib.Concepts.SketchSpectral.EvenSvtLaw
