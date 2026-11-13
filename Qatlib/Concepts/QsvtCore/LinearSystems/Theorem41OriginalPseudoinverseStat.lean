/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.QsVtMain.LengthQSVT
import Qatlib.Concepts.CoherentSim.CoherentOAA.Pseudoinverse
import Qatlib.Concepts.WalshMoment.Forrelation.ThresholdApproximation
import Qatlib.Concepts.BlockEncoding.Basic

/-!
# Statement of the threshold-sector pseudoinverse theorem

`Theorem41OriginalPseudoinverse` specifies a QSVT construction for a projected unitary encoding
whose nonzero singular values are bounded below by δ, with `0 < ε ≤ δ ≤ 1/2`. It requests a
bounded windowed reciprocal polynomial, a phase list, an exact encoding of its odd singular
transform, and explicit compilation counts.

The final estimate compares the adjoint transform with the scaled Moore–Penrose pseudoinverse
between threshold-sector operators. The statement is associated with Theorem 41 of
[GilyenSuLowWiebe2019].

## Main statements

* `Theorem41OriginalPseudoinverse`: defines the polynomial, circuit, and sector error guarantees
  as a proposition.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.WalshMoment.Forrelation

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Concepts.QsvtCore.LinearSystems

open Matrix Polynomial Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Matrix.Norms.L2Operator

/-- The proposition requesting a windowed reciprocal polynomial and real QSVT encoding for a
projected unitary encoding with a positive singular-value gap and 0 < ε ≤ δ ≤ 1/2. It
records phase length, parameter bounds, compilation counts, and an ε-bound for the
sector-projected scaled-pseudoinverse error [GilyenSuLowWiebe2019]. -/
def Theorem41OriginalPseudoinverse : Prop :=
  ∀ (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (ε δ : ℝ),
    ProjectedUnitaryEncoding A U L R → 0 < ε → ε ≤ δ → δ ≤ 1/2 →
    (∀ i : Fin (Fintype.card I), matrixSingularValues A i ≠ 0 →
      δ ≤ matrixSingularValues A i) →
    ∃ (Pw : Polynomial ℝ) (J k : ℕ) (Φ : List ℝ),
      Φ.length = 2*J+1+2*3^k ∧
      (2*J+1 : ℝ) ≤ 32*(2/δ)*Real.log (16/(δ*ε)) ∧
      ((3 : ℝ)^k) ≤ 3*(64/(δ*ε))^(12/(δ*δ)) ∧
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |Pw.eval x| ≤ 1) ∧
      Pw.eval 0 = 0 ∧
      (∀ x ∈ Set.Icc δ 1, |Pw.eval x - (δ/2)/x| ≤ ε) ∧
      ProjectedUnitaryEncoding
        (Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A
          (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))
        (sourceRealWord U (rangeProjector R) (rangeProjector L) Φ)
        (sourceAverageClean L) (sourceAverageClean R) ∧
      cppCounts (cppCompile (sourceRealFamily Φ)) =
        (2*J+1+2*3^k, 2*J+2*3^k, 2*J+2+2*3^k, 2*J+1+2*3^k) ∧
      let C : Matrix I O ℂ :=
        (Qatlib.Concepts.CoherentSim.CoherentOAA.oddSingularTransform A
          (fun x : ℝ => ((Pw.eval x : ℝ) : ℂ)))ᴴ
      let sectorR : Matrix I I ℂ :=
        1 - (rightThresholdProjection A 0 - rightThresholdProjection A δ)
      let sectorL : Matrix O O ℂ :=
        1 - (leftThresholdProjection A 0 - leftThresholdProjection A δ)
      ‖sectorR * C * sectorL - (δ/2 : ℂ) • (matrixPseudoinverse A * sectorL)‖ ≤ ε

end Qatlib.Concepts.QsvtCore.LinearSystems
