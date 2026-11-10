/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.PhaseExistence.PaperQsvtEndpoint
import Qatlib.Concepts.QsvtCore.ApproxToolkit.QsvtCoreRefined
import Qatlib.Concepts.QsvtCore.ApproxToolkit.DolphWindow
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QsvtCore.ApproxToolkit
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QsvtCore.PhaseExistence

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSingValue19.AlgorithmApps

open scoped Matrix.Norms.L2Operator

open Polynomial
open scoped Classical BigOperators

open Qatlib

noncomputable def paperApplicationWindow (ε δ : ℝ) : Polynomial ℝ :=
  Qatlib.Concepts.QsvtCore.ApproxToolkit.dolphWindowPolynomial ε
    (Qatlib.Concepts.QsvtCore.ApproxToolkit.dolphWindowDegree ε δ)

def PaperEndpointNext : Prop :=
  (∀ (Φ : List ℝ),
      Qatlib.Concepts.QsvtCore.PhaseExistence.paperLedger
        ((Qatlib.Concepts.QsvtCore.PhaseExistence.def15Ledger
            (Qatlib.Concepts.QsvtCore.PhaseExistence.def15Steps Φ .odd)).forwardQueries +
          (Qatlib.Concepts.QsvtCore.PhaseExistence.def15Ledger
            (Qatlib.Concepts.QsvtCore.PhaseExistence.def15Steps Φ .odd)).adjointQueries)
        ((Qatlib.Concepts.QsvtCore.PhaseExistence.def15Ledger
            (Qatlib.Concepts.QsvtCore.PhaseExistence.def15Steps Φ .odd)).projectorNotP +
          (Qatlib.Concepts.QsvtCore.PhaseExistence.def15Ledger
            (Qatlib.Concepts.QsvtCore.PhaseExistence.def15Steps Φ .odd)).projectorNotQ)
        (Qatlib.Concepts.QsvtCore.PhaseExistence.def15Ledger
            (Qatlib.Concepts.QsvtCore.PhaseExistence.def15Steps Φ .odd)).phaseMacros 1
        = Qatlib.Concepts.QsvtCore.PhaseExistence.paperOddWordLedger Φ.length) ∧
  (∀ (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      Qatlib.Concepts.QsvtCore.ApproxToolkit.DolphFlatCenter
        (paperApplicationWindow ε δ) ε (1 - δ)) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] (A B : Matrix I I ℂ)
      (hA : A.IsHermitian) (hB : B.IsHermitian) (p : Polynomial ℝ),
      ‖A‖ ≤ 1 → ‖B‖ ≤ 1 →
        ‖hermitianFunction A hA (fun x : ℝ => ((p.eval x : ℝ) : ℂ)) -
          hermitianFunction B hB (fun x : ℝ => ((p.eval x : ℝ) : ℂ))‖ ≤
          Qatlib.Concepts.QsvtCore.PhaseExistence.modulusRobustnessFactor ‖A - B‖ *
            Qatlib.Concepts.QsvtCore.ApproxToolkit.polynomialResponseModulus p ‖A - B‖)

end Qatlib.Papers.QSingValue19.AlgorithmApps
