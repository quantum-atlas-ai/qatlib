/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeStandardPhaseConvention

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

/-!
# Phase Convention

The exact source convention or stability contract is consumed with all original parameters and hypotheses.
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QSPHaah19.Theory
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Polynomial
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data

/-- The exact source convention or stability contract is consumed with all original parameters and hypotheses. -/
theorem native_standard_quarter_response (base : ℂ) (zs : List ℂ) :
    responseP ((-Complex.I)*base) (zs.map (fun z => (-Complex.I)*z))=
      C ((-Complex.I)^(zs.length+1))*standardResponseP base zs ∧
    responseQ ((-Complex.I)*base) (zs.map (fun z => (-Complex.I)*z))=
      C ((-Complex.I)^zs.length)*standardResponseQ base zs :=
  Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.native_standard_quarter_response base zs

/-- The exact source convention or stability contract is consumed with all original parameters and hypotheses. -/
theorem nativePacketFromStandard_matrix_real_imag (data : PhaseData) (x s : ℝ)
    (hs : s*s=1-x*x) :
    ((responseP (gaussianRatComplex (nativePacketFromStandard data).base)
      ((nativePacketFromStandard data).phases.map gaussianRatComplex)).eval (x : ℂ)).re=
    (standardMatrixWord (gaussianRatComplex data.base) x s
      (data.phases.map gaussianRatComplex) false false).im :=
  Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.nativePacketFromStandard_matrix_real_imag data x s hs

end Qatlib.Papers.QSPHaah19.Theory
