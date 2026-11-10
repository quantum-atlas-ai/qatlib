/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LcuPostselect.ScaledLCU.ApproximateCoefficientLCU
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.TrotterFormula.LieStrang.AnticommutingPropagator
open Matrix
open scoped Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

def shiftedGenerator (P Q : Matrix I I ℂ) (a ω : ℝ) : Matrix I I ℂ :=
  (Complex.I * (ω : ℂ)) • P + (a : ℂ) • Q

def rescaledStep (P Q : Matrix I I ℂ) (a ω c s : ℝ) : Matrix I I ℂ :=
  (c : ℂ) • 1 + (s : ℂ) • shiftedGenerator P Q a ω

def rescaledCoefficients (a ω c s : ℝ) : Fin 3 → ℂ :=
  ![(c : ℂ), Complex.I * (ω : ℂ) * (s : ℂ), (a : ℂ) * (s : ℂ)]

def rescaledUnitaries (P Q : Matrix I I ℂ) : Fin 3 → Matrix I I ℂ := ![1, P, Q]

end Qatlib.Concepts.TrotterFormula.LieStrang.AnticommutingPropagator
