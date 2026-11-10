/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false
noncomputable section
open Complex
namespace Qatlib.Concepts.QcaDynamics.ParityWeights

def P2 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

def eq24wm (θ ρ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.cos ρ : ℂ) • !![0, I * (Real.sin θ : ℂ); 0, (Real.cos θ : ℂ)]

def eq24wp (θ ρ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.cos ρ : ℂ) • !![(Real.cos θ : ℂ), 0; I * (Real.sin θ : ℂ), 0]

def eq24w0 (θ ρ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.sin ρ : ℂ) •
    !![(Real.sin θ : ℂ), -(I * (Real.cos θ : ℂ));
       -(I * (Real.cos θ : ℂ)), (Real.sin θ : ℂ)]

def Eq19 (wm w0 wp : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  wm * star wm + w0 * star w0 + wp * star wp = 1 ∧
  w0 * star wm + wp * star w0 = 0 ∧
  wp * star wm = 0

def ParityInvariant (wm w0 wp : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  wm = P2 * wp * P2 ∧ w0 = P2 * w0 * P2

end Qatlib.Concepts.QcaDynamics.ParityWeights
