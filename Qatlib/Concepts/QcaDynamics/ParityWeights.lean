/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Parity invariant two component weights

Defines three parametrized two by two weight matrices and the matrix constraints `Eq19` and
`ParityInvariant`. These definitions express local unitarity equations and parity symmetry for
two component cellular dynamics in the setting of [Meyer1996a].

## Main statements

* `P2`: exchanges the two internal components.
* `eq24wm`: defines the negative displacement weight.
* `Eq19`: states three matrix unitarity equations.
* `ParityInvariant`: states parity relations between the weights.

## References

* [Meyer, 1996][Meyer1996a]
-/

set_option autoImplicit false
noncomputable section
open Complex
namespace Qatlib.Concepts.QcaDynamics.ParityWeights

/-- The two by two permutation matrix that exchanges the two components. -/
def P2 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- The negative displacement weight matrix parametrized by the real angles `θ` and `ρ`. -/
def eq24wm (θ ρ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.cos ρ : ℂ) • !![0, I * (Real.sin θ : ℂ); 0, (Real.cos θ : ℂ)]

/-- The positive displacement weight matrix parametrized by the real angles `θ` and `ρ`. -/
def eq24wp (θ ρ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.cos ρ : ℂ) • !![(Real.cos θ : ℂ), 0; I * (Real.sin θ : ℂ), 0]

/-- The zero displacement weight matrix parametrized by the real angles `θ` and `ρ`. -/
def eq24w0 (θ ρ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Real.sin ρ : ℂ) •
    !![(Real.sin θ : ℂ), -(I * (Real.cos θ : ℂ));
       -(I * (Real.cos θ : ℂ)), (Real.sin θ : ℂ)]

/-- The three matrix equations requiring total row normalization and vanishing correlations at
the two nonzero displacement separations. -/
def Eq19 (wm w0 wp : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  wm * star wm + w0 * star w0 + wp * star wp = 1 ∧
  w0 * star wm + wp * star w0 = 0 ∧
  wp * star wm = 0

/-- Parity symmetry of the weights: conjugation by `P2` exchanges `wm` and `wp` and fixes `w0`. -/
def ParityInvariant (wm w0 wp : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  wm = P2 * wp * P2 ∧ w0 = P2 * w0 * P2

end Qatlib.Concepts.QcaDynamics.ParityWeights
