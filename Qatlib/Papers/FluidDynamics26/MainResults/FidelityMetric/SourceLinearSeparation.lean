/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FluidDynamics26.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# FluidDynamics26 — linear separation of the linearized Euler equations

Fixed source: Ameri–Carolan–Childs–Krovi, *Quantum lower bounds for simulating fluid
dynamics*, arXiv:2603.12161v1 (12 March 2026), Theorem 17, Eqs. (133)–(137), p. 23.

c015 = Theorem 17: for `0 < ε < min{1, 1/q}` there is a pair of solutions of the
linearized Euler equations, Eq. (132), p. 23, whose normalized overlaps at time `0` are
`1 - O(ε²)` and `≥ 1 - ε²`, and whose overlap at time `t` is sandwiched between the
explicit exponential bounds `g(t) ≤ ⟨u₀(t)|ũ(t)⟩ ≤ f(t)` of Eqs. (135)–(137).

Theorem 17 itself is not formalized (its proof needs the Fourier-mode construction of
Theorem 16 and the Parseval overlap computation); its statement is preserved in this
branch's history.  This file retains the overlap vocabulary (`vecFieldOverlap`,
`scalarFieldOverlap`) and the explicit bounds `separationUpper`/`separationLower` of
Eqs. (136)–(137) used to state it.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FluidDynamics26.MainResults

open MeasureTheory
open Qatlib.Foundations.PureStateMath

open scoped BigOperators

/-! ## Field overlaps -/

/-- Squared `L²` norm of a vector field on `𝕋^d`. -/
def vecFieldL2Sq {d : ℕ} (u : (Fin d → ℝ) → ℝ → Fin d → ℝ) (t : ℝ) : ℝ :=
  ∫ r in torusFund d, ∑ i, (u r t i) ^ 2

/-- `L²` inner product of two vector fields on `𝕋^d`. -/
def vecFieldInner {d : ℕ} (u v : (Fin d → ℝ) → ℝ → Fin d → ℝ) (t : ℝ) : ℝ :=
  ∫ r in torusFund d, ∑ i, u r t i * v r t i

/-- Normalized overlap `⟨u|v⟩ / (‖u‖ ‖v‖)` of two vector fields. -/
def vecFieldOverlap {d : ℕ} (u v : (Fin d → ℝ) → ℝ → Fin d → ℝ) (t : ℝ) : ℝ :=
  vecFieldInner u v t / Real.sqrt (vecFieldL2Sq u t * vecFieldL2Sq v t)

/-- `L²` inner product of two scalar fields on `𝕋²`. -/
def scalarFieldInner (f g : (Fin 2 → ℝ) → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ r in torusFund 2, f r t * g r t

/-- Squared `L²` norm of a scalar field on `𝕋²`. -/
def scalarFieldL2Sq (f : (Fin 2 → ℝ) → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ r in torusFund 2, (f r t) ^ 2

/-- Normalized overlap of two scalar fields. -/
def scalarFieldOverlap (f g : (Fin 2 → ℝ) → ℝ → ℝ) (t : ℝ) : ℝ :=
  scalarFieldInner f g t / Real.sqrt (scalarFieldL2Sq f t * scalarFieldL2Sq g t)

/-! ## The explicit bounds of Eqs. (136)–(137), p. 23 -/

/-- `f(t)` of Eq. (136), p. 23 (upper bound on the overlap, governed by `γ_l`). -/
def separationUpper (ε γl : ℝ) (t : ℝ) : ℝ :=
  Real.sqrt ((1 - ε ^ 2) / (1 + ε ^ 2 * (Real.exp (2 * γl * t) - 1)))

/-- `g(t)` of Eq. (137), p. 23 (lower bound on the overlap, governed by `γ_u`). -/
def separationLower (ε γu : ℝ) (t : ℝ) : ℝ :=
  Real.sqrt ((1 - ε ^ 2) / (1 + ε ^ 2 * (Real.exp (2 * γu * t) - 1)))

end Qatlib.Papers.FluidDynamics26.MainResults
