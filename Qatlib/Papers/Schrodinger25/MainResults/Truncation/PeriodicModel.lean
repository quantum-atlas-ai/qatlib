/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Schrodinger25.MainResults.Model

set_option backward.isDefEq.respectTransparency false

/-!
# Schrodinger25 — periodic truncated model (Section 5.3)

Fixed paper version: arXiv:2505.00370.  Source: eq. (5.2), p. 28–30; the
periodic solution `𝓦` used in Lemmas 5.4/5.5 and Theorem 5.3.

On the truncation interval `(−L, R)` the paper considers the same transport
equation (2.4) with **periodic boundary conditions** (5.2).  For the
diagonalized characteristic model of `Model.lean` this means folding the
characteristic footpoint `p − λ_j t` back into `(−L, R)` with period `R + L`:

  `𝓦_j(t,p) = ψ( periodize_{L,R}(p − λ_j t) ) u_j`.

This is the object against which the exact solution `w` is compared in
Theorem 5.3 (truncation error).  `periodize` is `Int.fract`-based:
`periodize L R q = −L + fract((q+L)/(R+L)) · (R+L)`, which maps `ℝ` onto the
half-open fundamental domain `[−L, −L + (R+L)) = [−L, R)`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.Schrodinger25.MainResults.Truncation

open Qatlib.Papers.Schrodinger25.MainResults

variable {ι : Type*} [Fintype ι]

/-- Period of the truncation window `(−L, R)`: `R + L`. -/
def periodLength (L R : ℝ) : ℝ := R + L

/-- Fold a real number into the fundamental domain `[−L, R)` of period `R + L`:
`periodize L R q = −L + fract((q+L)/(R+L)) · (R+L)`. -/
def periodize (L R q : ℝ) : ℝ :=
  -L + Int.fract ((q + L) / (R + L)) * (R + L)

/-- The periodic truncated solution `𝓦` of (5.2) at time `t`, in the
diagonalized characteristic model: `𝓦_j(t,p) = ψ(periodize_{L,R}(p−λ_j t))u_j`. -/
def periodicSolutionW (ψ : ℝ → ℂ) (lam : ι → ℝ) (u : ι → ℂ) (L R : ℝ) (t p : ℝ) : ι → ℂ :=
  fun j => ψ (periodize L R (p - lam j * t)) * u j

/-- Boundary flux `∑_j λ_j ‖𝓦_j(t,p)‖²` of the periodic solution at spatial
point `p`, the quantity integrated in Lemmas 5.4/5.5. -/
def fluxTraceW (ψ : ℝ → ℂ) (lam : ι → ℝ) (u : ι → ℂ) (L R : ℝ) (t p : ℝ) : ℝ :=
  ∑ j, lam j * ‖periodicSolutionW ψ lam u L R t p j‖ ^ 2

end Qatlib.Papers.Schrodinger25.MainResults.Truncation
