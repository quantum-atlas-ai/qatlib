/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalGibbs09.MainResults.Prelude

set_option backward.isDefEq.respectTransparency false

/-!
# ThermalGibbs09 — Appendix A: simulation error for the effective Hamiltonian

Poulin--Wocjan, fixed arXiv:0905.2199, Appendix A (eqs. (A1)--(A14), p. 5-6).

Claim `c003`: let `H` be self-adjoint with `‖H‖ ≤ π/(4t)` and `U = e^{itH}`.
If `Ũ` is a unitary with `‖U - Ũ‖ ≤ ε` (obtained by Hamiltonian simulation),
then there is a self-adjoint `H̃` with `e^{itH̃} = Ũ` and
`‖H - H̃‖ ≤ κ ε / t` for a small constant `κ` (the paper's `K ≤ 6π + 12`).

## Original proof route (Appendix A)

1. `U` and `Ũ` are unitary and, for `ε ≤ 1/4`, their spectra lie in the
   contour interior `I(γ)` and avoid `-1` (p. 5, the paragraph bounding
   `|λ̃|`).
2. The principal matrix logarithm `Log` satisfies `e^{Log A} = A` (eq. (A13))
   and `Log U = i t H`, so `H̃ := -(i/t) Log Ũ` is self-adjoint and
   `e^{itH̃} = Ũ`.
3. The contour integral (A12) and the resolvent estimates (A19)--(A25)
   give the Lipschitz bound `‖Log A - Log B‖ ≤ K‖A - B‖` with `K ≤ 6π+12`
   (eq. (A14), choosing `R = 2`).
4. Combining turns `‖U - Ũ‖ ≤ ε` into `t‖H - H̃‖ ≤ K ε`.

## Scope and related matrix-logarithm results

* Self-adjoint logarithms of unitaries and the identity
  `expUnitary (argSelfAdjoint u) = u` exist in Mathlib:
  `Unitary.argSelfAdjoint` and `expUnitary_argSelfAdjoint`
  (`Mathlib.Analysis.CStarAlgebra.Unitary.Connected`, with
  `Mathlib.Analysis.CStarAlgebra.Matrix` supplying the C⋆-algebra structure
  on `Matrix I I ℂ`). `Unitary.norm_sub_eq` gives the relative form.
* The quantitative Lipschitz estimate (A14)
  `‖argSelfAdjoint u - argSelfAdjoint v‖ ≤ K‖u - v‖` for `u, v` in the ball
  `‖u - 1‖ < 2`, together with the transfer of the norm bound through the
  `1/t` rescaling of `H̃`, is outside the scope of this file. Mathlib provides
  the exact modulus `Unitary.norm_argSelfAdjoint` for a single `u`, but no
  two-point Lipschitz constant.
* A differential approach to the two-point bound would study
  `t ↦ argSelfAdjoint (expUnitary (t • x))` along a path from `u` to `v`
  (related constructions are `Unitary.path` and `Unitary.joined`). The relevant
  derivative bounds are the contour estimates `(R-1)⁻¹`, `R/(R-1)`, `2` of
  Appendix A; at `R = 2` these give the paper's constant `K = 6π + 12`.

## Formalization scope

Scope note: the quantitative statement of claim `c003`, including the
two-point Lipschitz estimate (A14), is described here in prose. This file
does not provide a theorem asserting that bound.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace Qatlib.Papers.ThermalGibbs09.MainResults.EffectiveHamiltonian

open Qatlib.Papers.ThermalGibbs09.MainResults

variable {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

/- **arXiv:0905.2199, Appendix A (eq. (A14), p. 5-6).** The paper's
guarantee: let `H` be a self-adjoint Hamiltonian with `‖H‖ ≤ π/(4t)`, let
`U = e^{itH}`, and let `Ũ` be a unitary with `‖U - Ũ‖ ≤ ε` where
`0 ≤ ε ≤ 1/4`. Then there is a self-adjoint effective Hamiltonian `H̃` with
`e^{itH̃} = Ũ` and `‖H - H̃‖ ≤ (6π+12) ε / t`.

The constant `6π+12` is the paper's `K` from the resolvent estimates
`(A19)--(A25)` at `R = 2`; the paper's `κ` in the main text is this `K`.

## Scope of the quantitative statement

The existence half is available in Mathlib (`Unitary.argSelfAdjoint`,
`expUnitary_argSelfAdjoint`), but the *quantitative* norm bound needs the
two-point contour Lipschitz estimate (A14), which Mathlib does not provide
(only the single-point modulus `Unitary.norm_argSelfAdjoint`).  See the
module docstring for the analytic approach. The quantitative statement is
recorded in prose only and is outside the formalized results of this file. -/

end Qatlib.Papers.ThermalGibbs09.MainResults.EffectiveHamiltonian
