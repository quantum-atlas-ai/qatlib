/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.WindowLchs.TimeDependentLCHSWindow
import Qatlib.Concepts.LchsSimulation.KTrapezoid.HomogeneousKTrapezoidQuadratureDefs

/-!
# Homogeneous trapezoidal LCHS specification

`HomogeneousKTrapezoidQuadrature` specifies the operator-norm error of `kTrapSum` for forward
dissipative evolution. The bound separates the Cauchy tail from a second-order parameter-grid
error depending on the integral of `‖L u‖`. See [AnLiuLin2023] for the mathematical setting.

## Main statements

* `HomogeneousKTrapezoidQuadrature`: The homogeneous trapezoidal LCHS error specification with
  tail `2 / (Real.pi * K)` and the stated second-order grid term involving the integral of `‖L
  u‖`.

## References

* [An, Liu, and Lin, 2023][AnLiuLin2023]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.LchsSimulation.KTrapezoid

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

section HomogeneousKTrapezoidDefinitions

variable {I : Type} [Fintype I] [DecidableEq I]

end HomogeneousKTrapezoidDefinitions

/-- The homogeneous trapezoidal LCHS error specification with tail `2 / (Real.pi * K)` and the
stated second-order grid term involving the integral of `‖L u‖`. -/
def HomogeneousKTrapezoidQuadrature : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (L H : ℝ → Matrix I I ℂ)
    (s t : ℝ) (K M : ℕ),
    Continuous L → Continuous H →
    (∀ u, (L u).PosSemidef) → (∀ u, (H u).IsHermitian) → s ≤ t →
    0 < K → 0 < M →
    ‖kTrapSum L H s t K M -
      orderedEvolution (fun u => L u + Complex.I • H u) s t‖ ≤
      2/(Real.pi*(K : ℝ)) +
        (2*(K : ℝ))^3/(12*(M : ℝ)^2) *
          (2*(1 + (∫ u in s..t, ‖L u‖) + (∫ u in s..t, ‖L u‖)^2)/Real.pi)

end Qatlib.Concepts.LchsSimulation.KTrapezoid
