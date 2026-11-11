/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.InhomLeftGrid.InhomogeneousSourceQuadratureStat

/-!
# Trapezoidal source quadrature definitions

`inhTrapNode` and `inhTrapWeight` define a source-time grid with both endpoints and half
endpoint weights. The sum `inhTrapSourceSum` combines this time quadrature with the static LCHS
parameter quadrature. See [AnLiuLin2023] for the mathematical setting.

## Main statements

* `inhTrapWeight`: The source-time trapezoidal weight, equal to half the step at the endpoint
  indices and the full step at interior indices.
* `inhTrapSourceSum`: The trapezoidal source-time sum obtained by applying the static LCHS
  propagator approximation to each sampled source vector.

## References

* [An, Liu, and Lin, 2023][AnLiuLin2023]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

variable {I : Type} [Fintype I] [DecidableEq I]

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LchsSimulation.InhomLeftGrid
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.LchsSimulation.KTrapezoid

/-- The source-time grid node `s + l * inhStep Mt s t`, including the endpoint index `Mt`. -/
noncomputable def inhTrapNode (Mt : ℕ) (s t : ℝ) (l : Fin (Mt+1)) : ℝ :=
  s + (l : ℝ) * inhStep Mt s t

/-- The source-time trapezoidal weight, equal to half the step at the endpoint indices and the
full step at interior indices. -/
noncomputable def inhTrapWeight (Mt : ℕ) (s t : ℝ) (l : Fin (Mt+1)) : ℝ :=
  if (l : ℕ) = 0 ∨ (l : ℕ) = Mt then inhStep Mt s t / 2 else inhStep Mt s t

/-- The ordered unitary-family evolution from a trapezoidal source-time node to `t` at a static
LCHS parameter node. -/
noncomputable def inhTrapSourceKUnitary (L H : ℝ → Matrix I I ℂ) (s t : ℝ) (K N Mt : ℕ)
    (j : Fin N) (l : Fin (Mt+1)) : Matrix I I ℂ :=
  orderedEvolution (fun u => Complex.I • (H u + staticLchsGrid K N j • L u))
    (inhTrapNode Mt s t l) t

/-- The trapezoidal source-time sum obtained by applying the static LCHS propagator
approximation to each sampled source vector. -/
noncomputable def inhTrapSourceSum (L H : ℝ → Matrix I I ℂ) (b : ℝ → QState I) (s t : ℝ)
    (K N Mt : ℕ) : QState I :=
  ∑ l : Fin (Mt+1), (inhTrapWeight Mt s t l : ℂ) •
    ((∑ j : Fin N, staticLchsCoeff K N j • inhTrapSourceKUnitary L H s t K N Mt j l) *ᵥ
      b (inhTrapNode Mt s t l))
end Qatlib.Concepts.LchsSimulation.KTrapezoid
