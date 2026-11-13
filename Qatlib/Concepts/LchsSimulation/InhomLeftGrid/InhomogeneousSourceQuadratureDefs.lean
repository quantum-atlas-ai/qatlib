/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.WindowLchs.TimeDependentLCHSWindowConsumers

/-!
# Left-grid source quadrature definitions

`inhStep` and `inhNode` define a uniform left grid, while `inhSourceKUnitary` propagates each
sampled source value to the final time. The finite approximation `inhSourceSum` is paired with
the exact variation-of-constants integral `inhSourceResponse`. See [AnLiuLin2023] for the
mathematical setting.

## Main statements

* `inhSourceSum`: The left-grid source approximation obtained by applying the static LCHS sum to
  each sampled source value and multiplying by the time step.
* `inhSourceResponse`: The variation-of-constants source integral for the generator `L u +
  Complex.I • H u` over the interval from `s` to `t`.

## References

* [An, Liu, and Lin, 2023][AnLiuLin2023]
-/

set_option backward.isDefEq.respectTransparency false
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

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.LchsSimulation.InhomLeftGrid

/-- The uniform time-step size `(t - s) / Mt`. -/
noncomputable def inhStep (Mt : ℕ) (s t : ℝ) : ℝ := (t - s) / Mt

/-- The left-grid node `s + l * inhStep Mt s t` indexed by `Fin Mt`. -/
noncomputable def inhNode (Mt : ℕ) (s t : ℝ) (l : Fin Mt) : ℝ :=
  s + (l : ℝ) * inhStep Mt s t

/-- The ordered evolution from the source node to `t` for the generator `Complex.I • (H u +
staticLchsGrid K N j • L u)`. -/
noncomputable def inhSourceKUnitary (L H : ℝ → Matrix I I ℂ) (s t : ℝ) (K N Mt : ℕ)
    (j : Fin N) (l : Fin Mt) : Matrix I I ℂ :=
  orderedEvolution (fun u => Complex.I • (H u + staticLchsGrid K N j • L u))
    (inhNode Mt s t l) t

/-- The left-grid source approximation obtained by applying the static LCHS sum to each sampled
source value and multiplying by the time step. -/
noncomputable def inhSourceSum (L H : ℝ → Matrix I I ℂ) (b : ℝ → QState I) (s t : ℝ)
    (K N Mt : ℕ) : QState I :=
  ∑ l : Fin Mt, (inhStep Mt s t : ℂ) •
    ((∑ j : Fin N, staticLchsCoeff K N j • inhSourceKUnitary L H s t K N Mt j l) *ᵥ
      b (inhNode Mt s t l))

/-- The variation-of-constants source integral for the generator `L u + Complex.I • H u` over
the interval from `s` to `t`. -/
noncomputable def inhSourceResponse (L H : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (s t : ℝ) : QState I :=
  ∫ u in s..t, orderedEvolution (fun y => L y + Complex.I • H y) u t *ᵥ b u
end Qatlib.Concepts.LchsSimulation.InhomLeftGrid
