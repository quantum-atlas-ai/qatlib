/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.KTrapezoid.HomogeneousKTrapezoidQuadratureStat
import Qatlib.Concepts.LchsSimulation.KTrapezoid.InhomogeneousTrapezoidSourceQuadrature

/-!
# Two-dimensional trapezoidal LCHS source sums

`inh2dTrapSourceKUnitary` propagates from a trapezoidal source-time node to the final time at a
trapezoidal Hamiltonian-parameter node. `inh2dTrapSourceSum` combines these propagators with
time weights, Cauchy weights, and sampled source vectors to define the joint quadrature
approximation.

The mathematical background is described in [AnLiuLin2023].

## Main statements

* `inh2dTrapSourceKUnitary`: defines the ordered propagator at a pair of nodes.
* `inh2dTrapSourceSum`: defines the nested weighted source sum.

## References

* [An et al., 2023][AnLiuLin2023]
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

open Qatlib.Concepts.LchsSimulation.KTrapezoid
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.LchsSimulation.TimeTrapezoid

/-- The ordered Hamiltonian propagator from a trapezoidal source-time node to `t`, evaluated at
a trapezoidal parameter node. -/
noncomputable def inh2dTrapSourceKUnitary (L H : ℝ → Matrix I I ℂ) (s t : ℝ)
    (K M Mt : ℕ) (j : Fin (M+1)) (l : Fin (Mt+1)) : Matrix I I ℂ :=
  orderedEvolution (fun u => Complex.I • (H u + (kTrapNode K M j) • L u))
    (inhTrapNode Mt s t l) t

/-- The nested trapezoidal sum over source times and Hamiltonian parameters, applying each
weighted propagator to the source at its time node. -/
noncomputable def inh2dTrapSourceSum (L H : ℝ → Matrix I I ℂ) (b : ℝ → QState I)
    (s t : ℝ) (K M Mt : ℕ) : QState I :=
  ∑ l : Fin (Mt+1), (inhTrapWeight Mt s t l : ℂ) •
    ((∑ j : Fin (M+1), kTrapCoeff K M j •
      inh2dTrapSourceKUnitary L H s t K M Mt j l) *ᵥ
      b (inhTrapNode Mt s t l))
end Qatlib.Concepts.LchsSimulation.TimeTrapezoid
