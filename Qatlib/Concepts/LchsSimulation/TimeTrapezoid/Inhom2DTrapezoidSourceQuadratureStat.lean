/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.KTrapezoid.HomogeneousKTrapezoidQuadratureStat
import Qatlib.Concepts.LchsSimulation.KTrapezoid.InhomogeneousTrapezoidSourceQuadrature
import Qatlib.Concepts.LchsSimulation.TimeTrapezoid.Inhom2DTrapezoidSourceQuadratureDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LchsSimulation.InhomLeftGrid
open Qatlib.Concepts.LchsSimulation.KTrapezoid
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.LchsSimulation.TimeTrapezoid

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

section Inhomogeneous2DTrapezoidDefinitions

variable {I : Type} [Fintype I] [DecidableEq I]

end Inhomogeneous2DTrapezoidDefinitions

def Inhomogeneous2DTrapezoidSourceQuadrature : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (L L' H H' : ℝ → Matrix I I ℂ)
    (b b' b'' : ℝ → QState I) (s t : ℝ) (K M Mt : ℕ)
    (β β₂ lamL lamH lamLd lamHd bmax : ℝ),
    Continuous L → Continuous H → Continuous b →
    (∀ u, (L u).PosSemidef) → (∀ u, (H u).IsHermitian) → s ≤ t →
    0 < K → 0 < M → 0 < Mt →
    (∀ u, s ≤ u → u ≤ t → HasDerivAt L (L' u) u) →
    (∀ u, s ≤ u → u ≤ t → HasDerivAt H (H' u) u) →
    (∀ u, s ≤ u → u ≤ t → ‖L' u‖ ≤ lamLd) →
    (∀ u, s ≤ u → u ≤ t → ‖H' u‖ ≤ lamHd) →
    (∀ u, s ≤ u → u ≤ t → HasDerivAt b (b' u) u) →
    (∀ u, s ≤ u → u ≤ t → HasDerivAt b' (b'' u) u) →
    (∀ u, s ≤ u → u ≤ t → ‖toEuclidean_fromVec (b' u)‖ ≤ β) →
    (∀ u, s ≤ u → u ≤ t → ‖toEuclidean_fromVec (b'' u)‖ ≤ β₂) →
    (∀ u, s ≤ u → u ≤ t → ‖toEuclidean_fromVec (b u)‖ ≤ bmax) →
    (∀ u, ‖L u‖ ≤ lamL) → (∀ u, ‖H u‖ ≤ lamH) →
    ‖toEuclidean_fromVec (inh2dTrapSourceSum L H b s t K M Mt -
      inhSourceResponse L H b s t)‖ ≤
      (t - s) * (inhStep Mt s t)^2 *
        (((lamL + lamH)^2 + (lamLd + lamHd)) * bmax + 2*(lamL + lamH)*β + β₂) / 12 +
      (t - s) * bmax *
        (2/(Real.pi*(K : ℝ)) +
          (2*(K : ℝ))^3/(12*(M : ℝ)^2) *
            (2*(1 + (∫ u in s..t, ‖L u‖) + (∫ u in s..t, ‖L u‖)^2)/Real.pi))

end Qatlib.Concepts.LchsSimulation.TimeTrapezoid
