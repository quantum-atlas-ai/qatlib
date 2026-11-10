/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.InhomLeftGrid.InhomogeneousSourceQuadratureStat
import Qatlib.Concepts.LchsSimulation.KTrapezoid.InhomogeneousTrapezoidSourceDefs
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
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.LchsSimulation.KTrapezoid

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

section InhomogeneousTrapezoidDefinitions

variable {I : Type} [Fintype I] [DecidableEq I]

end InhomogeneousTrapezoidDefinitions

def InhomogeneousTrapezoidSourceQuadrature : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (L L' H H' : ℝ → Matrix I I ℂ)
    (b b' b'' : ℝ → QState I) (s t : ℝ) (K N Mt : ℕ)
    (β β₂ lamL lamH lamLd lamHd bmax : ℝ),
    Continuous L → Continuous H → Continuous b →
    (∀ u, (L u).PosSemidef) → (∀ u, (H u).IsHermitian) → s ≤ t →
    0 < K → 0 < N → 0 < Mt →
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
    ‖toEuclidean_fromVec (inhTrapSourceSum L H b s t K N Mt -
      inhSourceResponse L H b s t)‖ ≤
      (t - s) * (inhStep Mt s t)^2 *
        (((lamL + lamH)^2 + (lamLd + lamHd)) * bmax + 2*(lamL + lamH)*β + β₂) / 12 +
      (t - s) * bmax *
        (2/(Real.pi*(K : ℝ)) + (2*(K : ℝ)/N) *
          (2/Real.pi + ∫ u in s..t, ‖L u‖))

end Qatlib.Concepts.LchsSimulation.KTrapezoid
