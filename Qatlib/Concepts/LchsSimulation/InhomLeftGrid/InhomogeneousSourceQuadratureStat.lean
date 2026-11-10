/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.WindowLchs.TimeDependentLCHSWindowConsumers
import Qatlib.Concepts.LchsSimulation.InhomLeftGrid.InhomogeneousSourceQuadratureDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.LchsSimulation.InhomLeftGrid

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

section InhomogeneousLchsDefinitions

variable {I : Type} [Fintype I] [DecidableEq I]

end InhomogeneousLchsDefinitions

def InhomogeneousSourceQuadrature : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (L H : ℝ → Matrix I I ℂ) (b b' : ℝ → QState I)
    (s t : ℝ) (K N Mt : ℕ) (β lamL lamH bmax : ℝ),
    Continuous L → Continuous H → Continuous b →
    (∀ u, (L u).PosSemidef) → (∀ u, (H u).IsHermitian) → s ≤ t →
    0 < K → 0 < N → 0 < Mt →
    (∀ u, s ≤ u → u ≤ t → HasDerivAt b (b' u) u) →
    (∀ u, s ≤ u → u ≤ t → ‖toEuclidean_fromVec (b' u)‖ ≤ β) →
    (∀ u, s ≤ u → u ≤ t → ‖toEuclidean_fromVec (b u)‖ ≤ bmax) →
    (∀ u, ‖L u‖ ≤ lamL) → (∀ u, ‖H u‖ ≤ lamH) →
    ‖toEuclidean_fromVec (inhSourceSum L H b s t K N Mt -
      inhSourceResponse L H b s t)‖ ≤
      (t - s) * inhStep Mt s t * ((lamL + lamH) * bmax + β) / 2 +
      (t - s) * bmax *
        (2/(Real.pi*(K : ℝ)) + (2*(K : ℝ)/N) *
          (2/Real.pi + ∫ u in s..t, ‖L u‖))

end Qatlib.Concepts.LchsSimulation.InhomLeftGrid
