/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.InhomLeftGrid.InhomogeneousSourceQuadratureStat
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LchsSimulation.WindowLchs

namespace Qatlib.Concepts.LchsSimulation.InhomLeftGrid

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

def InhomogeneousSourceSchedule : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (L H : ℝ → Matrix I I ℂ) (b b' : ℝ → QState I)
    (s t ε Λ β lamL lamH bmax : ℝ),
    Continuous L → Continuous H → Continuous b →
    (∀ u, (L u).PosSemidef) → (∀ u, (H u).IsHermitian) → s < t →
    0 < ε → 0 < bmax →
    (∀ u, s ≤ u → u ≤ t → HasDerivAt b (b' u) u) →
    (∀ u, s ≤ u → u ≤ t → ‖toEuclidean_fromVec (b' u)‖ ≤ β) →
    (∀ u, s ≤ u → u ≤ t → ‖toEuclidean_fromVec (b u)‖ ≤ bmax) →
    (∀ u, ‖L u‖ ≤ lamL) → (∀ u, ‖H u‖ ≤ lamH) →
    2/Real.pi + (∫ u in s..t, ‖L u‖) ≤ Λ →
    let K := timeDependentLchsWindowCutoff (min (ε/2) (ε/(4*(t-s)*bmax)))
    let N := timeDependentLchsWindowNodes (min (ε/2) (ε/(4*(t-s)*bmax))) Λ
    let Mt := max 1 (Nat.ceil (2*((lamL + lamH)*bmax + β)*(t-s)^2/ε))
    0 < Mt ∧
    2*(K : ℝ)/(N : ℝ) ≤ 1/2 ∧
    (2/(Real.pi*(K : ℝ)) + (2*(K : ℝ)/N) *
      (2/Real.pi + ∫ u in s..t, ‖L u‖)) ≤ min (ε/2) (ε/(4*(t-s)*bmax)) ∧
    ‖toEuclidean_fromVec (inhSourceSum L H b s t K N Mt -
      inhSourceResponse L H b s t)‖ ≤ ε/2 ∧
    (∑ l : Fin Mt, inhStep Mt s t * ‖toEuclidean_fromVec (b (inhNode Mt s t l))‖) ≤
      (∫ u in s..t, ‖toEuclidean_fromVec (b u)‖) + β*(t-s)^2/(2*(Mt : ℝ))

end Qatlib.Concepts.LchsSimulation.InhomLeftGrid
