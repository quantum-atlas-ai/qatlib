/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.KTrapezoid.HomogeneousKTrapezoidQuadratureStat
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false


open Qatlib.Concepts.LchsSimulation.WindowLchs
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.LchsSimulation.KTrapezoid

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

def HomogeneousKTrapezoidSchedule : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (L H : ℝ → Matrix I I ℂ)
    (s t ε lamL : ℝ),
    Continuous L → Continuous H →
    (∀ u, (L u).PosSemidef) → (∀ u, (H u).IsHermitian) → s ≤ t →
    0 < ε → (∀ u, ‖L u‖ ≤ lamL) →
    let K := timeDependentLchsWindowCutoff (ε/2)
    let M := max 1 (Nat.ceil (Real.sqrt
      ((2*(K : ℝ))^3*(2*(1 + lamL*(t-s) + (lamL*(t-s))^2)/Real.pi)/(6*ε))))
    0 < M ∧
    ‖kTrapSum L H s t K M -
      orderedEvolution (fun u => L u + Complex.I • H u) s t‖ ≤ ε

end Qatlib.Concepts.LchsSimulation.KTrapezoid
