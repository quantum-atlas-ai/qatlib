/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.WindowLchs.TimeDependentLCHSConsumers
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.LchsSimulation.InteractHybrid

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

def HybridObservableRepresentation : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (L H : ℝ → Matrix I I ℂ) (O : Matrix I I ℂ)
    (u₀ : QState I) (t : ℝ),
    Continuous L → Continuous H → (∀ u, (L u).PosSemidef) → (∀ u, (H u).IsHermitian) → 0 ≤ t →
    let A := fun u => L u + Complex.I • H u
    let U := orderedEvolution A 0 t
    let V := fun k : ℝ => orderedEvolution (fun u => Complex.I • (H u + k • L u)) 0 t
    Inner (U *ᵥ u₀) (O *ᵥ (U *ᵥ u₀)) =
      ∫ k : ℝ, ∫ k' : ℝ,
        ((1/(Real.pi*(1+k^2)) * 1/(Real.pi*(1+k'^2)) : ℝ) : ℂ) •
          Inner (V k *ᵥ u₀) (O *ᵥ (V k' *ᵥ u₀))

end Qatlib.Concepts.LchsSimulation.InteractHybrid
