/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.AdaptiveModels
import Qatlib.Concepts.BitWordCompiler.WordComposition.FiniteModels
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.GramQueryCore.ModelSemantics
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

def VolterraAndOracleLogSemantics : Prop :=
  (∀ (H : Type) [Fintype H] [DecidableEq H] (K : ℝ → Matrix H H ℂ) (T : ℝ),
      0 ≤ T → (∀ i j, IntervalIntegrable (fun t => K t i j) MeasureTheory.volume 0 T) →
      (∀ t ∈ Set.Icc 0 T, (K t).IsHermitian) →
      (∃ U, sourceVolterra K T U ∧
        (∀ V, sourceVolterra K T V → ∀ t ∈ Set.Icc 0 T, U t=V t) ∧
        ∀ t ∈ Set.Icc 0 T, U t ∈ Matrix.unitaryGroup H ℂ) ∧
      sourceVolterraMatrix K T ∈ Matrix.unitaryGroup H ℂ) ∧
  (∀ (H : Type) [Fintype H] [DecidableEq H] (U : Matrix H H ℂ),
      U ∈ Matrix.unitaryGroup H ℂ →
      (sourceLog U).IsHermitian ∧ ‖sourceLog U‖ ≤ Real.pi ∧
        sourceVolterraMatrix (fun _ => sourceLog U) 1=U) ∧
  (∀ (X S : Type) [Fintype S] [DecidableEq S] (n q : ℕ)
      (input : X → Fin n → Fin (q+1)) (x : X),
      (sourceLogOracle (W := S) input x).IsHermitian ∧
      ‖sourceLogOracle (W := S) input x‖ ≤ Real.pi ∧
      sourceVolterraMatrix (fun _ => sourceLogOracle (W := S) input x) 1=
        sourceAlphabetOracle (W := S) input x)
end Qatlib.Concepts.GramQueryCore.ModelSemantics
