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
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.ConversionCore.WitnessCompile
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

def EffectiveSpectralGap : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] (P L V : Matrix H H ℂ)
    (angles : H → ℝ) (Θ : ℝ) (w : QState H),
    IsOrthogonalProjector P → IsOrthogonalProjector L → V ∈ Matrix.unitaryGroup H ℂ →
    (∀ h, -Real.pi < angles h ∧ angles h ≤ Real.pi) →
    ReflectionAbout P * ReflectionAbout L=
      V * Matrix.diagonal (fun h => Complex.exp (Complex.I*angles h)) * Vᴴ →
    0 ≤ Θ → L *ᵥ w=0 →
    ‖toEuclidean_fromVec (sourcePhaseProjector V angles Θ *ᵥ (P *ᵥ w))‖ ≤
      Θ/2*‖toEuclidean_fromVec w‖
end Qatlib.Concepts.ConversionCore.WitnessCompile
