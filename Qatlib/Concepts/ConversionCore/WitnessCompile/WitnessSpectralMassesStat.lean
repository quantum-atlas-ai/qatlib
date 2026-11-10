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
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.ConversionCore.WitnessCompile
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

def WitnessSpectralMasses : Prop :=
  ∀ (X H : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H]
    (n q m : ℕ) (input : X → Fin n → Fin (q+1)) (ρ σ : X → QState H)
    (u v : X → Fin n → QState (Fin m)) (W ε : ℝ),
    (∀ x, Normalized (ρ x) ∧ Normalized (σ x)) → 0<q → 0<W → 0<ε →
    (∀ y x, (gramStateMatrix ρ-gramStateMatrix σ) y x=
      ∑ j, sourceAlphabetDelta input j y x*∑ k, star (u y j k)*v x j k) →
    (∀ x, (∑ j, ‖toEuclidean_fromVec (u x j)‖^2) ≤ W ∧
      (∑ j, ‖toEuclidean_fromVec (v x j)‖^2) ≤ W) →
    ∀ (x : X) (V : Matrix (SourceGeometry n q m H) (SourceGeometry n q m H) ℂ)
      (angles : SourceGeometry n q m H → ℝ),
    V ∈ Matrix.unitaryGroup _ ℂ → (∀ h, -Real.pi < angles h ∧ angles h ≤ Real.pi) →
    ReflectionAbout (sourceKeep input x) * ReflectionAbout (sourceComplement input ρ σ u W ε)=
      V * Matrix.diagonal (fun h => Complex.exp (Complex.I*angles h)) * Vᴴ →
    ‖toEuclidean_fromVec (sourcePhaseProjector V angles 0 *ᵥ sourcePlus (ρ x) (σ x))‖^2 ≥
      1-ε^2 ∧ ∀ Θ : ℝ, 0 ≤ Θ →
      ‖toEuclidean_fromVec (sourcePhaseProjector V angles Θ *ᵥ sourceMinus (ρ x) (σ x))‖^2 ≤
        Θ^2/4*(W^2/ε^2+1)
end Qatlib.Concepts.ConversionCore.WitnessCompile
