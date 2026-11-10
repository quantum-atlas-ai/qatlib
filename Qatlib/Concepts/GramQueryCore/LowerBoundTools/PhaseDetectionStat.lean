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
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

def PhaseDetection : Prop :=
  ∃ c : ℕ, 0<c ∧ ∀ (H : Type) [Fintype H] [DecidableEq H]
    (Θ δ : ℝ), 0<Θ → 0<δ →
    ∃ (b : ℕ) (C : SourceWord ((Bool × H) × Fin (2^b))),
      sourceWordLegal C ∧
      sourceWordCalls C ≤ c*max 1 (Nat.ceil (1/Θ))*
        (Nat.ceil (Real.log (2/min 1 δ))+1) ∧
      b ≤ c*(Nat.clog 2 (max 1 (Nat.ceil (1/Θ))+1)+1)*
        (Nat.ceil (Real.log (2/min 1 δ))+1) ∧
      ∀ (U V : Matrix H H ℂ) (angles : H → ℝ),
      U ∈ Matrix.unitaryGroup H ℂ → V ∈ Matrix.unitaryGroup H ℂ →
      (∀ h, -Real.pi < angles h ∧ angles h ≤ Real.pi) →
      U=V * Matrix.diagonal (fun h => Complex.exp (Complex.I*angles h)) * Vᴴ →
      ∀ ψ : QState H,
      let embed := fun φ : QState H => TensorState (TensorState (Ket false) φ)
        (Ket (0 : Fin (2^b)))
      let A := sourceWordMatrix (sourceControlledU (2^b) U) C
      (U *ᵥ ψ=ψ → A *ᵥ embed ψ=embed ψ) ∧
      (sourcePhaseProjector V angles Θ *ᵥ ψ=0 →
        ‖toEuclidean_fromVec (A *ᵥ embed ψ+embed ψ)‖ ≤ δ*‖toEuclidean_fromVec ψ‖)
end Qatlib.Concepts.GramQueryCore.LowerBoundTools
