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

open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.ConversionCore.WitnessCompile
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

def AdaptiveInstrumentPurification : Prop :=
  ∀ (X H : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] [Nonempty H]
    (n q r : ℕ) (hr : 0<r) (input : X → Fin n → Fin (q+1))
    (T : SourceAdaptive (SourceSpace n q H r)), sourceAdaptiveLegal T →
    let leaves := max 1 (sourceAdaptiveLeaves T)
    ∃ (R : ℕ) (hR : 0<R) (C : SourceWord (SourceSpace n q H R)),
      leaves*r ≤ R ∧ sourceWordLegal C ∧ sourceWordCalls C ≤ 2*sourceAdaptiveCalls T ∧
      let F := sourceTreeFrame (H := H) n q r leaves R
      Fᴴ * F=1 ∧ ∀ (x : X) (ψ : QState (SourceSpace n q H r)),
      sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        (F *ᵥ TensorState (Ket (⟨0, by dsimp [leaves]; omega⟩ : Fin leaves)) ψ)=
      F *ᵥ sourceAdaptivePure (sourceAlphabetOracle input x) T ψ ∧
      (Normalized ψ →
        ((sourceAdaptiveBranches (sourceAlphabetOracle input x) T ψ).map
          (fun φ => ‖toEuclidean_fromVec φ‖^2)).sum=1) ∧
      (∀ p t, sourceAdaptiveDensity (sourceAlphabetOracle input x) T ψ p t=
        ∑ i : Fin leaves, sourceAdaptivePure (sourceAlphabetOracle input x) T ψ (i,p)*
          star (sourceAdaptivePure (sourceAlphabetOracle input x) T ψ (i,t)))
end Qatlib.Concepts.ConversionCore.WitnessCompile
