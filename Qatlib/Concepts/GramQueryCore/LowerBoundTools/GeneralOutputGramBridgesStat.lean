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

open Qatlib.Concepts.GramQueryCore.FilteredCert

namespace Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

def GeneralOutputGramBridges : Prop :=
  (∀ (X H : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H]
      (n q r : ℕ) (hr : 0<r) (input : X → Fin n → Fin (q+1)) (ρ : X → QState H)
      (C : SourceWord (SourceSpace n q H r)),
      (∀ x, Normalized (ρ x)) → sourceWordLegal C →
      let out := fun x => sourceWordMatrix (sourceAlphabetOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)
      sourceRectValue (gramStateMatrix ρ-gramStateMatrix out) (sourceAlphabetDelta input) ≤
        ENNReal.ofReal (2*sourceWordCalls C)) ∧
  (∀ (X H : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H]
      (ρ σ : X → QState H) (ε : ℝ),
      (∀ x, Normalized (ρ x) ∧ Normalized (σ x)) → 0 ≤ ε → ε ≤ 1 →
      (∀ x, (∑ p, star (ρ x p)*σ x p).re ≥ Real.sqrt (1-ε)) →
      sourceUnfiltered (gramStateMatrix ρ-gramStateMatrix σ) ≤
        ENNReal.ofReal (2*Real.sqrt (2*ε))) ∧
  (∀ (X H : Type) [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] [Nonempty H]
      (ρ σ : X → QState H) (δ : ℝ),
      (∀ x, Normalized (ρ x) ∧ Normalized (σ x)) → 0 ≤ δ →
      sourceUnfiltered (gramStateMatrix ρ-gramStateMatrix σ) ≤ ENNReal.ofReal δ →
      ∃ (r : ℕ) (hr : 0<r) (C : SourceWord (SourceSpace 0 0 H r)),
        sourceWordLegal C ∧ sourceWordCalls C=0 ∧ ∀ x,
        ‖toEuclidean_fromVec (sourceWordMatrix (1 : Matrix _ _ ℂ) C *ᵥ
          sourceClean 0 0 r hr false (ρ x)-sourceClean 0 0 r hr true (σ x))‖ ≤ Real.sqrt (2*δ))
end Qatlib.Concepts.GramQueryCore.LowerBoundTools
