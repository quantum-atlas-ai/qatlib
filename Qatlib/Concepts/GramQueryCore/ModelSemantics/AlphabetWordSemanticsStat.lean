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

open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.GramQueryCore.ModelSemantics
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

def AlphabetWordSemantics : Prop :=
  ∀ (X S : Type) [Fintype S] [DecidableEq S] (n q : ℕ)
    (input : X → Fin n → Fin (q+1)) (x : X),
    sourceAlphabetOracle (W := S) input x ∈ Matrix.unitaryGroup _ ℂ ∧
    (∀ C : SourceWord ((Fin (n+1) × Fin (q+1)) × S), sourceWordLegal C →
      sourceWordMatrix (sourceAlphabetOracle input x) C ∈ Matrix.unitaryGroup _ ℂ) ∧
    (∀ (H : Type) [Fintype H] [DecidableEq H] (r : ℕ) (hr : 0<r)
      (tag : Bool) (ψ : QState H), Normalized ψ → Normalized (sourceClean n q r hr tag ψ))
end Qatlib.Concepts.GramQueryCore.ModelSemantics
