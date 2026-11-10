/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.LinearCombination
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib
open Qatlib

open Matrix

namespace Qatlib.Papers.HamLCUSim12.Multiproduct

def LCUContractionSubgoal : Prop :=
  ∀ (J I : Type) [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (U : J → Matrix I I ℂ) (w : J → ℝ), (∀ j, 0 ≤ w j) → (∑ j, w j = 1) →
    ∀ (P : Matrix J J ℂ) (j0 : J), IsPrepare P w j0 → ∀ (ψ : QState I),
      (fun i' => (LCUWorkspace U P *ᵥ TensorState (Ket j0) ψ) (j0, i'))
        = (∑ j, w j • U j) *ᵥ ψ

end Qatlib.Papers.HamLCUSim12.Multiproduct
