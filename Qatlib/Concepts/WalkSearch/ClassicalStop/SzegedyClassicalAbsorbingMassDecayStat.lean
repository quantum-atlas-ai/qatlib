/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.ProjectorCS
set_option warningAsError false

open Qatlib.Concepts.WalkSearch.ProjectorCS
open Matrix

namespace Qatlib.Concepts.WalkSearch.ClassicalStop

def SzegedyClassicalAbsorbingMassDecay : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I] (P : I→I→ℝ) (S : Finset I)
      (δ ε : ℝ) (K : ℕ),
    0 < δ → δ ≤ 1 → SymmetricChainGap P δ → 0 < ε → ε ≤ markedFraction S →
    ∀ law : ℕ → I → ℝ,
      law 0 = (fun _ => (1:ℝ)/(Fintype.card I : ℝ)) →
      (∀ t j, law (t+1) j =
        ∑ i, law t i * (if i ∈ S then (if j = i then 1 else 0) else P i j)) →
      (∑ i : {x : I // x ∉ S}, law K i) ≤ (1 - δ*ε/2)^(K:ℕ)

end Qatlib.Concepts.WalkSearch.ClassicalStop
