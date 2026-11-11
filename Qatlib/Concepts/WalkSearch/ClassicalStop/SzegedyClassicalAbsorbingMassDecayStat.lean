/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.ProjectorCS

/-!
# Classical absorbing mass decay statement

`SzegedyClassicalAbsorbingMassDecay` specifies geometric decay of the mass remaining outside a
marked set. It quantifies over real-valued laws initialized uniformly and satisfying the marked
absorbing recurrence, with a symmetric-chain gap and a lower bound on the marked fraction. See
[Szegedy2004] for the mathematical background.

## Main statements

* `SzegedyClassicalAbsorbingMassDecay`: the absorbing-law decay proposition.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false

open Qatlib.Concepts.WalkSearch.ProjectorCS
open Matrix

namespace Qatlib.Concepts.WalkSearch.ClassicalStop

/-- The proposition that a uniformly initialized law following the marked absorbing recurrence
has unmarked mass at most `(1 - δ * ε / 2) ^ K`, under the stated gap and marked-fraction
conditions. -/
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
