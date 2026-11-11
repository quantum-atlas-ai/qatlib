/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CodingDecoding.CssTesters.CssPauli

/-!
# Greedy syndrome decoder

This module defines `chooseReducingFlip` and the fuel bounded decoder `greedyDecode` for binary
syndrome matrices. `GreedyTrace` records the correction, residual syndrome, flip count, and
number of candidate tests. The model provides finite execution data for decoding analyses in the
setting of [BhartiHaugTanggara2026].

## Main statements

* `chooseReducingFlip`: search for the first move that strictly reduces syndrome weight.
* `greedyDecode`: iterate successful moves with a fuel bound.

## References

* [Bharti et al., 2026][BhartiHaugTanggara2026]
-/

open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib

set_option autoImplicit false

namespace Qatlib.Concepts.CssGreedyDecode.SyndromeGreedy

open Matrix

/-- Search the candidate list for the first flip that strictly reduces syndrome weight,
returning that flip if found and the number of tested candidates. -/
def chooseReducingFlip {ι κ : Type*} [Fintype ι] [Fintype κ]
    (H : Matrix κ ι (ZMod 2)) (s : κ → ZMod 2) :
    List (ι → ZMod 2) → Option (ι → ZMod 2) × ℕ
  | [] => (none, 0)
  | f :: fs =>
      if bitWeight (s + H *ᵥ f) < bitWeight s then (some f, 1)
      else let r := chooseReducingFlip H s fs; (r.1, r.2 + 1)

/-- The correction, remaining syndrome, successful flip count, and candidate test count produced
by greedy decoding. -/
structure GreedyTrace (ι κ : Type*) where
  correction : ι → ZMod 2
  syndrome : κ → ZMod 2
  flips : ℕ
  candidateChecks : ℕ

/-- Apply reducing flips until the fuel is exhausted or no candidate reduces the syndrome
weight, accumulating the correction and execution counts. -/
def greedyDecode {ι κ : Type*} [Fintype ι] [Fintype κ]
    (H : Matrix κ ι (ZMod 2)) (moves : List (ι → ZMod 2)) :
    ℕ → (κ → ZMod 2) → GreedyTrace ι κ
  | 0, s => ⟨0, s, 0, 0⟩
  | fuel + 1, s =>
      let trial := chooseReducingFlip H s moves
      match trial.1 with
      | none => ⟨0, s, 0, trial.2⟩
      | some f =>
          let r := greedyDecode H moves fuel (s + H *ᵥ f)
          ⟨f + r.correction, r.syndrome, r.flips + 1, trial.2 + r.candidateChecks⟩

end Qatlib.Concepts.CssGreedyDecode.SyndromeGreedy
