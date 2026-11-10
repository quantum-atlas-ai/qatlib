/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CodingDecoding.CssTesters.CssPauli
open Qatlib.Concepts.CodingDecoding.CssTesters
open Qatlib

set_option autoImplicit false

namespace Qatlib.Concepts.CssGreedyDecode.SyndromeGreedy

open Matrix

def chooseReducingFlip {ι κ : Type*} [Fintype ι] [Fintype κ]
    (H : Matrix κ ι (ZMod 2)) (s : κ → ZMod 2) :
    List (ι → ZMod 2) → Option (ι → ZMod 2) × ℕ
  | [] => (none, 0)
  | f :: fs =>
      if bitWeight (s + H *ᵥ f) < bitWeight s then (some f, 1)
      else let r := chooseReducingFlip H s fs; (r.1, r.2 + 1)

structure GreedyTrace (ι κ : Type*) where
  correction : ι → ZMod 2
  syndrome : κ → ZMod 2
  flips : ℕ
  candidateChecks : ℕ

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
