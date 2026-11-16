/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.OneShotLDPC23.MainResults.Sequential.MismatchDecomposition

@[expose] public section


/-!
# The missing parallel-step condition in the legacy mismatch contract

The original Lemma 4.18 formalization leaves the proposed next mismatch free.
The zero starting mismatch and empty sequential decomposition satisfy all
recorded hypotheses, while choosing a nonzero next mismatch violates the bound.
The actual parallel decoder's transition relation is needed to recover the paper.
-/

set_option autoImplicit false

namespace Qatlib.Papers.OneShotLDPC23.MainResults

open Qatlib.Papers.OneShotLDPC23.MainResults.Model
open Qatlib.Papers.OneShotLDPC23.MainResults.Sequential

/-- An empty sequential decomposition does not control an arbitrary proposed
next parallel mismatch, as the one-bit instance demonstrates. -/
theorem parallel_free :
    ∃ (Zk Zk1 ZT : BitVec (Fin 1)) (F : List (BitVec (Fin 1))) (ε : ℝ),
      0 < ε ∧ ε < 1 / 6 ∧ DeltaDecomposes ε Zk F ∧ ZT = Zk + F.sum ∧
      ¬ ((1 / 16) * (1 - 6 * ε) * (weightR Zk - weightR ZT) ≤
        weightR Zk - weightR Zk1) := by
  refine ⟨0, fun _ => 1, 0, [], 1 / 12, ?_⟩
  norm_num [DeltaDecomposes, StepReduces, weightR,
    Qatlib.Concepts.CodingDecoding.CssTesters.bitWeight]

end Qatlib.Papers.OneShotLDPC23.MainResults
