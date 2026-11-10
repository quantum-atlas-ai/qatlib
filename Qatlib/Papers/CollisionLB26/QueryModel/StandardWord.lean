/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionLB26.QueryModel.ActualWord
import Qatlib.Concepts.CompressedQuery.CyclicRecord.WordTransport
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace Qatlib.Papers.CollisionLB26.QueryDefs
open Qatlib.Concepts.CompressedQuery.CyclicRecord
variable {W : Type*} [Fintype W] {M N : ℕ} [NeZero N]
local instance : DecidableEq (Fin M) := fun a b => Classical.propDecidable (a=b)

def actualSourceCheckpoint
    (gates : ℕ → EuclideanSpace ℂ (AlgorithmRegisters W M N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (AlgorithmRegisters W M N))
    (initial : EuclideanSpace ℂ (AlgorithmRegisters W M N)) (t : ℕ) :
    EuclideanSpace ℂ (AlgorithmRegisters W M N × (Fin M → ZMod N)) :=
  sourceCheckpoint (W := W) (X := Fin M) (P := ZMod N) (L := ZMod N) (character (N := N)) gates initial t

theorem actual_word_compression
    (gates : ℕ → EuclideanSpace ℂ (AlgorithmRegisters W M N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (AlgorithmRegisters W M N))
    (initial : EuclideanSpace ℂ (AlgorithmRegisters W M N)) (t : ℕ) :
    jointCompressionAction (actualSourceCheckpoint gates initial t)=actualCheckpoint gates initial t :=
  checkpoint_compression (W := W) (X := Fin M) (P := ZMod N) (L := ZMod N)
    (character (N := N)) (character_unitary (N := N)) gates initial t

theorem actual_source_norm
    (gates : ℕ → EuclideanSpace ℂ (AlgorithmRegisters W M N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (AlgorithmRegisters W M N))
    (initial : EuclideanSpace ℂ (AlgorithmRegisters W M N)) (t : ℕ) :
    ‖actualSourceCheckpoint gates initial t‖=‖initial‖ := by
  rw [← (jointCompressionAction (W := W) (X := Fin M) (P := ZMod N) (L := ZMod N)).norm_map,
    actual_word_compression,actual_checkpoint_norm]
end Qatlib.Papers.CollisionLB26.QueryDefs
