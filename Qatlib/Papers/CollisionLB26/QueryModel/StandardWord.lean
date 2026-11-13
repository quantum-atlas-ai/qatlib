/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionLB26.QueryModel.ActualWord
import Qatlib.Concepts.CompressedQuery.CyclicRecord.WordTransport

/-!
# Compression of cyclic source checkpoints

This module relates the explicit input-table source checkpoint to the compressed-record
checkpoint for cyclic query words. The exact intertwining identity and norm preservation connect
the two state descriptions used in the query analysis of [MagniezZur2026].

## Main statements

* `actualSourceCheckpoint`: the source state with its full input table register.
* `actual_word_compression`: equality after joint compression.
* `actual_source_norm`: preservation of the initial state norm.

## References

* [Magniez and Zur, 2026][MagniezZur2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace Qatlib.Papers.CollisionLB26.QueryDefs
open Qatlib.Concepts.CompressedQuery.CyclicRecord
variable {W : Type*} [Fintype W] {M N : ℕ} [NeZero N]
local instance : DecidableEq (Fin M) := fun a b => Classical.propDecidable (a=b)

/-- The uncompressed source checkpoint after `t` queries, with an explicit cyclic-valued input
table register. -/
def actualSourceCheckpoint
    (gates : ℕ → EuclideanSpace ℂ (AlgorithmRegisters W M N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (AlgorithmRegisters W M N))
    (initial : EuclideanSpace ℂ (AlgorithmRegisters W M N)) (t : ℕ) :
    EuclideanSpace ℂ (AlgorithmRegisters W M N × (Fin M → ZMod N)) :=
  sourceCheckpoint (W := W) (X := Fin M) (P := ZMod N) (L := ZMod N) (character (N := N)) gates initial t

/-- Joint compression maps the uncompressed source checkpoint exactly to the compressed-record
checkpoint; see [MagniezZur2026]. -/
theorem actual_word_compression
    (gates : ℕ → EuclideanSpace ℂ (AlgorithmRegisters W M N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (AlgorithmRegisters W M N))
    (initial : EuclideanSpace ℂ (AlgorithmRegisters W M N)) (t : ℕ) :
    jointCompressionAction (actualSourceCheckpoint gates initial t)=actualCheckpoint gates initial t :=
  checkpoint_compression (W := W) (X := Fin M) (P := ZMod N) (L := ZMod N)
    (character (N := N)) (character_unitary (N := N)) gates initial t

/-- The uncompressed source checkpoint has the same norm as the initial algorithm state; see
[MagniezZur2026]. -/
theorem actual_source_norm
    (gates : ℕ → EuclideanSpace ℂ (AlgorithmRegisters W M N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (AlgorithmRegisters W M N))
    (initial : EuclideanSpace ℂ (AlgorithmRegisters W M N)) (t : ℕ) :
    ‖actualSourceCheckpoint gates initial t‖=‖initial‖ := by
  rw [← (jointCompressionAction (W := W) (X := Fin M) (P := ZMod N) (L := ZMod N)).norm_map,
    actual_word_compression,actual_checkpoint_norm]
end Qatlib.Papers.CollisionLB26.QueryDefs
