/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionLB26.QueryModel.CyclicBounds
import Qatlib.Concepts.CompressedQuery.CyclicRecord.AlgorithmWord

/-!
# Compressed checkpoints for cyclic query words

This module specializes compressed query-word checkpoints to finite addresses and cyclic output
labels for the query model associated with [MagniezZur2026]. It records the algorithm register
size, preservation of the initial norm, and the database support bound after a finite number of
queries.

## Main statements

* `actual_algorithm_dimension`: the workspace-address-phase register cardinality.
* `actual_checkpoint_norm`: norm preservation at each checkpoint.
* `actual_checkpoint_supported`: at most `t` recorded entries after `t` queries.

## References

* [Magniez and Zur, 2026][MagniezZur2026]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CollisionLB26.QueryDefs
open Qatlib.Concepts.CompressedQuery.CyclicRecord
variable {W : Type*} [Fintype W] {M N : ℕ} [NeZero N]
local instance : DecidableEq (Fin M) := fun a b => Classical.propDecidable (a=b)

/-- The algorithm register basis consisting of workspace, query address, and cyclic phase
registers. -/
abbrev AlgorithmRegisters (W : Type*) (M N : ℕ) := Registers W (Fin M) (ZMod N)

/-- The compressed-record checkpoint after `t` queries, specialized to addresses `Fin M` and
cyclic labels and phases `ZMod N`. -/
def actualCheckpoint
    (gates : ℕ → EuclideanSpace ℂ (AlgorithmRegisters W M N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (AlgorithmRegisters W M N))
    (initial : EuclideanSpace ℂ (AlgorithmRegisters W M N)) (t : ℕ) :
    EuclideanSpace ℂ (DatabaseBasis W (Fin M) (ZMod N) (ZMod N)) :=
  checkpoint (W := W) (X := Fin M) (P := ZMod N) (L := ZMod N) (character (N := N)) (character_unitary (N := N)) gates initial t

/-- The algorithm register basis has cardinality `Fintype.card W * M * N`. -/
theorem actual_algorithm_dimension : Fintype.card (AlgorithmRegisters W M N)=Fintype.card W*M*N := by
  simp [AlgorithmRegisters,Registers,ZMod.card,mul_assoc]

/-- The compressed-record checkpoint has the same norm as the initial algorithm state. -/
theorem actual_checkpoint_norm
    (gates : ℕ → EuclideanSpace ℂ (AlgorithmRegisters W M N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (AlgorithmRegisters W M N))
    (initial : EuclideanSpace ℂ (AlgorithmRegisters W M N)) (t : ℕ) :
    ‖actualCheckpoint gates initial t‖=‖initial‖ := checkpoint_norm (W := W) (X := Fin M) (P := ZMod N) (L := ZMod N) (character (N := N)) (character_unitary (N := N)) gates initial t

/-- After `t` queries, the compressed-record checkpoint is supported on databases containing at
most `t` recorded entries; see [MagniezZur2026]. -/
theorem actual_checkpoint_supported
    (gates : ℕ → EuclideanSpace ℂ (AlgorithmRegisters W M N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (AlgorithmRegisters W M N))
    (initial : EuclideanSpace ℂ (AlgorithmRegisters W M N)) (t : ℕ) :
    SupportedAtMost t (actualCheckpoint gates initial t) := checkpoint_supported (W := W) (X := Fin M) (P := ZMod N) (L := ZMod N) (character (N := N)) (character_unitary (N := N)) gates initial t
end Qatlib.Papers.CollisionLB26.QueryDefs
