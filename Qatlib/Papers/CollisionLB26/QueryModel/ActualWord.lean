/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionLB26.QueryModel.CyclicBounds
import Qatlib.Concepts.CompressedQuery.CyclicRecord.AlgorithmWord
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CollisionLB26.QueryDefs
open Qatlib.Concepts.CompressedQuery.CyclicRecord
variable {W : Type*} [Fintype W] {M N : ℕ} [NeZero N]
local instance : DecidableEq (Fin M) := fun a b => Classical.propDecidable (a=b)

abbrev AlgorithmRegisters (W : Type*) (M N : ℕ) := Registers W (Fin M) (ZMod N)

def actualCheckpoint
    (gates : ℕ → EuclideanSpace ℂ (AlgorithmRegisters W M N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (AlgorithmRegisters W M N))
    (initial : EuclideanSpace ℂ (AlgorithmRegisters W M N)) (t : ℕ) :
    EuclideanSpace ℂ (DatabaseBasis W (Fin M) (ZMod N) (ZMod N)) :=
  checkpoint (W := W) (X := Fin M) (P := ZMod N) (L := ZMod N) (character (N := N)) (character_unitary (N := N)) gates initial t

theorem actual_algorithm_dimension : Fintype.card (AlgorithmRegisters W M N)=Fintype.card W*M*N := by
  simp [AlgorithmRegisters,Registers,ZMod.card,mul_assoc]

theorem actual_checkpoint_norm
    (gates : ℕ → EuclideanSpace ℂ (AlgorithmRegisters W M N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (AlgorithmRegisters W M N))
    (initial : EuclideanSpace ℂ (AlgorithmRegisters W M N)) (t : ℕ) :
    ‖actualCheckpoint gates initial t‖=‖initial‖ := checkpoint_norm (W := W) (X := Fin M) (P := ZMod N) (L := ZMod N) (character (N := N)) (character_unitary (N := N)) gates initial t

theorem actual_checkpoint_supported
    (gates : ℕ → EuclideanSpace ℂ (AlgorithmRegisters W M N) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (AlgorithmRegisters W M N))
    (initial : EuclideanSpace ℂ (AlgorithmRegisters W M N)) (t : ℕ) :
    SupportedAtMost t (actualCheckpoint gates initial t) := checkpoint_supported (W := W) (X := Fin M) (P := ZMod N) (L := ZMod N) (character (N := N)) (character_unitary (N := N)) gates initial t
end Qatlib.Papers.CollisionLB26.QueryDefs
