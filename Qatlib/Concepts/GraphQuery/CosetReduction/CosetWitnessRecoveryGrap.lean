/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GraphQuery.CosetReduction.CosetWitnessRecoveryStat
public import Qatlib.Concepts.GraphQuery.CosetReduction.GraphCosetReductionGrap

@[expose] public section

set_option autoImplicit false

namespace Qatlib.Concepts.GraphQuery.CosetReduction

/-- Establishes the recovery of a coset witness specified by `CosetWitnessRecovery`. -/
theorem cosetWitnessRecovery : CosetWitnessRecovery := by
  intro V A B k hk hcoset
  rcases (mem_encoded_coset_iff A B k).mp hcoset with ⟨p, rfl⟩
  refine ⟨p, ?_, (lifted_mem_color_iff A B p).mp hk⟩
  intro i
  unfold recoverVertex
  have hcancel : (flipMatrix B)⁻¹ *
      (flipMatrix B * liftPerm p * (flipMatrix A)⁻¹) * flipMatrix A = liftPerm p := by
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  rw [hcancel]
  rfl

end Qatlib.Concepts.GraphQuery.CosetReduction
