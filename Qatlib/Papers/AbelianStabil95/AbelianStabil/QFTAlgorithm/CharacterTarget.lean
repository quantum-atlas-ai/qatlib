/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.AbelianSampling.OrbitFourierBasisSubgoalQuan
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.HspRecovery.AbelianSampling
open Qatlib.Foundations.PureStateMath
open scoped BigOperators
namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.QFTAlgorithm

def characterQFT (E : Type) [AddCommGroup E] [Fintype E] [DecidableEq E]
    (labels : E ≃ AddChar E ℂ) : Matrix E E ℂ := fun x j => orbitFourierVec E (labels j) x

theorem characterQFT_unitary (E : Type) [AddCommGroup E] [Fintype E] [DecidableEq E]
    (labels : E ≃ AddChar E ℂ) : characterQFT E labels ∈ Matrix.unitaryGroup E ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  have h := (orbitFourierBasisSubgoal E).1 (labels i) (labels j)
  simpa [characterQFT, inner_apply, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Matrix.one_apply, labels.injective.eq_iff] using h

theorem characterLabelsExist (E : Type) [AddCommGroup E] [Fintype E] :
    Nonempty (E ≃ AddChar E ℂ) := Fintype.card_eq.mp AddChar.card_eq.symm

theorem characterQFT_entry (E : Type) [AddCommGroup E] [Fintype E] [DecidableEq E]
    (labels : E ≃ AddChar E ℂ) (x j : E) :
    characterQFT E labels x j = (Real.sqrt (Fintype.card E : ℝ))⁻¹ * labels j x := rfl

end Qatlib.Papers.AbelianStabil95.AbelianStabil.QFTAlgorithm
