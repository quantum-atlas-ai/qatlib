/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Unitary conjugation and Gelfand-Tsetlin norm invariance

This module defines conjugation of continuous linear maps by a complex linear isometry
equivalence and proves that it preserves the operator norm. For maps satisfying
`IsUnitaryEquivariant`, the resulting norms are constant on unitary conjugacy classes, providing
the abstract invariance used in [Jordan2008a].

## Main statements

* `norm_conjCLM`: operator-norm invariance under unitary conjugation.
* `gelfand_tsetlin_norm_constant`: constant norms along a unitary conjugacy class.

## References

* [Jordan, 2008][Jordan2008a]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GroupReps08.MainResults.GelfandTsetlinNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Conjugate a continuous complex linear map by the linear isometry equivalence `V`. -/
def conjCLM (V : E ≃ₗᵢ[ℂ] E) (X : E →L[ℂ] E) : E →L[ℂ] E :=
  (V.toLinearIsometry.toContinuousLinearMap).comp
    (X.comp (V.symm.toLinearIsometry.toContinuousLinearMap))

/-- Conjugation by a complex linear isometry equivalence preserves the operator norm
[Jordan2008a]. -/
theorem norm_conjCLM (V : E ≃ₗᵢ[ℂ] E) (X : E →L[ℂ] E) : ‖conjCLM V X‖ = ‖X‖ := by
  unfold conjCLM
  rw [LinearIsometry.norm_toContinuousLinearMap_comp (f := V.toLinearIsometry)
    (g := X.comp (V.symm.toLinearIsometry.toContinuousLinearMap))]
  exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv X V.symm

/-- The operator-valued map commutes with conjugation by every complex linear isometry
equivalence. -/
def IsUnitaryEquivariant (a : (E →L[ℂ] E) → (E →L[ℂ] E)) : Prop :=
  ∀ (V : E ≃ₗᵢ[ℂ] E) (X : E →L[ℂ] E), a (conjCLM V X) = conjCLM V (a X)

/-- An equivariant operator-valued map has equal output norms on two unitarily conjugate inputs
[Jordan2008a]. -/
theorem gelfand_tsetlin_norm_independent
    (a : (E →L[ℂ] E) → (E →L[ℂ] E)) (ha : IsUnitaryEquivariant a)
    (Hp Hq : E →L[ℂ] E) (hconj : ∃ V : E ≃ₗᵢ[ℂ] E, Hq = conjCLM V Hp) :
    ‖a Hp‖ = ‖a Hq‖ := by
  obtain ⟨V, hV⟩ := hconj
  rw [hV, ha V Hp, norm_conjCLM]

/-- An equivariant operator-valued map has constant output norm on a family whose members are
pairwise unitarily conjugate [Jordan2008a]. -/
theorem gelfand_tsetlin_norm_constant
    (a : (E →L[ℂ] E) → (E →L[ℂ] E)) (ha : IsUnitaryEquivariant a)
    (H : ℕ → E →L[ℂ] E) (hclass : ∀ p q, ∃ V : E ≃ₗᵢ[ℂ] E, H q = conjCLM V (H p))
    (p q : ℕ) : ‖a (H p)‖ = ‖a (H q)‖ :=
  gelfand_tsetlin_norm_independent a ha (H p) (H q) (hclass p q)

end Qatlib.Papers.GroupReps08.MainResults.GelfandTsetlinNorm
