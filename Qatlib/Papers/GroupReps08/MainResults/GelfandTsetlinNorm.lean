/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.LinearIsometry

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GroupReps08.MainResults.GelfandTsetlinNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def conjCLM (V : E ≃ₗᵢ[ℂ] E) (X : E →L[ℂ] E) : E →L[ℂ] E :=
  (V.toLinearIsometry.toContinuousLinearMap).comp
    (X.comp (V.symm.toLinearIsometry.toContinuousLinearMap))

theorem norm_conjCLM (V : E ≃ₗᵢ[ℂ] E) (X : E →L[ℂ] E) : ‖conjCLM V X‖ = ‖X‖ := by
  unfold conjCLM
  rw [LinearIsometry.norm_toContinuousLinearMap_comp (f := V.toLinearIsometry)
    (g := X.comp (V.symm.toLinearIsometry.toContinuousLinearMap))]
  exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv X V.symm

def IsUnitaryEquivariant (a : (E →L[ℂ] E) → (E →L[ℂ] E)) : Prop :=
  ∀ (V : E ≃ₗᵢ[ℂ] E) (X : E →L[ℂ] E), a (conjCLM V X) = conjCLM V (a X)

theorem gelfand_tsetlin_norm_independent
    (a : (E →L[ℂ] E) → (E →L[ℂ] E)) (ha : IsUnitaryEquivariant a)
    (Hp Hq : E →L[ℂ] E) (hconj : ∃ V : E ≃ₗᵢ[ℂ] E, Hq = conjCLM V Hp) :
    ‖a Hp‖ = ‖a Hq‖ := by
  obtain ⟨V, hV⟩ := hconj
  rw [hV, ha V Hp, norm_conjCLM]

theorem gelfand_tsetlin_norm_constant
    (a : (E →L[ℂ] E) → (E →L[ℂ] E)) (ha : IsUnitaryEquivariant a)
    (H : ℕ → E →L[ℂ] E) (hclass : ∀ p q, ∃ V : E ≃ₗᵢ[ℂ] E, H q = conjCLM V (H p))
    (p q : ℕ) : ‖a (H p)‖ = ‖a (H q)‖ :=
  gelfand_tsetlin_norm_independent a ha (H p) (H q) (hclass p q)

end Qatlib.Papers.GroupReps08.MainResults.GelfandTsetlinNorm
