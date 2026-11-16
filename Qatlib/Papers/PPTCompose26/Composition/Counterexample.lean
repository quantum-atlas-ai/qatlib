/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.Separable

@[expose] public section




/-!
# Complete copositivity does not imply complete positivity

Transposition on `M_2` is completely copositive (`t ∘ t = id`) but not completely positive (the
partial transpose of the unnormalized maximally entangled operator has a negative eigenvalue).
The definition `IsPPTMap` therefore requires both properties.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace Qatlib.Papers.PPTCompose26.Composition

open Qatlib.Foundations.PPTMatrix.OperatorCones

variable {p : Type*}

/-- Establishes `transposeMap_comp_transposeMap`: `transposeMap p ∘ₗ transposeMap p = LinearMap.id`, for the stated parameters. -/
theorem transposeMap_comp_transposeMap :
    transposeMap p ∘ₗ transposeMap p = LinearMap.id := by
  refine LinearMap.ext fun X => ?_
  simp

/-- Transposition is completely copositive. -/
theorem isCompletelyCopositive_transposeMap : IsCompletelyCopositive (transposeMap p) := by
  unfold IsCompletelyCopositive
  rw [transposeMap_comp_transposeMap]
  exact isCompletelyPositive_id

/-- Transposition on `M_2` is not completely positive. -/
theorem not_isCompletelyPositive_transposeMap :
    ¬ IsCompletelyPositive (transposeMap (Fin 2)) := by
  intro h
  let v : Fin 2 × Fin 2 → ℂ := fun x => if x.1 = x.2 then 1 else 0
  have hX : (Matrix.vecMulVec v (star v)).PosSemidef := Matrix.posSemidef_vecMulVec_self_star v
  have h2 := (h 2 _ hX).submatrix (![(0, 1), (1, 0)] : Fin 2 → Fin 2 × Fin 2)
  have hdet : ((refMap (Fin 2) (transposeMap (Fin 2)) (Matrix.vecMulVec v (star v))).submatrix
      (![(0, 1), (1, 0)] : Fin 2 → Fin 2 × Fin 2) ![(0, 1), (1, 0)]).det = -1 := by
    rw [Matrix.det_fin_two]
    simp [v, Matrix.vecMulVec_apply]
  have h3 := h2.det_nonneg
  rw [hdet] at h3
  have h4 := (Complex.nonneg_iff.mp h3).1
  norm_num at h4

/-- The claim "completely copositive implies `id_k ⊗ Φ` positive" fails for transposition on
`M_2`. -/
theorem isCompletelyCopositive_and_not_isCompletelyPositive_transposeMap :
    IsCompletelyCopositive (transposeMap (Fin 2)) ∧
      ¬ IsCompletelyPositive (transposeMap (Fin 2)) :=
  ⟨isCompletelyCopositive_transposeMap, not_isCompletelyPositive_transposeMap⟩

end Qatlib.Papers.PPTCompose26.Composition
