/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.Separable

@[expose] public section




/-!
# PPT maps: outputs are PPT operators; the zero map; ordered compositions

* `IsPPTMap.posSemidef_partialTransposeRef_refMap`: a PPT map sends positive operators to
  operators with positive partial transpose on the reference (first step of Lemma 3).
* The zero map is PPT and entanglement breaking, with entanglement-breaking index `1`.
* `compList_cons`: unfolding of the ordered composition.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace Qatlib.Foundations.PPTMatrix.OperatorCones

variable {κ n p : Type*}

/-- The reference partial transpose of `(id ⊗ Φ)(X)` is the full transpose of
`(id ⊗ (t ∘ Φ))(X)`. -/
theorem partialTransposeRef_refMap (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ)
    (X : Matrix (κ × n) (κ × n) ℂ) :
    partialTransposeRef (refMap κ Φ X) = (refMap κ (transposeMap p ∘ₗ Φ) X)ᵀ := by
  ext x y
  simp

/-- A PPT map sends positive operators to operators whose partial transpose on the reference is
positive. -/
theorem IsPPTMap.posSemidef_partialTransposeRef_refMap {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ}
    (hΦ : IsPPTMap Φ) {k : ℕ} {X : Matrix (Fin k × n) (Fin k × n) ℂ} (hX : X.PosSemidef) :
    (partialTransposeRef (refMap (Fin k) Φ X)).PosSemidef := by
  rw [partialTransposeRef_refMap]
  exact (hΦ.2 k X hX).transpose

/-! ### The zero map -/

/-- Establishes `refMap_zero`: `refMap κ (0 : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) = 0`, for the stated parameters. -/
theorem refMap_zero : refMap κ (0 : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) = 0 := by
  refine LinearMap.ext fun X => ?_
  ext x y
  simp

/-- Establishes `isCompletelyPositive_zero`: `IsCompletelyPositive (0 : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ)`, for the stated parameters. -/
theorem isCompletelyPositive_zero :
    IsCompletelyPositive (0 : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) := by
  intro k X _
  rw [refMap_zero, LinearMap.zero_apply]
  exact Matrix.PosSemidef.zero

/-- Establishes `isPPTMap_zero`: `IsPPTMap (0 : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ)`, for the stated parameters. -/
theorem isPPTMap_zero : IsPPTMap (0 : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) := by
  refine ⟨isCompletelyPositive_zero, ?_⟩
  unfold IsCompletelyCopositive
  rw [LinearMap.comp_zero]
  exact isCompletelyPositive_zero

/-- Establishes `isEntanglementBreaking_zero`: `IsEntanglementBreaking (0 : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ)`, for the stated parameters. -/
theorem isEntanglementBreaking_zero :
    IsEntanglementBreaking (0 : Matrix n n ℂ →ₗ[ℂ] Matrix p p ℂ) := by
  refine ⟨isCompletelyPositive_zero, fun k X _ => ?_⟩
  rw [refMap_zero, LinearMap.zero_apply]
  exact IsSeparable.zero

/-- The zero map has entanglement-breaking index `1`. -/
theorem ebIndex_zero : ebIndex (0 : Module.End ℂ (Matrix n n ℂ)) = 1 := by
  apply le_antisymm
  · unfold ebIndex
    refine iInf_le_of_le 1 (iInf_le_of_le le_rfl (iInf_le_of_le ?_ ?_))
    · rw [pow_one]
      exact isEntanglementBreaking_zero
    · simp
  · unfold ebIndex
    refine le_iInf fun m => le_iInf fun hm => le_iInf fun _ => ?_
    exact_mod_cast hm

/-! ### Ordered compositions -/

/-- Establishes `compList_nil`: `compList ([] : List (Module.End ℂ (Matrix n n ℂ))) = LinearMap.id`, for the stated parameters. -/
@[simp]
theorem compList_nil : compList ([] : List (Module.End ℂ (Matrix n n ℂ))) = LinearMap.id :=
  rfl

/-- Establishes `foldl_comp`: `L.foldl (fun acc φ => φ ∘ₗ acc) acc = L.foldl (fun acc φ => φ ∘ₗ acc) LinearMap.id ∘ₗ acc`, for the stated parameters. -/
private theorem foldl_comp (L : List (Module.End ℂ (Matrix n n ℂ)))
    (acc : Module.End ℂ (Matrix n n ℂ)) :
    L.foldl (fun acc φ => φ ∘ₗ acc) acc =
      L.foldl (fun acc φ => φ ∘ₗ acc) LinearMap.id ∘ₗ acc := by
  induction L generalizing acc with
  | nil => simp
  | cons φ L ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (φ ∘ₗ acc), ih (φ ∘ₗ LinearMap.id),
      LinearMap.comp_id, LinearMap.comp_assoc]

/-- The head of the list is applied first. -/
theorem compList_cons (φ : Module.End ℂ (Matrix n n ℂ))
    (L : List (Module.End ℂ (Matrix n n ℂ))) : compList (φ :: L) = compList L ∘ₗ φ := by
  unfold compList
  rw [List.foldl_cons, foldl_comp L (φ ∘ₗ LinearMap.id), LinearMap.comp_id]

end Qatlib.Foundations.PPTMatrix.OperatorCones
