/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.Maps

@[expose] public section




/-!
# The definitions are not trivial

* `IsSeparable.posSemidef_partialTransposeRef`: separable operators have positive partial
  transpose.
* `not_isSeparable_bell`: the (unnormalized) maximally entangled operator on `ℂ² ⊗ ℂ^d`, `d ≥ 2`,
  is positive but not separable.
* `not_isEntanglementBreaking_id`: the identity map on `M_d`, `d ≥ 2`, is not entanglement
  breaking.
* `exists_short_composition_not_isEntanglementBreaking`: for `d ≥ 2` there is a composition of at
  most `2(d-1)` PPT maps (the empty one) that is not entanglement breaking; Theorem 1 concerns
  exactly `2(d-1)` maps.
-/

open Matrix
open scoped Kronecker ComplexOrder

noncomputable section

namespace Qatlib.Papers.PPTCompose26.Composition

open Qatlib.Foundations.PPTMatrix.OperatorCones

variable {κ n : Type*}

/-- Establishes `partialTransposeRef_kronecker`: `partialTransposeRef (A ⊗ₖ B) = Aᵀ ⊗ₖ B`, for the stated parameters. -/
theorem partialTransposeRef_kronecker (A : Matrix κ κ ℂ) (B : Matrix n n ℂ) :
    partialTransposeRef (A ⊗ₖ B) = Aᵀ ⊗ₖ B := by
  ext x y
  simp

/-- Establishes `partialTransposeRef_sum`: `partialTransposeRef (∑ i ∈ s, X i) = ∑ i ∈ s, partialTransposeRef (X i)`, for the stated parameters. -/
theorem partialTransposeRef_sum {ι : Type*} (s : Finset ι) (X : ι → Matrix (κ × n) (κ × n) ℂ) :
    partialTransposeRef (∑ i ∈ s, X i) = ∑ i ∈ s, partialTransposeRef (X i) := by
  ext x y
  simp [Matrix.sum_apply]

/-- Separable operators have positive partial transpose. -/
theorem IsSeparable.posSemidef_partialTransposeRef [Finite κ] [Finite n]
    {X : Matrix (κ × n) (κ × n) ℂ} (h : IsSeparable X) : (partialTransposeRef X).PosSemidef := by
  obtain ⟨N, A, B, hA, hB, rfl⟩ := h
  rw [partialTransposeRef_sum]
  refine Matrix.posSemidef_sum _ fun i _ => ?_
  rw [partialTransposeRef_kronecker]
  exact (hA i).transpose.kronecker (hB i)

/-- The coefficient vector of the unnormalized maximally entangled vector `|00⟩ + |11⟩` on
`ℂ² ⊗ ℂ^d`. -/
def bellVec (d : ℕ) : Fin 2 × Fin d → ℂ := fun x => if (x.1 : ℕ) = (x.2 : ℕ) then 1 else 0

/-- The maximally entangled operator on `ℂ² ⊗ ℂ^d`, `d ≥ 2`, is not separable. -/
theorem not_isSeparable_bell (d : ℕ) (hd : 2 ≤ d) : ¬ IsSeparable (pureState (bellVec d)) := by
  intro h
  have h1 : 1 < d := hd
  have h0 : 0 < d := by omega
  have hP := (IsSeparable.posSemidef_partialTransposeRef h).submatrix
    (![((0 : Fin 2), (⟨1, h1⟩ : Fin d)), ((1 : Fin 2), (⟨0, h0⟩ : Fin d))] : Fin 2 → Fin 2 × Fin d)
  have hdet : ((partialTransposeRef (pureState (bellVec d))).submatrix
      (![((0 : Fin 2), (⟨1, h1⟩ : Fin d)), ((1 : Fin 2), (⟨0, h0⟩ : Fin d))] : Fin 2 → Fin 2 × Fin d)
      ![((0 : Fin 2), (⟨1, h1⟩ : Fin d)), ((1 : Fin 2), (⟨0, h0⟩ : Fin d))]).det = -1 := by
    rw [Matrix.det_fin_two]
    simp [bellVec, pureState, Matrix.vecMulVec_apply]
  have h3 := hP.det_nonneg
  rw [hdet] at h3
  have h4 := (Complex.nonneg_iff.mp h3).1
  norm_num at h4

/-- The identity map on `M_d`, `d ≥ 2`, is not entanglement breaking. -/
theorem not_isEntanglementBreaking_id (d : ℕ) (hd : 2 ≤ d) :
    ¬ IsEntanglementBreaking (LinearMap.id : Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) := by
  rintro ⟨-, h⟩
  have hsep := h 2 (pureState (bellVec d)) (Matrix.posSemidef_vecMulVec_self_star _)
  rw [refMap_id, LinearMap.id_apply] at hsep
  exact not_isSeparable_bell d hd hsep

/-- For `d ≥ 2`, some composition of at most `2(d-1)` PPT maps on `M_d` (the empty composition) is
not entanglement breaking. -/
theorem exists_short_composition_not_isEntanglementBreaking (d : ℕ) (hd : 2 ≤ d) :
    ∃ L : List (Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)),
      L.length ≤ 2 * (d - 1) ∧ (∀ φ ∈ L, IsPPTMap φ) ∧ ¬ IsEntanglementBreaking (compList L) := by
  refine ⟨[], Nat.zero_le _, fun φ hφ => absurd hφ List.not_mem_nil, ?_⟩
  rw [compList_nil]
  exact not_isEntanglementBreaking_id d hd

end Qatlib.Papers.PPTCompose26.Composition
