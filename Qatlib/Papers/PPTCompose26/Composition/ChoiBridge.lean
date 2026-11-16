/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.PPTCompose26.Composition.Reduction
public import Qatlib.Foundations.PPTMatrix.OperatorCones.Lift
public import Qatlib.Foundations.PPTMatrix.OperatorCones.Maps

@[expose] public section




/-!
# The Choi matrix bridge

With the (unnormalized) maximally entangled vector `ω = ∑ᵢ |i⟩ ⊗ |i⟩ ∈ ℂ^d ⊗ ℂ^d`, the Choi
matrix of a map `Φ : M_d → M_p` is `(id_d ⊗ Φ)(|ω⟩⟨ω|)`. Every pure input factors through it:
`(id_k ⊗ Φ)(|v⟩⟨v|) = (V ⊗ 1) C_Φ (V ⊗ 1)ᴴ`, where `V` is the coefficient matrix of `v`. This
gives

* Choi's theorem: `Φ` is completely positive iff its Choi matrix is positive;
* `Φ` is PPT iff its Choi matrix is positive with positive reference partial transpose;
* Horodecki–Shor–Ruskai: `Φ` is entanglement breaking iff its Choi matrix is separable.
-/

open Matrix
open scoped Kronecker ComplexOrder

noncomputable section

namespace Qatlib.Papers.PPTCompose26.Composition

open Qatlib.Foundations.PPTMatrix.OperatorCones

/-- The unnormalized maximally entangled vector `ω = ∑ᵢ |i⟩ ⊗ |i⟩ ∈ ℂ^d ⊗ ℂ^d`. -/
def omegaVec (d : ℕ) : Fin d × Fin d → ℂ := fun x => if x.1 = x.2 then 1 else 0

/-- The coefficient matrix of `ω` is the identity. -/
theorem coeffMatrix_omegaVec (d : ℕ) : coeffMatrix (omegaVec d) = 1 := by
  ext i j
  simp [omegaVec, Matrix.one_apply]

/-- `(V ⊗ 1) ω = v`, where `V` is the coefficient matrix of `v`. -/
theorem mulVec_omegaVec {k d : ℕ} (v : Fin k × Fin d → ℂ) :
    (coeffMatrix v ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ omegaVec d = v := by
  apply eq_of_coeffMatrix_eq
  rw [coeffMatrix_kronecker_one_mulVec, coeffMatrix_omegaVec, Matrix.mul_one]

/-- Every pure input factors through the Choi matrix:
`(id_k ⊗ Φ)(|v⟩⟨v|) = (V ⊗ 1) (id_d ⊗ Φ)(|ω⟩⟨ω|) (V ⊗ 1)ᴴ`. -/
theorem refMap_pureState_eq_conj_choi {k d p : ℕ}
    (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ) (v : Fin k × Fin d → ℂ) :
    refMap (Fin k) Φ (pureState v) =
      (coeffMatrix v ⊗ₖ (1 : Matrix (Fin p) (Fin p) ℂ)) *
          refMap (Fin d) Φ (pureState (omegaVec d)) *
        (coeffMatrix v ⊗ₖ (1 : Matrix (Fin p) (Fin p) ℂ))ᴴ := by
  calc refMap (Fin k) Φ (pureState v)
      = refMap (Fin k) Φ
          (pureState ((coeffMatrix v ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) *ᵥ omegaVec d)) := by
        rw [mulVec_omegaVec]
    _ = _ := by rw [pureState_mulVec, refMap_refConj]

variable {d p : ℕ}

/-- **Choi's theorem.** A map is completely positive iff its Choi matrix is positive. -/
theorem isCompletelyPositive_iff_choi
    (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ) :
    IsCompletelyPositive Φ ↔ (refMap (Fin d) Φ (pureState (omegaVec d))).PosSemidef := by
  constructor
  · intro h
    exact h d _ (Matrix.posSemidef_vecMulVec_self_star _)
  · intro h k X hX
    obtain ⟨N, v, rfl⟩ := exists_sum_vecMulVec_of_posSemidef hX
    rw [map_sum]
    refine Matrix.posSemidef_sum _ fun α _ => ?_
    change (refMap (Fin k) Φ (pureState (v α))).PosSemidef
    rw [refMap_pureState_eq_conj_choi]
    exact h.mul_mul_conjTranspose_same _

/-- A map is PPT iff its Choi matrix is positive and has positive reference partial transpose. -/
theorem isPPTMap_iff_choi (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ) :
    IsPPTMap Φ ↔ (refMap (Fin d) Φ (pureState (omegaVec d))).PosSemidef ∧
      (partialTransposeRef (refMap (Fin d) Φ (pureState (omegaVec d)))).PosSemidef := by
  show IsCompletelyPositive Φ ∧ IsCompletelyPositive (transposeMap (Fin p) ∘ₗ Φ) ↔ _
  rw [isCompletelyPositive_iff_choi Φ, isCompletelyPositive_iff_choi (transposeMap (Fin p) ∘ₗ Φ),
    partialTransposeRef_refMap, Matrix.posSemidef_transpose_iff]

/-- **Horodecki–Shor–Ruskai.** A map is entanglement breaking iff its Choi matrix is
separable. -/
theorem isEntanglementBreaking_iff_choi
    (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin p) (Fin p) ℂ) :
    IsEntanglementBreaking Φ ↔ IsSeparable (refMap (Fin d) Φ (pureState (omegaVec d))) := by
  constructor
  · intro h
    exact h.2 d _ (Matrix.posSemidef_vecMulVec_self_star _)
  · intro h
    refine ⟨(isCompletelyPositive_iff_choi Φ).mpr h.posSemidef, fun k X hX => ?_⟩
    obtain ⟨N, v, rfl⟩ := exists_sum_vecMulVec_of_posSemidef hX
    rw [map_sum]
    refine IsSeparable.sum _ fun α _ => ?_
    change IsSeparable (refMap (Fin k) Φ (pureState (v α)))
    rw [refMap_pureState_eq_conj_choi]
    exact h.refConj _

end Qatlib.Papers.PPTCompose26.Composition
