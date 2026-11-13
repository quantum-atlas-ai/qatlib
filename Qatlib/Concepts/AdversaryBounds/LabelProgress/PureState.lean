/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Reduced input matrices and orbit dimensions

`reducedInput C` is the positive semidefinite Gram matrix `C * Cᴴ` of an amplitude matrix, and
`support C` is its range. Its rank bounds the dimension of invariant orbit spans by the number
of algorithm coordinates, yielding a `2^S` bound when those coordinates fit in an `S`-qubit
space.

The right-unitary invariance of this Gram matrix supplies an algebraic ingredient for
label-symmetry arguments such as [MagniezZur2026]. No normalization or group-action laws are
required for the range and dimension statements here.

## Main statements

* `actual_orbit_finrank`: bound an invariant orbit span by the algorithm-coordinate count.
* `actual_qubit_orbit`: specialize the bound to a space of size at most `2^S`.
* `reducedInput_unitary`: preserve the reduced input matrix under right-unitary multiplication.

## References

* [Magniez and Zur, 2026][MagniezZur2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix Module
open scoped Classical BigOperators ComplexOrder
namespace Qatlib.Concepts.AdversaryBounds.LabelProgress
variable {I A G : Type*} [Fintype I] [Fintype A]

/-- The input-indexed Gram matrix `C * Cᴴ` of the amplitude matrix `C`. -/
def reducedInput (C : Matrix I A ℂ) : Matrix I I ℂ := C*Cᴴ
omit [Fintype I] in

/-- An entry of `reducedInput C` is the sum of `C i a * star (C j a)` over algorithm
coordinates. -/
theorem reducedInput_entry (C : Matrix I A ℂ) (i j : I) :
    reducedInput C i j=∑ a, C i a*star (C j a) := rfl

/-- The reduced input matrix of any complex amplitude matrix is positive semidefinite. -/
theorem reducedInput_psd (C : Matrix I A ℂ) : (reducedInput C).PosSemidef :=
  posSemidef_self_mul_conjTranspose C

/-- The rank of `reducedInput C` is at most the number of algorithm coordinates. -/
theorem reducedInput_rank (C : Matrix I A ℂ) : (reducedInput C).rank ≤ Fintype.card A :=
  (rank_mul_le_left C Cᴴ).trans C.rank_le_card_width

/-- The range submodule of the linear map represented by `reducedInput C`. -/
def support (C : Matrix I A ℂ) : Submodule ℂ (I → ℂ) := (reducedInput C).mulVecLin.range

/-- The support of an amplitude matrix has complex dimension at most the number of its algorithm
coordinates. -/
theorem support_finrank (C : Matrix I A ℂ) : finrank ℂ (support C) ≤ Fintype.card A :=
  reducedInput_rank C

/-- The complex linear span of the images of `v` under the indexed family of linear equivalences
`π`. -/
def orbitSpan (π : G → (I → ℂ) ≃ₗ[ℂ] (I → ℂ)) (v : I → ℂ) : Submodule ℂ (I → ℂ) :=
  Submodule.span ℂ (Set.range (fun g => π g v))

/-- If every `π g` commutes with the reduced input map, the orbit span of any vector in its
support is contained in that support. -/
theorem orbitSpan_le_support (C : Matrix I A ℂ) (π : G → (I → ℂ) ≃ₗ[ℂ] (I → ℂ))
    (hinv : ∀ g, (reducedInput C).mulVecLin.comp (π g).toLinearMap=
      (π g).toLinearMap.comp (reducedInput C).mulVecLin)
    (v : I → ℂ) (hv : v ∈ support C) : orbitSpan π v ≤ support C := by
  apply Submodule.span_le.mpr
  rintro _ ⟨g,rfl⟩
  obtain ⟨x,hx⟩ := hv
  refine ⟨π g x,?_⟩
  have he := congrArg (fun f : (I → ℂ) →ₗ[ℂ] (I → ℂ) => f x) (hinv g)
  simpa only [LinearMap.comp_apply,hx] using! he

/-- Under commutation with the reduced input map, the orbit span of a supported vector has
dimension at most the number of algorithm coordinates. -/
theorem actual_orbit_finrank (C : Matrix I A ℂ) (π : G → (I → ℂ) ≃ₗ[ℂ] (I → ℂ))
    (hinv : ∀ g, (reducedInput C).mulVecLin.comp (π g).toLinearMap=
      (π g).toLinearMap.comp (reducedInput C).mulVecLin)
    (v : I → ℂ) (hv : v ∈ support C) : finrank ℂ (orbitSpan π v) ≤ Fintype.card A :=
  (Submodule.finrank_mono (orbitSpan_le_support C π hinv v hv)).trans (support_finrank C)

/-- If the algorithm-coordinate count is at most `2^S` and the indexed equivalences commute with
the reduced input map, every supported vector's orbit span has dimension at most `2^S`. -/
theorem actual_qubit_orbit (C : Matrix I A ℂ) (π : G → (I → ℂ) ≃ₗ[ℂ] (I → ℂ))
    (hinv : ∀ g, (reducedInput C).mulVecLin.comp (π g).toLinearMap=
      (π g).toLinearMap.comp (reducedInput C).mulVecLin)
    (S : ℕ) (hspace : Fintype.card A ≤ 2^S) (v : I → ℂ) (hv : v ∈ support C) :
    finrank ℂ (orbitSpan π v) ≤ 2^S := (actual_orbit_finrank C π hinv v hv).trans hspace
omit [Fintype I] in

/-- Right multiplication by `U` satisfying `U * Uᴴ = 1` leaves the reduced input matrix
unchanged, as used in the label-symmetry setting of [MagniezZur2026]. -/
theorem reducedInput_unitary (C : Matrix I A ℂ) (U : Matrix A A ℂ)
    (hU : U*Uᴴ=1) : reducedInput (C*U)=reducedInput C := by
  simp only [reducedInput,conjTranspose_mul]
  calc
    (C*U)*(Uᴴ*Cᴴ)=(C*(U*Uᴴ))*Cᴴ := by simp only [Matrix.mul_assoc]
    _ = C*Cᴴ := by rw [hU,Matrix.mul_one]
end Qatlib.Concepts.AdversaryBounds.LabelProgress
