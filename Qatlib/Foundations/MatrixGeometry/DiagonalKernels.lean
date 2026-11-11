/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# Kernels and minima of diagonal matrices

`diagonalMap` acts by coordinatewise multiplication, and `kernelEquiv` identifies its kernel
with functions on the coordinates where the diagonal vanishes. `finrank_kernel` therefore
computes the kernel dimension by counting zero diagonal entries.

For natural-valued diagonal costs on a nonempty finite index set, `minimumCost` is attained and
equals the least real spectral value. The module uses elementary diagonal spectral theory
[HornJohnson2013].

## Main statements

* `kernelEquiv`: identify the diagonal kernel with functions on its zero coordinates.
* `finrank_kernel`: kernel dimension equals the number of zero entries.
* `minimum_isLeast`: the minimum cost is the least real spectral value.

## References

* [Horn and Johnson, 2013][HornJohnson2013]
-/

namespace Qatlib.Foundations.MatrixGeometry.DiagonalKernels
set_option autoImplicit false
noncomputable section
open scoped Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The complex linear map given by multiplication by the diagonal matrix with entries `c`. -/
def diagonalMap (c : I → ℂ) : (I → ℂ) →ₗ[ℂ] (I → ℂ) := (Matrix.diagonal c).toLin'

/-- The diagonal linear map multiplies each vector coordinate by the corresponding entry of `c`. -/
theorem diagonalMap_apply (c v : I → ℂ) (i : I) : diagonalMap c v i = c i * v i := by
  simp [diagonalMap, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

/-- A vector in the diagonal map's kernel vanishes at every coordinate whose diagonal entry is
nonzero. -/
theorem kernel_coordinate (c : I → ℂ) (v : LinearMap.ker (diagonalMap c)) (i : I)
    (hi : c i ≠ 0) : v.val i = 0 := by
  have h := congrFun v.property i
  change diagonalMap c v.val i = 0 at h
  rw [diagonalMap_apply] at h
  exact (mul_eq_zero.mp h).resolve_left hi

/-- The linear equivalence between the diagonal map's kernel and complex-valued functions on the
zero diagonal coordinates. -/
def kernelEquiv (c : I → ℂ) :
    LinearMap.ker (diagonalMap c) ≃ₗ[ℂ] ({i : I // c i = 0} → ℂ) where
  toFun v i := v.val i.val
  invFun w := ⟨fun i => if h : c i = 0 then w ⟨i,h⟩ else 0, by
    ext i
    by_cases h : c i = 0 <;> simp [diagonalMap_apply, h]⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    by_cases h : c i = 0
    · simp [h]
    · simp [h, kernel_coordinate c v i h]
  right_inv w := by funext i; simp [i.property]
  map_add' v w := rfl
  map_smul' a v := rfl

/-- The complex dimension of the diagonal map's kernel equals the number of zero diagonal
coordinates. -/
theorem finrank_kernel (c : I → ℂ) :
    Module.finrank ℂ (LinearMap.ker (diagonalMap c)) = Fintype.card {i : I // c i = 0} := by
  rw [(kernelEquiv c).finrank_eq, Module.finrank_fintype_fun_eq_card]
omit [Fintype I] in

/-- The diagonal matrix of natural-valued costs, cast to the complex numbers, is Hermitian. -/
theorem cost_hermitian (c : I → ℕ) : (Matrix.diagonal (fun i => (c i : ℂ))).IsHermitian := by
  rw [Matrix.isHermitian_diagonal_iff]
  intro i
  simp [IsSelfAdjoint]

/-- The complex spectrum of the diagonal cost matrix is exactly the range of its cast cost
entries. -/
theorem cost_spectrum (c : I → ℕ) :
    spectrum ℂ (Matrix.diagonal (fun i => (c i : ℂ))) = Set.range (fun i => (c i : ℂ)) :=
  _root_.spectrum_diagonal _
variable [Nonempty I]

/-- The minimum of the natural-valued cost function on the nonempty finite index type. -/
def minimumCost (c : I → ℕ) : ℕ :=
  (Finset.univ.image c).min' (Finset.image_nonempty.mpr Finset.univ_nonempty)
omit [DecidableEq I] in

/-- Some coordinate attains `minimumCost c`. -/
theorem minimum_attained (c : I → ℕ) : ∃ i, c i = minimumCost c := by
  have h := (Finset.univ.image c).min'_mem (Finset.image_nonempty.mpr Finset.univ_nonempty)
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
  exact ⟨i,hi⟩
omit [DecidableEq I] in

/-- The minimum cost is at most the cost at every coordinate. -/
theorem minimum_le (c : I → ℕ) (i : I) : minimumCost c ≤ c i :=
  (Finset.univ.image c).min'_le _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)

/-- The minimum cost, cast to the reals, is the least real number whose complex cast belongs to
the spectrum of the diagonal cost matrix. -/
theorem minimum_isLeast (c : I → ℕ) :
    IsLeast {e : ℝ | (e : ℂ) ∈ spectrum ℂ (Matrix.diagonal (fun i => (c i : ℂ)))}
      (minimumCost c : ℝ) := by
  constructor
  · obtain ⟨i,hi⟩ := minimum_attained c
    rw [cost_spectrum]
    exact ⟨i,by simp only [hi, Complex.ofReal_natCast]⟩
  · intro e he
    rw [cost_spectrum] at he
    obtain ⟨i,hi⟩ := he
    change (c i : ℂ) = (e : ℂ) at hi
    have heq : (c i : ℝ) = e := by exact_mod_cast hi
    rw [← heq]
    exact_mod_cast minimum_le c i
omit [DecidableEq I] in

/-- The minimum cost is zero exactly when some coordinate has zero cost. -/
theorem minimum_zero_iff (c : I → ℕ) : minimumCost c = 0 ↔ ∃ i, c i = 0 := by
  constructor
  · intro h
    obtain ⟨i,hi⟩ := minimum_attained c
    exact ⟨i,hi.trans h⟩
  · rintro ⟨i,hi⟩
    have h := minimum_le c i
    omega
end
end Qatlib.Foundations.MatrixGeometry.DiagonalKernels
