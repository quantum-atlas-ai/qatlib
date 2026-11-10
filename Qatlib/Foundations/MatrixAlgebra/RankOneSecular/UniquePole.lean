/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixAlgebra.RankOneSecular.SecularAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixAlgebra.RankOneSecular
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem unique_pole_eigenvector_zero (d : I→ℝ) (u x : I→ℂ) (a z : ℝ) (i0 : I)
    (hdiag : d i0=z) (hother : ∀j,j≠i0→d j≠z) (ha : a≠0) (hu : u i0≠0)
    (heig : diagonalMinusRankOne d u a *ᵥ x=(z:ℂ)•x) : x=0 := by
  have hs:=(eigen_equation_iff d u x a z).mp heig
  let c:=∑j,star (u j)*x j
  have hi:=hs i0
  rw [hdiag,sub_self,Complex.ofReal_zero,zero_mul] at hi
  have haC : (a:ℂ)≠0 := by exact_mod_cast ha
  have hc : c=0 := (mul_eq_zero.mp hi.symm).resolve_left (mul_ne_zero haC hu)
  have hx (j : I) (hj : j≠i0) : x j=0 := by
    have hd : ((d j-z:ℝ):ℂ)≠0 := by exact_mod_cast sub_ne_zero.mpr (hother j hj)
    have h : ((d j-z:ℝ):ℂ)*x j=0 := by
      have hsj:=hs j
      change ((d j-z:ℝ):ℂ)*x j=(a:ℂ)*u j*c at hsj
      simpa only [hc,mul_zero] using hsj
    exact (mul_eq_zero.mp h).resolve_left hd
  have hone : c=star (u i0)*x i0 := by
    dsimp only [c]
    apply Finset.sum_eq_single i0
    · intro j _ hj
      rw [hx j hj,mul_zero]
    · simp
  have hstar : star (u i0)≠0 := by
    intro h
    apply hu
    simpa only [star_star,star_zero] using congrArg star h
  rw [hone] at hc
  have hzero : x i0=0 := (mul_eq_zero.mp hc).resolve_left hstar
  funext i
  by_cases hi0 : i=i0
  · subst i
    exact hzero
  · exact hx i hi0

theorem unique_pole_not_eigenvalue (d : I→ℝ) (u : I→ℂ) (a z : ℝ) (i0 : I)
    (hdiag : d i0=z) (hother : ∀j,j≠i0→d j≠z) (ha : a≠0) (hu : u i0≠0) :
    ¬∃x:I→ℂ,x≠0 ∧diagonalMinusRankOne d u a *ᵥ x=(z:ℂ)•x := by
  rintro ⟨x,hx,he⟩
  exact hx (unique_pole_eigenvector_zero d u x a z i0 hdiag hother ha hu he)
end Qatlib.Foundations.MatrixAlgebra.RankOneSecular
