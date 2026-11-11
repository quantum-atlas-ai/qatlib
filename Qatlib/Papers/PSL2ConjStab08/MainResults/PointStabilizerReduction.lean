/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.Matrix.Action
import Mathlib.Data.Matrix.Mul

/-!
# Affine point stabilizer reductions

`AffineGroup` equips `V × G` with the semidirect-product group law and its affine action on `V`.
Translation conjugacy and linear stabilizer intersections explain point-stabilizer reductions,
while a movement hypothesis ensures distinct points have distinct stabilizers, as used in the
setting of [DenneyMooreRussell2008].

## Main statements

* `stabilizer_eq_map_conj`: translations conjugate the stabilizer of zero to each point
  stabilizer.
* `stabilizer_injective_of_moves_nonzero`: moving every nonzero vector makes the
  point-stabilizer map injective.

## References

* [Denney et al., 2008][DenneyMooreRussell2008]
-/

set_option autoImplicit false
noncomputable section

open MulAction
open scoped Matrix

namespace Qatlib.Papers.PSL2ConjStab08.MainResults.PointStabilizerReduction

/-- The underlying type `V × G` for the affine semidirect product determined by the action of
`G` on `V`. -/
abbrev AffineGroup (V G : Type*) [AddCommGroup V] [Group G] [DistribMulAction G V] :=
  V × G

namespace AffineGroup

variable {V G : Type*} [AddCommGroup V] [Group G] [DistribMulAction G V]

instance : Mul (AffineGroup V G) where
  mul x y := (x.1 + x.2 • y.1, x.2 * y.2)

instance : One (AffineGroup V G) where
  one := (0, 1)

instance : Inv (AffineGroup V G) where
  inv x := (-(x.2⁻¹ • x.1), x.2⁻¹)

/-- Affine multiplication combines translations as `x.1 + x.2 • y.1` and multiplies the linear
parts. -/
@[simp] theorem mul_def (x y : AffineGroup V G) :
    x * y = (x.1 + x.2 • y.1, x.2 * y.2) := rfl

/-- The identity affine element is `(0, 1)`. -/
@[simp] theorem one_def : (1 : AffineGroup V G) = (0, 1) := rfl

/-- The inverse affine element has translation `−(x.2⁻¹ • x.1)` and linear part `x.2⁻¹`. -/
@[simp] theorem inv_def (x : AffineGroup V G) :
    x⁻¹ = (-(x.2⁻¹ • x.1), x.2⁻¹) := rfl

instance : Group (AffineGroup V G) where
  mul_assoc x y z := by
    apply Prod.ext <;>
      simp [mul_def, smul_add, smul_smul, add_assoc, mul_assoc]
  one_mul x := by
    apply Prod.ext <;> simp [mul_def, one_def]
  mul_one x := by
    apply Prod.ext <;> simp [mul_def, one_def]
  inv_mul_cancel x := by
    apply Prod.ext <;> simp [mul_def, one_def, inv_def]

/-- The pure translation by `v`, represented by `(v, 1)`. -/
def inl (v : V) : AffineGroup V G := (v, 1)

/-- The multiplicative homomorphism embedding a linear group element as the affine element `(0,
g)`. -/
def inrHom : G →* AffineGroup V G where
  toFun g := (0, g)
  map_one' := rfl
  map_mul' g h := by
    show ((0 : V), g * h) = (0, g) * (0, h)
    rw [mul_def]
    simp

/-- The translation embedding sends `v` to `(v, 1)`. -/
@[simp] theorem inl_def (v : V) : inl (G := G) v = (v, 1) := rfl

/-- The linear embedding sends `g` to `(0, g)`. -/
@[simp] theorem inrHom_apply (g : G) : inrHom (V := V) g = (0, g) := rfl

instance : MulAction (AffineGroup V G) V where
  smul x v := x.1 + x.2 • v
  one_smul v := by
    show (0 : V) + (1 : G) • v = v
    simp
  mul_smul x y v := by
    show (x.1 + x.2 • y.1) + (x.2 * y.2) • v = x.1 + x.2 • (y.1 + y.2 • v)
    rw [smul_add, smul_smul, add_assoc]

/-- The affine action sends `v` to `x.1 + x.2 • v`. -/
@[simp] theorem smul_def (x : AffineGroup V G) (v : V) :
    x • v = x.1 + x.2 • v := rfl

/-- The subgroup of linear group elements fixing `v`. -/
def linearFixing (v : V) : Subgroup G where
  carrier := {g | g • v = v}
  one_mem' := one_smul G v
  mul_mem' {g h} hg hh := by
    have hg' : g • v = v := hg
    have hh' : h • v = v := hh
    show (g * h) • v = v
    rw [mul_smul, hh']
    exact hg'
  inv_mem' {g} hg := by
    have hg' : g • v = v := hg
    have h2 : g⁻¹ • (g • v) = g⁻¹ • v := congrArg (fun w => g⁻¹ • w) hg'
    rw [← mul_smul, inv_mul_cancel, one_smul] at h2
    exact h2.symm

/-- The affine stabilizer of zero is the range of the linear embedding. See
[DenneyMooreRussell2008]. -/
theorem stabilizer_zero_eq_range_inr :
    stabilizer (AffineGroup V G) (0 : V) = (inrHom : G →* AffineGroup V G).range := by
  ext x
  constructor
  · intro hx
    rw [mem_stabilizer_iff] at hx
    have hleft : x.1 = 0 := by simpa using hx
    exact ⟨x.2, by apply Prod.ext <;> simp [inrHom, hleft]⟩
  · rintro ⟨g, rfl⟩
    rw [mem_stabilizer_iff]
    simp [inrHom]

/-- The affine stabilizer of `v` is the image of the stabilizer of zero under conjugation by
translation by `v`. See [DenneyMooreRussell2008]. -/
theorem stabilizer_eq_map_conj (v : V) :
    stabilizer (AffineGroup V G) v =
      (stabilizer (AffineGroup V G) (0 : V)).map
        (MulAut.conj (inl (G := G) v)).toMonoidHom := by
  have h : (inl (G := G) v) • (0 : V) = v := by
    simp [inl, smul_def]
  have hconj := stabilizer_smul_eq_stabilizer_map_conj (inl (G := G) v) (0 : V)
  simpa [h] using hconj

/-- The intersection of the affine stabilizers of zero and `v` is the image of `linearFixing v`
under the linear embedding. See [DenneyMooreRussell2008]. -/
theorem stabilizer_zero_inf_stabilizer_eq_fixing (v : V) :
    stabilizer (AffineGroup V G) (0 : V) ⊓ stabilizer (AffineGroup V G) v =
      (linearFixing v).map (inrHom : G →* AffineGroup V G) := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_inf, mem_stabilizer_iff, mem_stabilizer_iff] at hx
    obtain ⟨h0, hv⟩ := hx
    have hleft : x.1 = 0 := by simpa using h0
    refine ⟨x.2, ?_, ?_⟩
    · show x.2 • v = v
      rw [smul_def, hleft, zero_add] at hv
      exact hv
    · apply Prod.ext <;> simp [inrHom, hleft]
  · rintro ⟨g, hg, rfl⟩
    rw [Subgroup.mem_inf, mem_stabilizer_iff, mem_stabilizer_iff]
    refine ⟨?_, ?_⟩
    · show (inrHom g) • (0 : V) = 0
      simp [inrHom, smul_def]
    · show (inrHom g) • v = v
      simpa [linearFixing, inrHom, smul_def] using hg

/-- If every nonzero vector is moved by some linear group element, the map sending a point to
its affine stabilizer is injective. See [DenneyMooreRussell2008]. -/
theorem stabilizer_injective_of_moves_nonzero
    (hmove : ∀ u : V, u ≠ 0 → ∃ g : G, g • u ≠ u) :
    Function.Injective fun v : V => stabilizer (AffineGroup V G) v := by
  intro v w hvw
  by_contra hne
  have huv : w - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  obtain ⟨g, hg⟩ := hmove (w - v) huv

  let x : AffineGroup V G := (w - g • w, g)
  have hxw : x ∈ stabilizer (AffineGroup V G) w := by
    rw [mem_stabilizer_iff]
    show (w - g • w) + g • w = w
    abel
  have hvw' : stabilizer (AffineGroup V G) v = stabilizer (AffineGroup V G) w := hvw
  have hxv : x ∈ stabilizer (AffineGroup V G) v := by
    rw [hvw']
    exact hxw
  rw [mem_stabilizer_iff] at hxv
  have hmain : (w - g • w) + g • v = v := hxv

  have hsub : g • (w - v) = w - v := by
    have hv : g • v = v - w + g • w := by
      calc g • v = ((w - g • w) + g • v) - (w - g • w) := by abel
        _ = v - (w - g • w) := by rw [hmain]
        _ = v - w + g • w := by abel
    rw [smul_sub, hv]
    abel
  exact hg hsub

instance instGLDistribMulAction (n R : Type*) [Fintype n] [DecidableEq n]
    [Semiring R] : DistribMulAction (Matrix.GeneralLinearGroup n R) (n → R) where
  smul A v := A.1 *ᵥ v
  one_smul v := by
    show (1 : Matrix n n R) *ᵥ v = v
    exact Matrix.one_mulVec v
  mul_smul A B v := by
    show (A * B).1 *ᵥ v = A.1 *ᵥ (B.1 *ᵥ v)
    rw [Units.val_mul, Matrix.mulVec_mulVec]
  smul_zero A := by
    show A.1 *ᵥ (0 : n → R) = 0
    exact Matrix.mulVec_zero A.1
  smul_add A v w := by
    show A.1 *ᵥ (v + w) = A.1 *ᵥ v + A.1 *ᵥ w
    exact Matrix.mulVec_add A.1 v w

end AffineGroup

end Qatlib.Papers.PSL2ConjStab08.MainResults.PointStabilizerReduction
