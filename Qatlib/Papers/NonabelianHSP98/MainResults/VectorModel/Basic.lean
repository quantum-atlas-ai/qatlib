/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Prod
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Notation.Prod
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup

/-!
# Binary vector coordinates for the wreath product

`Vec n` consists of two binary vector blocks and a final binary coordinate. `phiEquiv`
identifies it as a set with `Wreath n`, using a coordinate swap when the final coordinate is
nonzero. The coordinate dot product is bundled as the nondegenerate bilinear form `blin`. This
development accompanies [RoettelerBeth1998].

## Main statements

* `phiEquiv`: the equivalence between wreath-product elements and binary vectors.
* `dot`: the coordinate dot product over `ZMod 2`.
* `blin_nondegenerate`: nondegeneracy of the bundled bilinear form.

## References

* [Roetteler and Beth, 1998][RoettelerBeth1998]
-/

set_option autoImplicit false

namespace Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel

open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup
open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup.Wreath
open Finset

variable {n : ℕ}

/-- Every binary residue is zero or one. -/
lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  exact h a

/-- The binary vector space consisting of two length-`n` blocks and one final coordinate. -/
abbrev Vec (n : ℕ) : Type := (Fin n → ZMod 2) × (Fin n → ZMod 2) × ZMod 2

/-- The vector coordinates of a wreath-product element, swapping its two blocks when its final
coordinate is nonzero. -/
def phi (g : Wreath n) : Vec n :=
  if g.a = 0 then (g.x, g.y, 0) else (g.y, g.x, 1)

/-- The wreath-product element associated with binary vector coordinates, reversing the block
swap encoded by the final coordinate. -/
def phiInv (v : Vec n) : Wreath n :=
  if v.2.2 = 0 then ⟨v.1, v.2.1, 0⟩ else ⟨v.2.1, v.1, 1⟩

/-- For final coordinate zero, `phi` keeps both vector blocks in their original order. -/
@[simp] lemma phi_of_a_zero {g : Wreath n} (h : g.a = 0) :
    phi g = (g.x, g.y, 0) := if_pos h

/-- For nonzero final coordinate, `phi` swaps the vector blocks and sets the final coordinate to
one. -/
@[simp] lemma phi_of_a_one {g : Wreath n} (h : g.a ≠ 0) :
    phi g = (g.y, g.x, 1) := if_neg h

/-- Applying `phiInv` after `phi` recovers the wreath-product element. -/
lemma phi_phiInv (g : Wreath n) : phiInv (phi g) = g := by
  rcases g with ⟨x, y, a⟩
  rcases zmod2_eq_zero_or_one a with h | h
  · rw [phi_of_a_zero h]; simp [phiInv, h]
  · rw [phi_of_a_one (by simp [h])]; simp [phiInv, h]

/-- Applying `phi` after `phiInv` recovers the vector. -/
lemma phiInv_phi (v : Vec n) : phi (phiInv v) = v := by
  obtain ⟨x, y, a⟩ := v
  rcases zmod2_eq_zero_or_one a with h | h
  · simp [phi, phiInv, h]
  · simp [phi, phiInv, h]

/-- The equivalence of underlying types given by `phi` and `phiInv`. -/
def phiEquiv (n : ℕ) : Wreath n ≃ Vec n where
  toFun := phi
  invFun := phiInv
  left_inv := phi_phiInv
  right_inv := phiInv_phi

/-- The forward map of `phiEquiv` is `phi`. -/
@[simp] lemma phiEquiv_apply (g : Wreath n) : phiEquiv n g = phi g := rfl

/-- The inverse map of `phiEquiv` is `phiInv`. -/
@[simp] lemma phiEquiv_symm_apply (v : Vec n) : (phiEquiv n).symm v = phiInv v := rfl

/-- The identity wreath-product element maps to the zero vector. -/
@[simp] lemma phi_one : phi (1 : Wreath n) = (0, 0, 0) := by
  change phi (oneW : Wreath n) = (0, 0, 0)
  rw [phi_of_a_zero oneW_a]
  rfl

/-- Equality of `phi` images implies equality of wreath-product elements. -/
lemma phi_inj {g h : Wreath n} (H : phi g = phi h) : g = h := by
  have := congrArg phiInv H
  simpa [phi_phiInv] using this

/-- The binary coordinate dot product on the two vector blocks and the final coordinate. -/
def dot (u v : Vec n) : ZMod 2 :=
  (∑ i, u.1 i * v.1 i) + (∑ i, u.2.1 i * v.2.1 i) + u.2.2 * v.2.2

/-- The binary dot product is symmetric. -/
lemma dot_comm (u v : Vec n) : dot u v = dot v u := by
  unfold dot
  rw [Finset.sum_congr rfl (fun i _ => mul_comm (u.1 i) (v.1 i)),
      Finset.sum_congr rfl (fun i _ => mul_comm (u.2.1 i) (v.2.1 i)),
      mul_comm u.2.2 v.2.2]

/-- The dot product with zero in the first argument is zero. -/
@[simp] lemma dot_zero_left (v : Vec n) : dot 0 v = 0 := by
  simp [dot]

/-- The dot product with zero in the second argument is zero. -/
@[simp] lemma dot_zero_right (u : Vec n) : dot u 0 = 0 := by
  simp [dot]

/-- The dot product is additive in its first argument. -/
lemma dot_add_left (u v w : Vec n) : dot (u + v) w = dot u w + dot v w := by
  simp only [dot, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]
  abel

/-- The dot product is additive in its second argument. -/
lemma dot_add_right (u v w : Vec n) : dot u (v + w) = dot u v + dot u w := by
  simp only [dot, Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]
  abel

/-- Scaling the first dot-product argument scales the result by the same binary scalar. -/
lemma dot_smul_left (c : ZMod 2) (u v : Vec n) : dot (c • u) v = c * dot u v := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
  rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
  simp only [mul_assoc]

/-- Scaling the second dot-product argument scales the result by the same binary scalar. -/
lemma dot_smul_right (c : ZMod 2) (u v : Vec n) : dot u (c • v) = c * dot u v := by
  rw [dot_comm u (c • v), dot_smul_left c v u, dot_comm v u]

/-- The bilinear form over `ZMod 2` induced by `dot`. -/
def blin : LinearMap.BilinForm (ZMod 2) (Vec n) :=
  LinearMap.mk₂ (ZMod 2) dot
    (fun u₁ u₂ v => dot_add_left u₁ u₂ v)
    (fun c u v => by rw [smul_eq_mul]; exact dot_smul_left c u v)
    (fun u v₁ v₂ => dot_add_right u v₁ v₂)
    (fun c u v => by rw [smul_eq_mul]; exact dot_smul_right c u v)

/-- Evaluating `blin` gives the coordinate dot product. -/
@[simp] lemma blin_apply (u v : Vec n) : blin u v = dot u v := rfl

/-- The bilinear form has symmetric orthogonality: if `blin x y = 0`, then `blin y x = 0`. -/
lemma blin_isRefl : blin (n := n).IsRefl := by
  intro x y h
  rw [blin_apply] at h ⊢
  rw [dot_comm]
  exact h

/-- A vector whose pairing with every vector is zero in the first argument is zero. -/
lemma blin_separatingLeft : blin (n := n).SeparatingLeft := by
  intro x hx

  have hx1 : x.1 = 0 := by
    by_contra hne
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    have h := hx (fun j => if j = i then (1 : ZMod 2) else 0, 0, 0)
    simp only [blin_apply, dot, Pi.zero_apply, zero_mul, mul_zero,
      Finset.sum_const_zero, add_zero] at h
    have hsum : (∑ j, x.1 j * (if j = i then (1 : ZMod 2) else 0)) = x.1 i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [hj]
      · intro hi'; exact absurd (Finset.mem_univ i) hi'
    rw [hsum] at h
    exact hi (by simpa using h)
  have hx2 : x.2.1 = 0 := by
    by_contra hne
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    have h := hx (0, fun j => if j = i then (1 : ZMod 2) else 0, 0)
    simp only [blin_apply, dot, Pi.zero_apply, zero_mul, mul_zero,
      Finset.sum_const_zero, add_zero] at h
    have hsum : (∑ j, x.2.1 j * (if j = i then (1 : ZMod 2) else 0)) = x.2.1 i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [hj]
      · intro hi'; exact absurd (Finset.mem_univ i) hi'
    rw [hsum] at h
    exact hi (by simpa using h)
  have hx3 : x.2.2 = 0 := by
    have h := hx (0, 0, 1)
    simpa [blin_apply, dot, mul_comm] using h
  obtain ⟨x1, x2, x3⟩ := x
  simp only at hx1 hx2 hx3
  rw [hx1, hx2, hx3]
  rfl

/-- A vector whose pairing with every vector is zero in the second argument is zero. -/
lemma blin_separatingRight : blin (n := n).SeparatingRight := by
  intro y hy
  apply blin_separatingLeft
  intro x
  rw [blin_apply, dot_comm]
  simp only [blin_apply] at hy
  exact hy x

/-- The binary coordinate bilinear form is nondegenerate. -/
lemma blin_nondegenerate : blin (n := n).Nondegenerate :=
  ⟨blin_separatingLeft, blin_separatingRight⟩

end Qatlib.Papers.NonabelianHSP98.MainResults.VectorModel
