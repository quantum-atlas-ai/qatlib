/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Coordinates for Nilpotency Class Two

This module constructs a `ZMod p` coordinate group from `Coord` and `Nil2Form`, following the
algebraic setup of [IvanyosSanselmeSantha2007a]. The multiplication adds the first coordinates
and corrects the second coordinates by the alternating additive map `Nil2Form.cmt`; powers act
by repeated addition in both coordinates.

The subgroup `gPrime` consists of elements with zero first coordinate and is identified with the
derived subgroup. The maps `phi` scale the first coordinates by `j` and the second coordinates
by `j * j`, giving the identities needed for Proposition 1 in this coordinate model.

## Main statements

* `pow_coord` computes powers, and `pow_prime` shows that every `p`th power is the identity.
* `commutator_eq_gPrime` identifies the derived subgroup, while `gPrime_le_center` proves its
  centrality.
* `phi_mul` and `phi_bijective` show multiplicativity and bijectivity for nonzero parameters.
* `phi_gPrime_pow` and `exists_zg` establish the two power identities for `phi`.

## References

* [Ivanyos et al., 2007][IvanyosSanselmeSantha2007a]
-/

set_option autoImplicit false

open scoped commutatorElement

namespace Qatlib.Papers.NilpotentHSP07.MainResults

/-- A pair of vectors over `ZMod p`, with `m` coordinates in `fst` and `d` coordinates in `snd`. -/
structure Coord (p m d : ℕ) where

  fst : Fin m → ZMod p

  snd : Fin d → ZMod p

/-- Two coordinate pairs are equal if their first vectors and their second vectors are equal. -/
@[ext] theorem Coord.ext {p : ℕ} {m d : ℕ} {g h : Coord p m d} (hf : g.fst = h.fst)
    (hs : g.snd = h.snd) : g = h := by
  cases g
  cases h
  simp_all

/-- An additive alternating map in two vector arguments whose skew differences attain every
vector in the second-coordinate space. This data specifies the correction term in coordinate
multiplication. -/
class Nil2Form (p m d : ℕ) where

  cmt : (Fin m → ZMod p) → (Fin m → ZMod p) → (Fin d → ZMod p)

  cmt_zero_left : ∀ y, cmt 0 y = 0

  cmt_add_left : ∀ x₁ x₂ y, cmt (x₁ + x₂) y = cmt x₁ y + cmt x₂ y

  cmt_zero_right : ∀ x, cmt x 0 = 0

  cmt_add_right : ∀ x y₁ y₂, cmt x (y₁ + y₂) = cmt x y₁ + cmt x y₂

  cmt_self : ∀ x, cmt x x = 0

  surj_comm : ∀ w, ∃ x y, cmt x y - cmt y x = w

variable {p : ℕ} [Fact p.Prime] {m d : ℕ}

instance instMul [F : Nil2Form p m d] : Mul (Coord p m d) :=
  ⟨fun g h => ⟨g.fst + h.fst, g.snd + h.snd + F.cmt g.fst h.fst⟩⟩

instance instOne : One (Coord p m d) := ⟨⟨0, 0⟩⟩

instance instInv : Inv (Coord p m d) := ⟨fun g => ⟨-g.fst, -g.snd⟩⟩

/-- The first coordinate vector of the identity is zero. -/
@[simp] theorem one_fst : (1 : Coord p m d).fst = 0 := rfl

/-- The second coordinate vector of the identity is zero. -/
@[simp] theorem one_snd : (1 : Coord p m d).snd = 0 := rfl

/-- The first coordinate vector of an inverse is the negative of the original first coordinate
vector. -/
@[simp] theorem inv_fst (g : Coord p m d) : g⁻¹.fst = -g.fst := rfl

/-- The second coordinate vector of an inverse is the negative of the original second coordinate
vector. -/
@[simp] theorem inv_snd (g : Coord p m d) : g⁻¹.snd = -g.snd := rfl

section GroupLaws

variable [F : Nil2Form p m d]

/-- The first coordinate vector of a product is the sum of the two first coordinate vectors. -/
@[simp] theorem mul_fst (g h : Coord p m d) : (g * h).fst = g.fst + h.fst := rfl

/-- The second coordinate vector of a product is the sum of the second coordinate vectors plus
the correction term `F.cmt g.fst h.fst`. -/
@[simp] theorem mul_snd (g h : Coord p m d) : (g * h).snd = g.snd + h.snd + F.cmt g.fst h.fst := rfl

/-- Coordinate multiplication is given by addition in the first vector and corrected addition in
the second vector. -/
theorem mul_eq_mk (g h : Coord p m d) :
    g * h = ⟨g.fst + h.fst, g.snd + h.snd + F.cmt g.fst h.fst⟩ := rfl

/-- Negating the first argument of the correction map negates its value. -/
theorem cmt_neg_left (x : Fin m → ZMod p) (y : Fin m → ZMod p) :
    F.cmt (-x) y = -F.cmt x y := by
  have h : F.cmt x y + F.cmt (-x) y = 0 := by
    rw [← F.cmt_add_left, add_neg_cancel, F.cmt_zero_left]
  exact eq_neg_of_add_eq_zero_right h

/-- Negating the second argument of the correction map negates its value. -/
theorem cmt_neg_right (x : Fin m → ZMod p) (y : Fin m → ZMod p) :
    F.cmt x (-y) = -F.cmt x y := by
  have h : F.cmt x y + F.cmt x (-y) = 0 := by
    rw [← F.cmt_add_right, add_neg_cancel, F.cmt_zero_right]
  exact eq_neg_of_add_eq_zero_right h

/-- Natural-number scaling in the first argument scales the correction map's value by the same
number. -/
theorem cmt_nsmul_left (n : ℕ) (x y : Fin m → ZMod p) :
    F.cmt (n • x) y = n • F.cmt x y := by
  induction n with
  | zero => simp [F.cmt_zero_left]
  | succ n ih => rw [succ_nsmul, F.cmt_add_left, ih, succ_nsmul]

/-- Natural-number scaling in the second argument scales the correction map's value by the same
number. -/
theorem cmt_nsmul_right (n : ℕ) (x y : Fin m → ZMod p) :
    F.cmt x (n • y) = n • F.cmt x y := by
  induction n with
  | zero => simp [F.cmt_zero_right]
  | succ n ih => rw [succ_nsmul, F.cmt_add_right, ih, succ_nsmul]

/-- Repeated addition of a vector over `ZMod p` agrees with scalar multiplication by the
corresponding element of `ZMod p`. -/
theorem natCast_smul_coord (n : ℕ) (v : Fin d → ZMod p) :
    n • v = (n : ZMod p) • v := by
  funext i
  simp [nsmul_eq_mul]

/-- Scaling the two correction-map arguments by `a` and `b` scales its value by `a * b`. -/
theorem cmt_smul (a b : ZMod p) (x y : Fin m → ZMod p) :
    F.cmt (a • x) (b • y) = (a * b) • F.cmt x y := by
  have hx : a • x = a.val • x := by
    funext i
    simp [nsmul_eq_mul, ZMod.natCast_zmod_val]
  have hy : b • y = b.val • y := by
    funext i
    simp [nsmul_eq_mul, ZMod.natCast_zmod_val]
  rw [hx, hy, cmt_nsmul_left, cmt_nsmul_right, smul_smul, natCast_smul_coord, Nat.cast_mul,
    ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

/-- The coordinate multiplication determined by `Nil2Form` is associative. -/
theorem mul_assoc_coord (a b c : Coord p m d) : a * b * c = a * (b * c) := by
  apply Coord.ext <;> funext i
  · simp
    abel
  · simp [F.cmt_add_left, F.cmt_add_right]
    abel

instance instGroup : Group (Coord p m d) :=
  Group.ofLeftAxioms
    (by intro a b c; exact mul_assoc_coord a b c)
    (by intro a; apply Coord.ext <;> funext i <;> simp [F.cmt_zero_left])
    (by intro a; apply Coord.ext <;> funext i <;> simp [F.cmt_zero_left, cmt_neg_left, F.cmt_self])

/-- The `n`th power of a coordinate element is obtained by repeated addition of each coordinate
vector `n` times. -/
theorem pow_coord (g : Coord p m d) (n : ℕ) : g ^ n = ⟨n • g.fst, n • g.snd⟩ := by
  induction n with
  | zero =>
    rw [pow_zero, zero_smul, zero_smul]
    exact Coord.ext one_fst one_snd
  | succ n ih =>
    rw [pow_succ, ih]
    apply Coord.ext
    · funext i
      rw [mul_fst]
      simp only [Pi.add_apply, Pi.smul_apply, succ_nsmul]
    · funext i
      rw [mul_snd]
      simp only [Pi.add_apply, Pi.smul_apply, succ_nsmul, cmt_nsmul_left, F.cmt_self,
        Pi.zero_apply, smul_zero, add_zero]

/-- The `p`th power of every coordinate group element is the identity. -/
theorem pow_prime (g : Coord p m d) : g ^ p = 1 := by
  rw [pow_coord, natCast_smul_coord, natCast_smul_coord, ZMod.natCast_self, zero_smul,
    zero_smul]
  rfl

end GroupLaws

section DerivedSubgroup

variable [F : Nil2Form p m d]

/-- The subgroup of coordinate elements whose first vector is zero. -/
def gPrime : Subgroup (Coord p m d) where
  carrier := {g | g.fst = 0}
  mul_mem' := by
    intro a b ha hb
    have ha' : a.fst = 0 := ha
    have hb' : b.fst = 0 := hb
    show (a * b).fst = 0
    rw [mul_fst, ha', hb', add_zero]
  one_mem' := rfl
  inv_mem' := by
    intro a ha
    have ha' : a.fst = 0 := ha
    show a⁻¹.fst = 0
    rw [inv_fst, ha', neg_zero]

/-- Membership in `gPrime` is equivalent to having zero first coordinate vector. -/
theorem mem_gPrime (g : Coord p m d) : g ∈ gPrime (p := p) (m := m) (d := d) ↔ g.fst = 0 := Iff.rfl

/-- Every element commutator has zero first coordinate vector. -/
theorem commutator_fst (g h : Coord p m d) : (⁅g, h⁆).fst = 0 := by
  funext i
  simp [commutatorElement_def]

/-- The derived subgroup of the coordinate group is contained in `gPrime`. -/
theorem commutator_le_gPrime : ⁅(⊤ : Subgroup (Coord p m d)), ⊤⁆ ≤ gPrime (p := p) (m := m) (d := d) := by
  rw [Subgroup.commutator_le]
  intro g _ h _
  rw [mem_gPrime]
  exact commutator_fst g h

/-- Every element of `gPrime` is central in the coordinate group. -/
theorem gPrime_le_center : gPrime (p := p) (m := m) (d := d) ≤ Subgroup.center (Coord p m d) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  have hz' : z.fst = 0 := hz
  apply Coord.ext
  · funext i
    simp [mul_fst]
    abel
  · funext i
    simp [mul_snd, hz', F.cmt_zero_left, F.cmt_zero_right]
    abel

/-- The derived subgroup of the coordinate group is contained in its center. -/
theorem derived_le_center :
    ⁅(⊤ : Subgroup (Coord p m d)), ⊤⁆ ≤ Subgroup.center (Coord p m d) :=
  le_trans commutator_le_gPrime gPrime_le_center

/-- The commutator of coordinate elements `(x, 0)` and `(y, 0)` is `(0, F.cmt x y - F.cmt y x)`. -/
theorem commutator_pair (x y : Fin m → ZMod p) :
    (⁅(⟨x, 0⟩ : Coord p m d), (⟨y, 0⟩ : Coord p m d)⁆) = ⟨0, F.cmt x y - F.cmt y x⟩ := by
  apply Coord.ext <;> funext i
  · simp only [commutatorElement_def, mul_fst, inv_fst, mul_snd, Pi.add_apply, Pi.neg_apply,
      Pi.zero_apply]
    abel
  · simp [commutatorElement_def, mul_fst, inv_fst, inv_snd, mul_snd, F.cmt_add_left,
      F.cmt_add_right, cmt_neg_left, cmt_neg_right, F.cmt_zero_left, F.cmt_zero_right,
      F.cmt_self] <;> abel

/-- Every element of `gPrime` belongs to the derived subgroup of the coordinate group. -/
theorem gPrime_le_commutator : gPrime (p := p) (m := m) (d := d) ≤ ⁅(⊤ : Subgroup (Coord p m d)), ⊤⁆ := by
  intro z hz
  have hz' : z.fst = 0 := hz
  obtain ⟨x, y, hxy⟩ := F.surj_comm z.snd
  have hzeq : z = ⟨0, F.cmt x y - F.cmt y x⟩ := by
    apply Coord.ext
    · exact hz'
    · exact hxy.symm
  rw [hzeq, ← commutator_pair x y]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- The derived subgroup of the coordinate group is exactly `gPrime`. -/
theorem commutator_eq_gPrime : ⁅(⊤ : Subgroup (Coord p m d)), ⊤⁆ = gPrime (p := p) (m := m) (d := d) :=
  le_antisymm commutator_le_gPrime gPrime_le_commutator

/-- The commutator of two products expands into the product of the four pairwise commutators in
the displayed order. -/
theorem commutator_mul_mul (g₁ g₂ g₃ g₄ : Coord p m d) :
    ⁅g₁ * g₂, g₃ * g₄⁆ = ⁅g₁, g₃⁆ * ⁅g₁, g₄⁆ * ⁅g₂, g₃⁆ * ⁅g₂, g₄⁆ := by
  apply Coord.ext <;> funext i
  · simp only [commutatorElement_def, mul_fst, inv_fst, mul_snd, Pi.add_apply, Pi.neg_apply,
      Pi.zero_apply]
    abel
  · simp [commutatorElement_def, mul_fst, inv_fst, inv_snd, mul_snd, F.cmt_add_left,
      F.cmt_add_right, cmt_neg_left, cmt_neg_right, F.cmt_zero_left, F.cmt_zero_right,
      F.cmt_self] <;> abel

end DerivedSubgroup

section Automorphisms

variable [F : Nil2Form p m d]

/-- The coordinate map scaling the first vector by `j` and the second vector by `j * j`. -/
def phi (j : ZMod p) (g : Coord p m d) : Coord p m d :=
  ⟨j • g.fst, (j * j) • g.snd⟩

/-- The coordinate map with parameter one is the identity map. -/
theorem phi_one (g : Coord p m d) : phi 1 g = g := by
  apply Coord.ext <;> funext i <;> simp [phi]

/-- The coordinate map with parameter zero sends every element to the group identity. -/
theorem phi_zero (g : Coord p m d) : phi 0 g = 1 := by
  apply Coord.ext <;> funext i <;> simp [phi]

/-- The coordinate map `phi j` preserves multiplication for every parameter `j`. This provides
multiplicativity of the coordinate maps used in [IvanyosSanselmeSantha2007a]. -/
theorem phi_mul (j : ZMod p) (g h : Coord p m d) : phi j (g * h) = phi j g * phi j h := by
  apply Coord.ext <;> funext i
  · simp [phi]
  · simp only [phi, mul_fst, mul_snd, smul_add, cmt_smul, Pi.add_apply, Pi.smul_apply] <;> abel

/-- For nonzero `j`, the coordinate map `phi j` is bijective. This provides bijectivity of the
nonzero coordinate scalings used in [IvanyosSanselmeSantha2007a]. -/
theorem phi_bijective (j : ZMod p) (hj : j ≠ 0) : Function.Bijective (phi (p := p) (m := m) (d := d) j) := by
  have hj2 : j * j ≠ 0 := mul_ne_zero hj hj
  constructor
  · intro g h hgh
    have hf : g.fst = h.fst := by
      have h' := congrArg Coord.fst hgh
      simp only [phi] at h'
      funext i
      have hi := congrArg (fun v : Fin m → ZMod p => v i) h'
      simpa using (mul_left_cancel₀ hj hi)
    have hs : g.snd = h.snd := by
      have h' := congrArg Coord.snd hgh
      simp only [phi] at h'
      funext i
      have hi := congrArg (fun v : Fin d → ZMod p => v i) h'
      simpa using (mul_left_cancel₀ hj2 hi)
    exact Coord.ext hf hs
  · intro g
    refine ⟨phi j⁻¹ g, ?_⟩
    have h1 : (phi j (phi j⁻¹ g)).fst = g.fst := by
      simp [phi, smul_smul, mul_inv_cancel₀ hj]
    have h2 : (phi j (phi j⁻¹ g)).snd = g.snd := by
      have hinv : j⁻¹ * j⁻¹ = (j * j)⁻¹ := (mul_inv_rev j j).symm
      have : j * j * (j⁻¹ * j⁻¹) = 1 := by
        rw [hinv, mul_inv_cancel₀ hj2]
      simp [phi, smul_smul, this]
    exact Coord.ext h1 h2

/-- On `gPrime`, the map `phi j` agrees with raising an element to the natural representative of
`j * j`. This is the first power identity of [Ivanyos et al., Proposition
1][IvanyosSanselmeSantha2007a] in the coordinate model. -/
theorem phi_gPrime_pow (j : ZMod p) (z : Coord p m d) (hz : z ∈ gPrime) :
    phi j z = z ^ (j * j).val := by
  have hz' : z.fst = 0 := hz
  rw [pow_coord]
  apply Coord.ext <;> funext i
  · simp [phi, hz']
  · simp only [phi, hz', smul_zero]
    rw [natCast_smul_coord, ZMod.natCast_zmod_val]

/-- For every coordinate element `g`, there is an element `z` in the derived subgroup such that
`phi j g = g ^ j.val * z ^ (j - j * j).val` for every `j`. This is the second power identity
of [Ivanyos et al., Proposition 1][IvanyosSanselmeSantha2007a] in the coordinate model. -/
theorem exists_zg (g : Coord p m d) :
    ∃ z ∈ ⁅(⊤ : Subgroup (Coord p m d)), (⊤ : Subgroup (Coord p m d))⁆,
      ∀ j : ZMod p, phi j g = g ^ j.val * z ^ ((j - j * j : ZMod p)).val := by
  refine ⟨(⟨0, -g.snd⟩ : Coord p m d), ?_, ?_⟩
  · rw [commutator_eq_gPrime]
    show ((⟨0, -g.snd⟩ : Coord p m d)).fst = 0
    rfl
  · intro j
    rw [pow_coord, pow_coord]
    apply Coord.ext <;> funext i
    · simp only [phi, mul_fst, zero_add, Pi.add_apply, Pi.smul_apply, smul_zero, add_zero,
        Pi.zero_apply]
      simp [nsmul_eq_mul, ZMod.natCast_zmod_val]
    · simp only [phi, mul_fst, mul_snd, zero_add, smul_zero, F.cmt_zero_right, add_zero,
        smul_neg, Pi.zero_apply, Pi.smul_apply, Pi.add_apply, Pi.neg_apply]
      simp [nsmul_eq_mul, ZMod.natCast_zmod_val]
      ring

end Automorphisms

end Qatlib.Papers.NilpotentHSP07.MainResults
