/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# `Cohomology` — the low-degree group-cohomology model of Zatloukal, arXiv:1305.1327

Fixed source version: arXiv:1305.1327v1 (6 May 2013).  Text used:
`prove/assets/1305.1327.txt`, PDF
`.../assets/1305.1327.pdf` (Section 2.3 "Low Degree Group Cohomology",
Figure 1; Section 3.4 for the factorised functions `F(G,·)`).

This file fixes a concrete, faithful model of the objects used throughout
Section 3 of the paper:

* `G = ∏_i ℤ/d_i` (`CyclicProduct d`) — the structure theorem for finite
  abelian groups lets the paper assume this form for an abelian `G`
  (Section 3.4, first paragraph).
* `A` an additive commutative group (the abelian kernel of a central
  extension; the paper writes `A` additively).
* `coboundary s`, the 2-cocycle condition `IsCocycle`, the coboundaries
  `B2` and cocycles `Z2` of Figure 1 (page 5).
* the factorised functions `F(G,A)` of Section 3.4 (`FForm`), and the
  subgroup `B_F^2(G,A) = ∂F(G,A)` (`BF2`).

The model is additive on both sides: on `G = ∏ ℤ/d_i` (abelian) the cocycle
condition of Section 2.3 reads `f(y,z) - f(x+y,z) + f(x,y+z) - f(x,y) = 0`,
and `A` is written additively, exactly as in the paper.

Boundary: this is the concrete setting the paper *reduces to* for abelian
`G`.  The non-abelian total group `E` of a central extension and its
factorisations `F(G,E)` are **not** modelled here; they appear only as
abstract hypotheses in the Lemma 3.7/3.9 statements.
-/

set_option autoImplicit false

namespace Qatlib.Papers.GroupExtTest13.MainResults

open scoped BigOperators

/-! ## 2-cochains, coboundaries and cocycles (Figure 1, page 5) -/

section General

variable {G : Type*} [AddCommGroup G] {A : Type*} [AddCommGroup A]

/-- The coboundary operator `∂ : C¹(G,A) → C²(G,A)` of Figure 1:
`∂s(x,y) = s(x) + s(y) - s(x+y)` (page 5). -/
def coboundary (s : G → A) : G → G → A := fun x y => s x + s y - s (x + y)

/-- A 2-cochain is *normalized* when it vanishes on every pair involving the
identity (footnote 10, page 5). -/
def IsNormalized (f : G → G → A) : Prop :=
  (∀ x, f x 0 = 0) ∧ ∀ x, f 0 x = 0

/-- The **2-cocycle condition** of Section 2.3: `f` is normalized and
`f(y,z) - f(x+y,z) + f(x,y+z) - f(x,y) = 0` for all `x,y,z`. -/
def IsCocycle (f : G → G → A) : Prop :=
  IsNormalized f ∧ ∀ x y z, f y z - f (x + y) z + f x (y + z) - f x y = 0

/-- `B²(G,A)`, the group of 2-coboundaries: normalized cochains `s : G → A`
pushed forward by `∂` (Figure 1, page 5). -/
def B2 : Set (G → G → A) :=
  {f | ∃ s : G → A, s 0 = 0 ∧ f = coboundary s}

/-- `Z²(G,A)`, the group of 2-cocycles (Figure 1, page 5). -/
def Z2 : Set (G → G → A) := {f | IsCocycle f}

/-- `B²(G,A) ⊆ Z²(G,A)`: every coboundary `∂s` is a 2-cocycle.  This is the
first statement after Figure 1 on page 5 ("any function defined in such
manner is also a 2-cocycle.  In other words, we have `B²(G,A) ≤ Z²(G,A)`"). -/
theorem coboundary_mem_Z2 {s : G → A} (hs : s 0 = 0) : coboundary s ∈ Z2 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x
    simp [coboundary, hs]
  · intro x
    simp [coboundary, hs]
  · intro x y z
    simp only [coboundary]
    abel

end General

/-! ## The factorised functions `F(G,·)` (Section 3.4) -/

section FForm

variable {ι : Type*} [Fintype ι]
variable {A : Type*} [AddCommGroup A]

/-- The abelian group `G = ∏_i ℤ/d_i` attached to a finite tuple of moduli,
the normal form used in Section 3.4. -/
abbrev CyclicProduct (d : ι → ℕ) : Type _ := (i : ι) → ZMod (d i)

/-- The factorised functions `F(G,A)` of Section 3.4: a function
`v(x) = ∑_i x_i • a_i`, where `x_i ∈ {0,…,d_i-1}` is the standard
representative of the `i`-th coordinate (page 9).  This subset of `C¹(G,A)`
is the one for which the paper can efficiently evaluate factor sets. -/
def FForm (d : ι → ℕ) (a : ι → A) (x : CyclicProduct d) : A :=
  ∑ i, ((x i).val : ℤ) • a i

/-- `F(G,A)` is normalized: `v(0) = 0` (page 10, "we have `s(0,…,0) = 0`"). -/
theorem FForm_zero (d : ι → ℕ) (a : ι → A) : FForm d a 0 = 0 := by
  simp [FForm]

/-- `B_F²(G,A) := ∂F(G,A)`: the coboundaries of factorised functions
(Section 3.4, page 10: `B_F²(G,A) = ∂F(G,A) ⊂ ∂C¹(G,A) = B²(G,A)`). -/
def BF2 (d : ι → ℕ) : Set (CyclicProduct d → CyclicProduct d → A) :=
  {f | ∃ a : ι → A, f = coboundary (FForm d a)}

/-- `B_F²(G,A) ⊆ B²(G,A)` (Section 3.4, page 10).  This is the trivial
direction of Lemma 3.7: every `∂F`-coboundary is a coboundary. -/
theorem BF2_subset_B2 (d : ι → ℕ) :
    BF2 (A := A) d ⊆ B2 (G := CyclicProduct d) (A := A) := by
  rintro f ⟨a, rfl⟩
  exact ⟨FForm d a, FForm_zero d a, rfl⟩

end FForm

/-! ## Abstract central extensions and factor sets (Section 2.2, 3.4)

The total group `E` of a central extension is not part of the concrete model,
so for the statements of Lemmas 3.7/3.9/3.10 it is kept abstract: a
multiplicative group `E` together with a character `Multiplicative A →* E` embedding
the (abelian, central) kernel.  A section `s : G → E` determines an A-valued
factor set through `s(x) s(y) s(x+y)⁻¹ = ι(f(x,y))`. -/

section AbstractExtension

variable {Idx : Type*} [Fintype Idx]

/-- Non-commutative product of `t i ^ e i` over all indices, taken in the
(`Finset.toList`) order of `univ`.  Because the total group `E` is non-abelian,
the paper's product `∏_i t_i^{x_i}` cannot use `Finset.prod` (which needs a
`CommMonoid`); this is the corresponding ordered product. -/
noncomputable def fprod {M : Type*} [Monoid M] {ι : Type*} [Fintype ι]
    (f : ι → M) : M :=
  (Finset.univ.toList.map f).prod

/-- `s : G → E` is an `F(G,E)`-section (Section 3.4, page 9): there are
`t_i ∈ E` with `s(x) = ∏_i t_i^{x_i}`, where `x_i` is the standard
representative in `[0, d_i)`. -/
noncomputable def IsFFormSection (d : Idx → ℕ) {E : Type*} [Group E]
    (s : CyclicProduct d → E) : Prop :=
  ∃ t : Idx → E, ∀ x : CyclicProduct d, s x = fprod (fun i => t i ^ (x i).val)

/-- `f` is the A-valued factor set of the section `s` of the central extension
encoded by `ι : Multiplicative A →* E`: `s(x) s(y) s(x+y)⁻¹ = ι(f(x,y))`
(cf. the proof of Lemma 2.1, page 5). -/
def IsFactorSetD (d : Idx → ℕ) {A : Type*} [AddCommGroup A] {E : Type*} [Group E]
    (ι : Multiplicative A →* E) (s : CyclicProduct d → E)
    (f : CyclicProduct d → CyclicProduct d → A) : Prop :=
  ∀ x y, s x * s y * (s (x + y))⁻¹ = ι (Multiplicative.ofAdd (f x y))

/-- Two central extensions are *equivalent* (Section 2.2, page 3): an
isomorphism `τ : E₁ ≃* E₂` that restricts to the identity on `A`. -/
def EquivalentExtensions {A : Type*} [AddCommGroup A] {E1 E2 : Type*}
    [Group E1] [Group E2]
    (ι1 : Multiplicative A →* E1) (ι2 : Multiplicative A →* E2) : Prop :=
  ∃ τ : E1 ≃* E2, ∀ a : Multiplicative A, τ (ι1 a) = ι2 a

end AbstractExtension

/-! ## The carry identity on `ℤ/d`

The key arithmetic input for Lemma 3.8: adding the standard representatives of
`x, y ∈ ℤ/d` either stays below `d`, or "carries" exactly one `d`. -/

/-- The *carry* of the coordinate addition in `ℤ/d`, as an integer. -/
def carryZ (n : ℕ) (x y : ZMod n) : ℤ :=
  if n ≤ x.val + y.val then 1 else 0

/-- Carry identity in `ℕ`: `(x+y).val + d·δ = x.val + y.val`, where
`δ = 1` iff the sum of the standard representatives reaches `d`. -/
theorem zmod_val_add_carry (n : ℕ) [NeZero n] (x y : ZMod n) :
    (x + y).val + n * (if n ≤ x.val + y.val then 1 else 0) = x.val + y.val := by
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  have hn : 0 < n := Nat.pos_of_neZero n
  rw [ZMod.val_add, Nat.mod_eq_sub]
  have hdiv : (x.val + y.val) / n = if n ≤ x.val + y.val then 1 else 0 := by
    by_cases h : n ≤ x.val + y.val
    · rw [if_pos h]
      have h1 : 1 ≤ (x.val + y.val) / n := by
        rw [Nat.le_div_iff_mul_le hn]
        simpa using h
      have h2 : (x.val + y.val) / n < 2 := by
        rw [Nat.div_lt_iff_lt_mul hn]
        omega
      omega
    · rw [if_neg h]
      exact Nat.div_eq_of_lt (by omega)
  rw [hdiv]
  by_cases h : n ≤ x.val + y.val
  · rw [if_pos h]
    omega
  · rw [if_neg h]
    omega

/-- The carry identity in `ℤ`, the form consumed by Lemma 3.8. -/
theorem zmod_val_add_carry_z (n : ℕ) [NeZero n] (x y : ZMod n) :
    ((x + y).val : ℤ) + (n : ℤ) * (if n ≤ x.val + y.val then (1 : ℤ) else 0)
      = (x.val : ℤ) + (y.val : ℤ) := by
  have hnat := zmod_val_add_carry n x y
  by_cases h : n ≤ x.val + y.val
  · rw [if_pos h, Nat.mul_one] at hnat
    rw [if_pos h, mul_one]
    exact_mod_cast hnat
  · rw [if_neg h, Nat.mul_zero, Nat.add_zero] at hnat
    rw [if_neg h, mul_zero, add_zero]
    exact_mod_cast hnat

end Qatlib.Papers.GroupExtTest13.MainResults
