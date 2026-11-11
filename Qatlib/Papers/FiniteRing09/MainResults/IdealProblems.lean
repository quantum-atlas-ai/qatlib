/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Tactic

/-!
# Algebraic criteria for finite-ring ideal problems

The module collects subgroup cardinality and coset tests, criteria for units, and basic ideal
and ring-homomorphism characterizations. It defines the left ideal quotient `idealColon` and the
left annihilator, and expresses additive generation by integer coefficients. These are algebraic
ingredients for finite-ring ideal processing.

These constructions belong to the formalization of [WocjanEtAl2009].

## Main statements

* `source_ideal_equality_overlap`: bounds the intersection size of distinct finite additive
  subgroups.
* `source_linear_system_solvable`: characterizes integer linear combinations by additive
  closure.
* `source_nonunit_leftIdeal_half`: bounds the principal left ideal of a nonunit.

## References

* [Wocjan et al., 2009][WocjanEtAl2009]
-/

set_option autoImplicit false

namespace Qatlib.Papers.FiniteRing09.MainResults.IdealProblems

/-- Strict inclusion of finite additive subgroups increases cardinality by at least a factor of
two. See [WocjanEtAl2009]. -/
theorem strict_inclusion_doubling
    {A : Type*} [AddCommGroup A] [Finite A]
    {B C : AddSubgroup A} (hBC : B < C) :
    2 * Nat.card B ≤ Nat.card C := by
  have hle : B ≤ C := hBC.le
  let K : AddSubgroup C := B.comap C.subtype
  have hKtop : K ≠ ⊤ := by
    intro htop
    apply hBC.2
    intro x hx
    have hxK : (⟨x, hx⟩ : C) ∈ K := by
      rw [htop]
      simp
    have hmem : ((⟨x, hx⟩ : C) : A) ∈ B := AddSubgroup.mem_comap.mp hxK
    simpa using hmem
  haveI : Finite C := Subtype.finite
  haveI : Finite (C ⧸ K) := inferInstance
  have hidx : 1 < K.index := AddSubgroup.one_lt_index_of_ne_top hKtop
  have hcard : Nat.card K * K.index = Nat.card C := K.card_mul_index
  have hcardK : Nat.card K = Nat.card B :=
    Nat.card_congr
      { toFun := fun x => (⟨(x.1 : A), x.2⟩ : B)
        invFun := fun y => (⟨⟨(y.1 : A), hle y.2⟩, y.2⟩ : K)
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => Subtype.ext rfl }
  calc 2 * Nat.card B = Nat.card B * 2 := Nat.mul_comm 2 (Nat.card B)
    _ ≤ Nat.card B * K.index := Nat.mul_le_mul_left _ hidx
    _ = Nat.card K * K.index := by rw [hcardK]
    _ = Nat.card C := hcard

/-- For distinct finite additive subgroups, twice the squared intersection cardinality is at
most the product of their cardinalities. See [WocjanEtAl2009]. -/
theorem source_ideal_equality_overlap
    {A : Type*} [AddCommGroup A] [Finite A]
    {H K : AddSubgroup A} (hHK : H ≠ K) :
    2 * Nat.card ↥(H ⊓ K) ^ 2 ≤ Nat.card H * Nat.card K := by
  have hcardInfK : Nat.card ↥(H ⊓ K) ≤ Nat.card K :=
    Nat.card_le_card_of_injective
      (f := fun x : ↥(H ⊓ K) =>
        (⟨(x : A), (inf_le_right : H ⊓ K ≤ K) x.2⟩ : K))
      (fun x y hxy => by
        have hval := congrArg (fun z : K => (z : A)) hxy
        simpa using hval)
  by_cases hsub : H ≤ K
  · have hinf : H ⊓ K = H := inf_eq_left.mpr hsub
    have hlt : H < K := lt_of_le_of_ne hsub hHK
    have hdbl : 2 * Nat.card H ≤ Nat.card K := strict_inclusion_doubling hlt
    rw [hinf]
    calc 2 * Nat.card H ^ 2 = (2 * Nat.card H) * Nat.card H := by ring
      _ ≤ Nat.card K * Nat.card H := Nat.mul_le_mul hdbl le_rfl
      _ = Nat.card H * Nat.card K := Nat.mul_comm _ _
  · have hne : H ⊓ K ≠ H := fun heq => hsub (inf_eq_left.mp heq)
    have hlt : H ⊓ K < H :=
      lt_of_le_of_ne (inf_le_left : H ⊓ K ≤ H) hne
    have hdbl : 2 * Nat.card ↥(H ⊓ K) ≤ Nat.card H := strict_inclusion_doubling hlt
    calc 2 * Nat.card ↥(H ⊓ K) ^ 2
        = (2 * Nat.card ↥(H ⊓ K)) * Nat.card ↥(H ⊓ K) := by ring
      _ ≤ Nat.card H * Nat.card K := Nat.mul_le_mul hdbl hcardInfK

/-- An element belongs to an additive subgroup exactly when its left translate of that subgroup
is the subgroup itself. See [WocjanEtAl2009]. -/
theorem source_membership_coset
    {A : Type*} [AddGroup A] (H : AddSubgroup A) (r : A) :
    r ∈ H ↔ Set.image (fun h => r + h) (H : Set A) = (H : Set A) := by
  constructor
  · intro hr
    ext x
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact H.add_mem hr hh
    · intro hx
      refine ⟨-r + x, H.add_mem (H.neg_mem hr) hx, ?_⟩
      change r + (-r + x) = x
      rw [← add_assoc, add_neg_cancel, zero_add]
  · intro himg
    have h0 : (0 : A) ∈ Set.image (fun h => r + h) (H : Set A) := by
      rw [himg]
      exact H.zero_mem
    rcases h0 with ⟨h, hh, he⟩
    have hr : r = -h := by
      rw [eq_neg_iff_add_eq_zero]
      exact he
    rw [hr]
    exact H.neg_mem hh

/-- An element of a monoid is a unit exactly when left multiplication by it is bijective. See
[WocjanEtAl2009]. -/
theorem source_unit_criterion
    {R : Type*} [Monoid R] {r : R} :
    IsUnit r ↔ Function.Bijective (fun x => r * x) :=
  IsUnit.isUnit_iff_mulLeft_bijective

/-- In a finite ring, an element is a unit exactly when it possesses a left inverse. See
[WocjanEtAl2009]. -/
theorem source_unit_iff_left_inverse
    {R : Type*} [Ring R] [Finite R] {r : R} :
    IsUnit r ↔ ∃ x : R, x * r = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨↑u⁻¹, Units.inv_mul u⟩
  · rintro ⟨x, hx⟩
    have hinj : Function.Injective (fun a : R => r * a) := by
      intro a b hab
      have h := congrArg (fun y => x * y) hab
      simpa [← mul_assoc, hx] using h
    exact IsUnit.isUnit_iff_mulLeft_bijective.mpr
      ⟨hinj, Finite.surjective_of_injective hinj⟩

/-- In a commutative ring, an element is a unit exactly when its generated ideal is the whole
ring. See [WocjanEtAl2009]. -/
theorem source_unit_iff_span_top
    {R : Type*} [CommRing R] {r : R} :
    IsUnit r ↔ Submodule.span R ({r} : Set R) = ⊤ :=
  (Ideal.span_singleton_eq_top (x := r)).symm

/-- An ideal lies below the intersection of two ideals exactly when it lies below each one. See
[WocjanEtAl2009]. -/
theorem source_ideal_intersection
    {R : Type*} [Ring R] (I J K : Ideal R) :
    K ≤ I ⊓ J ↔ K ≤ I ∧ K ≤ J :=
  le_inf_iff

/-- The order relation on ideals is inclusion of their underlying sets. See [WocjanEtAl2009]. -/
theorem source_ideal_order
    {R : Type*} [Ring R] (I J : Ideal R) :
    I ≤ J ↔ (I : Set R) ⊆ (J : Set R) :=
  Iff.rfl

/-- The left ideal of elements `x` such that `x * y` belongs to `I` for every `y` in `J`. -/
def idealColon {R : Type*} [Ring R] (I J : Ideal R) : Ideal R where
  carrier := {x : R | ∀ y ∈ J, x * y ∈ I}
  zero_mem' := by
    intro y _
    simp
  add_mem' := by
    intro a b ha hb y hy
    rw [add_mul]
    exact I.add_mem (ha y hy) (hb y hy)
  smul_mem' := by
    intro c x hx y hy
    rw [smul_eq_mul, mul_assoc]
    exact I.mul_mem_left c (hx y hy)

/-- Membership in `idealColon I J` means that right multiplication by each element of `J` lands
in `I`. See [WocjanEtAl2009]. -/
theorem source_idealColon_membership
    {R : Type*} [Ring R] (I J : Ideal R) (x : R) :
    x ∈ idealColon I J ↔ ∀ y ∈ J, x * y ∈ I :=
  Iff.rfl

/-- An ideal lies below `idealColon I J` exactly when every product of one of its elements with
an element of `J` belongs to `I`. See [WocjanEtAl2009]. -/
theorem source_idealColon_le_iff
    {R : Type*} [Ring R] (I J K : Ideal R) :
    K ≤ idealColon I J ↔ ∀ x ∈ K, ∀ y ∈ J, x * y ∈ I :=
  Iff.rfl

/-- The left ideal of elements whose product with every element of `S` is zero. -/
def leftAnnihilator {R : Type*} [Ring R] (S : Set R) : Ideal R where
  carrier := {x : R | ∀ s ∈ S, x * s = 0}
  zero_mem' := by
    intro s _
    simp
  add_mem' := by
    intro a b ha hb s hs
    rw [add_mul, ha s hs, hb s hs, add_zero]
  smul_mem' := by
    intro c x hx s hs
    rw [smul_eq_mul, mul_assoc, hx s hs, mul_zero]

/-- An element belongs to the left annihilator of `S` exactly when it annihilates every element
of `S` by left multiplication. See [WocjanEtAl2009]. -/
theorem source_leftAnnihilator_membership
    {R : Type*} [Ring R] (S : Set R) (x : R) :
    x ∈ leftAnnihilator S ↔ ∀ s ∈ S, x * s = 0 :=
  Iff.rfl

/-- An element acting as a left multiplicative identity on every element equals one. See
[WocjanEtAl2009]. -/
theorem source_multiplicative_identity_unique
    {R : Type*} [MulOneClass R] {e : R} (h : ∀ x : R, e * x = x) : e = 1 := by
  simpa using h 1

/-- Every element of a finite additive commutative group has a positive natural multiple equal
to zero. See [WocjanEtAl2009]. -/
theorem source_additive_identity_of_order
    {A : Type*} [AddCommGroup A] [Finite A] (r : A) :
    ∃ c : ℕ, 0 < c ∧ c • r = 0 :=
  ⟨Nat.card A, Nat.card_pos, card_nsmul_eq_zero'⟩

/-- An ideal is maximal exactly when it is a coatom in the ideal lattice. See [WocjanEtAl2009]. -/
theorem source_ideal_maximal_criterion
    {R : Type*} [Ring R] (I : Ideal R) :
    I.IsMaximal ↔ IsCoatom I :=
  Ideal.isMaximal_def

/-- An element is an integer linear combination of the finite family `h` exactly when it belongs
to the additive subgroup generated by that family. See [WocjanEtAl2009]. -/
theorem source_linear_system_solvable
    {R : Type*} [Ring R] {ι : Type*} [Fintype ι] (h : ι → R) (b : R) :
    (∃ c : ι → ℤ, ∑ i, c i • h i = b) ↔
      b ∈ AddSubgroup.closure (Set.range h) := by
  constructor
  · rintro ⟨c, rfl⟩
    have hspan : ∑ i, c i • h i ∈ Submodule.span ℤ (Set.range h) :=
      (Submodule.mem_span_range_iff_exists_fun ℤ).mpr ⟨c, rfl⟩
    rwa [← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure] at hspan
  · intro hb
    have hspan : b ∈ Submodule.span ℤ (Set.range h) := by
      rw [← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure]
      exact hb
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hspan
    exact ⟨c, hc⟩

/-- A ring homomorphism is injective exactly when its kernel is the bottom ideal. See
[WocjanEtAl2009]. -/
theorem source_hom_injective_iff
    {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    Function.Injective f ↔ RingHom.ker f = ⊥ :=
  RingHom.injective_iff_ker_eq_bot f

/-- A ring homomorphism is surjective exactly when its range is the whole target ring. See
[WocjanEtAl2009]. -/
theorem source_hom_surjective_iff
    {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    Function.Surjective f ↔ RingHom.range f = ⊤ :=
  (RingHom.range_eq_top (f := f)).symm

/-- An additive equivalence with a finite product of `ZMod` groups makes the group cardinality
the product of their moduli. See [WocjanEtAl2009]. -/
theorem source_group_card_eq_prod_orders
    {A : Type*} [AddCommGroup A] [Finite A]
    {ι : Type*} [Fintype ι] (s : ι → ℕ)
    (e : A ≃+ ((i : ι) → ZMod (s i))) :
    Nat.card A = ∏ i, s i := by
  rw [Nat.card_congr e.toEquiv, Nat.card_pi]
  simp

/-- If `r ^ c = 1` for `c ≥ 1`, then `r ^ (c - 1)` is both a left and a right inverse of `r`.
See [WocjanEtAl2009]. -/
theorem source_inverse_of_pow_eq_one
    {R : Type*} [Monoid R] {r : R} {c : ℕ} (hc : 1 ≤ c) (h : r ^ c = 1) :
    r ^ (c - 1) * r = 1 ∧ r * r ^ (c - 1) = 1 := by
  constructor
  · rw [← pow_succ, Nat.sub_add_cancel hc, h]
  · rw [← pow_succ', Nat.sub_add_cancel hc, h]

/-- In a finite ring, left multiplication by `a` is surjective exactly when `a` is a unit. See
[WocjanEtAl2009]. -/
theorem source_mul_surjective_iff_unit
    {R : Type*} [Ring R] [Finite R] (a : R) :
    Function.Surjective (fun x : R => a * x) ↔ IsUnit a := by
  rw [IsUnit.isUnit_iff_mulLeft_bijective]
  exact ⟨fun hs => ⟨Finite.injective_iff_surjective.mpr hs, hs⟩, And.right⟩

/-- In a finite ring, the principal left ideal generated by a nonunit has at most half the
cardinality of the ring. [WocjanEtAl2009] -/
theorem source_nonunit_leftIdeal_half
    {R : Type*} [Ring R] [Finite R] {r : R} (hr : ¬ IsUnit r) :
    2 * Nat.card ↥(Submodule.span R ({r} : Set R)) ≤ Nat.card R := by
  have hne : Submodule.span R ({r} : Set R) ≠ ⊤ := by
    intro htop
    apply hr
    rw [source_unit_iff_left_inverse]
    have h1 : (1 : R) ∈ Submodule.span R ({r} : Set R) := by
      rw [htop]
      exact Submodule.mem_top
    obtain ⟨a, ha⟩ := (Submodule.mem_span_singleton (R := R) (x := (1 : R)) (y := r)).mp h1
    exact ⟨a, by simpa [smul_eq_mul] using ha⟩
  have hlt : (Submodule.span R ({r} : Set R)).toAddSubgroup < (⊤ : AddSubgroup R) := by
    refine lt_of_le_of_ne le_top ?_
    intro heq
    apply hne
    ext x
    have hx : x ∈ (Submodule.span R ({r} : Set R)).toAddSubgroup ↔
        x ∈ (⊤ : AddSubgroup R) := by rw [heq]
    simpa using hx
  have hdbl := strict_inclusion_doubling hlt
  have htopcard : Nat.card ↥(⊤ : AddSubgroup R) = Nat.card R :=
    Nat.card_congr
      { toFun := fun x => (x : R)
        invFun := fun x => ⟨x, AddSubgroup.mem_top x⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => rfl }
  rw [htopcard] at hdbl
  exact hdbl

end Qatlib.Papers.FiniteRing09.MainResults.IdealProblems
