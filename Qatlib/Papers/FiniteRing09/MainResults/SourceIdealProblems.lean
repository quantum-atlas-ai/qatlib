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

set_option backward.isDefEq.respectTransparency false

/-!
# FiniteRing09 — polynomial-time solutions to ideal-theoretic problems (Abstract p. 1, §4)

Source: Wocjan, Jordan, Ahmadi, Brennan, *Efficient quantum processing of ideals in finite
rings*, fixed arXiv:0908.0022v2 (5 Jul 2023), Abstract p. 1 and §4 pp. 4--7.

Abstract claim (p. 1): "As applications, we provide polynomial time solutions for a number of
problems, including: deciding the equality of two ideals, their intersection, quotient,
membership, ... deciding whether an element is a unit and computing its inverse, ... deciding
whether a system of linear equations has a solution, ... deciding whether an ideal is maximal,
computing annihilators, ... deciding the injectivity and surjectivity of ring homomorphisms."

The quantum algorithms in the paper reduce all of these to Abelian-HSP/black-box primitives; the
Lean development isolates the *mathematical reductions* that each problem relies on. All of them
are group/ideal identities over a finite ring, so they are proved here without any oracle
assumption. The one quantum-specific ingredient — the swap-test based equality test — is
captured by the purely combinatorial overlap inequality `source_ideal_equality_overlap`. The
paper displays the bound as `⟨I|J⟩ ≤ 1/2` for `I ≠ J`; read literally on the amplitudes
`⟨I|J⟩ = |I ∩ J| / sqrt(|I||J|)` this fails (e.g. in `Z/2 × Z/4` the ideals `I = Z/2 × 2Z/4`
and `J = 0 × Z/4` give `1/√2`), while the squared overlap `⟨I|J⟩² = |I ∩ J|²/(|I||J|)` is at
most `1/2`. The Lean statement is therefore the squared (probability) form actually used in the
swap-test error analysis.

Each theorem below carries the paper location it formalizes.
-/

set_option autoImplicit false

namespace Qatlib.Papers.FiniteRing09.MainResults.SourceIdealProblems

/-! ## Additive-group toolbox: strict subgroups double -/

/-- **Auxiliary (Lagrange), used for the equality/intersection tests, §4 p. 4.**

A strict inclusion `B < C` of additive subgroups of a finite additive group doubles the
cardinality: `2 |B| ≤ |C|`. This is the counting ingredient behind both the equality test of
`§4` (two distinct ideals cannot have inner-product amplitude above `1/2`) and the doubling in
the generator search (`§2`, pp. 2--3). -/
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

/-! ## Equality of ideals (§4, pp. 4--5) -/

/-- **FiniteRing09 §4 (ideal equality test), p. 4, Abstract p. 1.**

The paper's equality test computes the inner product `⟨I|J⟩ = |I ∩ J| / sqrt(|I||J|)` of the
uniform superpositions over the two ideals (via a swap test) and concludes `I = J` when it is
close to `1`. For `I ≠ J` at least one inclusion fails, and the Lagrange doubling lemma gives
`2 |I ∩ J|² ≤ |I| |J|`, i.e. the squared overlap `⟨I|J⟩²` is at most `1/2`. This is the
cardinality form used by the paper's error analysis, stated for additive subgroups of any finite
additive group (in particular for the additive groups of ideals of a finite ring).

The statement is purely combinatorial: the swap-test circuit itself is the granted
Hadamard-test primitive, only its probability bound is formalized here. -/
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

/-! ## Membership (§4, p. 5) -/

/-- **FiniteRing09 §4 (membership test), p. 4, Abstract p. 1.**

Membership `r ∈ H` is decided by testing whether the coset `r + H` equals `H`: the shift
`x ↦ r + x` is a bijection, so `r + H = H` iff `r ∈ H` (apply it to `0` to recover `r = -h`).
The quantum subroutine that compares the two superpositions is the granted swap test; the
mathematical equivalence is proved here. -/
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

/-! ## Units and inverses (§4, p. 5) -/

/-- **FiniteRing09 §4 (unit test and inverse), p. 5, Abstract p. 1.**

`r` is a unit iff multiplication by `r` is a bijection of the finite ring. This is the criterion
the paper uses to reduce "is a unit / compute its inverse" to an Abelian-HSP membership problem
(the inverse is recovered from the preimage of `1`). Proved from Mathlib's
`isUnit_iff_mulLeft_bijective`. -/
theorem source_unit_criterion
    {R : Type*} [Monoid R] {r : R} :
    IsUnit r ↔ Function.Bijective (fun x => r * x) :=
  IsUnit.isUnit_iff_mulLeft_bijective

/-- **FiniteRing09 §4 (unit iff the generated left ideal is the whole ring), pp. 4--5.**

Let `R r` be the left ideal generated by `r`, i.e. `{x r | x ∈ R}`. Then `R r = R` iff `r` has a
left inverse `x` (`x r = 1`). In a *finite* ring a left inverse is automatically two-sided
(left multiplication by `r` is injective, hence bijective on the finite ring), so this is
exactly the paper's criterion "`R r = R` if and only if `r` is a unit", used for the unit test
and (together with order finding) the inverse computation. -/
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

/-- **FiniteRing09 §4 (commutative form: unit iff the principal ideal is the whole ring), p. 5.**

In a commutative ring the criterion above takes the ideal-theoretic form
`span R {r} = ⊤ ↔ IsUnit r`: the paper checks `⟨r⟩ = R` with the ideal equality test, which by
this equivalence decides invertibility. -/
theorem source_unit_iff_span_top
    {R : Type*} [CommRing R] {r : R} :
    IsUnit r ↔ Submodule.span R ({r} : Set R) = ⊤ :=
  (Ideal.span_singleton_eq_top (x := r)).symm

/-! ## Intersection and order of ideals (§4, p. 5) -/

/-- **FiniteRing09 §4 (ideal intersection and order), p. 5, Abstract p. 1.**

The intersection `I ⊓ J` is the greatest ideal contained in both, and inclusion of ideals is
inclusion of their underlying sets. Both are the lattice identities that the paper's
intersection algorithm (`§4`) and its ideal-order test rely on. -/
theorem source_ideal_intersection
    {R : Type*} [Ring R] (I J K : Ideal R) :
    K ≤ I ⊓ J ↔ K ≤ I ∧ K ≤ J :=
  le_inf_iff

/-- **FiniteRing09 §4 (ideal order from membership), p. 5.**

`I ≤ J` is equivalent to the inclusion of the underlying subsets; this is how the paper's
black-box membership oracle for `J` decides `I ⊆ J` (and hence the order relation). -/
theorem source_ideal_order
    {R : Type*} [Ring R] (I J : Ideal R) :
    I ≤ J ↔ (I : Set R) ⊆ (J : Set R) :=
  Iff.rfl

/-! ## Quotient (colon) ideal (§4, p. 5) -/

/-- **FiniteRing09 §4 (quotient of ideals), p. 5, Abstract p. 1.**

The quotient (colon) ideal `(I : J) = {x | ∀ y ∈ J, x y ∈ I}`. For a non-commutative ring it is
only a *left* ideal (closure under left multiplication uses associativity `(c x) y = c (x y)`),
which matches the paper's systematic use of left ideals. -/
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

/-- **FiniteRing09 §4 (colon-ideal membership), p. 5.**

Membership in the quotient ideal is the pointwise product condition used in the paper's
quotient computation: `x ∈ (I : J) ↔ ∀ y ∈ J, x y ∈ I`. -/
theorem source_idealColon_membership
    {R : Type*} [Ring R] (I J : Ideal R) (x : R) :
    x ∈ idealColon I J ↔ ∀ y ∈ J, x * y ∈ I :=
  Iff.rfl

/-- **FiniteRing09 §4 (colon-ideal universal property), p. 5.**

`K ≤ (I : J)` iff all products `x y` with `x ∈ K`, `y ∈ J` lie in `I`. This is the reduction
used by the paper to test quotient containment with the membership oracle. -/
theorem source_idealColon_le_iff
    {R : Type*} [Ring R] (I J K : Ideal R) :
    K ≤ idealColon I J ↔ ∀ x ∈ K, ∀ y ∈ J, x * y ∈ I :=
  Iff.rfl

/-! ## Annihilators (§4, p. 5) -/

/-- **FiniteRing09 §4 (left annihilator), p. 5, Abstract p. 1.**

The left annihilator `Ann(S) = {x | ∀ s ∈ S, x s = 0}` of a set `S`. It is a left ideal
(closure under left multiplication: `(c x) s = c (x s) = 0`). The paper computes annihilators
as kernels of multiplication maps, i.e. as this ideal. -/
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

/-- **FiniteRing09 §4 (annihilator membership), p. 5.**

`x` annihilates `S` iff `x s = 0` for every `s ∈ S`. -/
theorem source_leftAnnihilator_membership
    {R : Type*} [Ring R] (S : Set R) (x : R) :
    x ∈ leftAnnihilator S ↔ ∀ s ∈ S, x * s = 0 :=
  Iff.rfl

/-! ## Identities (§4, p. 6) -/

/-- **FiniteRing09 §4 (multiplicative identity), p. 6, Abstract p. 1.**

The paper finds the multiplicative identity of the ring by solving a system of linear modular
equations in the invariant-factor basis (its result then is the unique element acting as a
two-sided identity). Formally: any element acting as a left identity is `1`. -/
theorem source_multiplicative_identity_unique
    {R : Type*} [MulOneClass R] {e : R} (h : ∀ x : R, e * x = x) : e = 1 := by
  simpa using h 1

/-- **FiniteRing09 §4 (additive identity), p. 6, Abstract p. 1.**

The paper obtains the additive identity of a black-box ring by order finding: for any `r` the
additive order `c` satisfies `c • r = 0`, and `c • r` is the additive identity. Formally, in a
finite additive group every element has finite additive order, and `Nat.card A • r = 0`. -/
theorem source_additive_identity_of_order
    {A : Type*} [AddCommGroup A] [Finite A] (r : A) :
    ∃ c : ℕ, 0 < c ∧ c • r = 0 :=
  ⟨Nat.card A, Nat.card_pos, card_nsmul_eq_zero'⟩

/-! ## Maximality (§4, p. 7) -/

/-- **FiniteRing09 §4 (maximality test), p. 7, Abstract p. 1.**

An ideal is maximal iff it is a coatom of the ideal lattice: proper, and contained in no other
proper ideal. This is the lattice-theoretic content of the paper's maximality test (once
`I` is known to be proper, it suffices to check that no strictly larger proper ideal exists). -/
theorem source_ideal_maximal_criterion
    {R : Type*} [Ring R] (I : Ideal R) :
    I.IsMaximal ↔ IsCoatom I :=
  Ideal.isMaximal_def

/-! ## Systems of linear equations (§4, p. 5) -/

/-- **FiniteRing09 §4 (linear systems), p. 6, Abstract p. 1.**

A system `Σᵢ cᵢ hᵢ = b` with integer coefficients is solvable iff `b` lies in the additive
subgroup generated by the `hᵢ`. This is exactly the linear-system problem of the paper: the
generators are the columns of the system, and the additive subgroup is what the quantum
additive-basis algorithm represents (see `SourceMainResult`). -/
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

/-! ## Ring homomorphisms (§4, p. 5) -/

/-- **FiniteRing09 §4 (injectivity of ring homomorphisms), p. 5, Abstract p. 1.**

A ring homomorphism is injective iff its kernel ideal is trivial. The paper decides injectivity
by testing whether the kernel (an ideal, hence representable by the additive-basis algorithm)
is the zero ideal. -/
theorem source_hom_injective_iff
    {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    Function.Injective f ↔ RingHom.ker f = ⊥ :=
  RingHom.injective_iff_ker_eq_bot f

/-- **FiniteRing09 §4 (surjectivity of ring homomorphisms), p. 5, Abstract p. 1.**

A ring homomorphism is surjective iff the subring it generates is the whole codomain. The paper
decides surjectivity by checking whether the image subring equals the top subring, using the
black-box membership test for the codomain. -/
theorem source_hom_surjective_iff
    {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    Function.Surjective f ↔ RingHom.range f = ⊤ :=
  (RingHom.range_eq_top (f := f)).symm

/-! ## Cardinality of the represented additive group (§4, p. 5) -/

/-- **FiniteRing09 §4 (size of the additive basis), p. 5.**

If the additive group of an ideal is represented by invariant-factor generators with orders
`sᵢ` (an additive isomorphism onto `∏ᵢ ZMod (sᵢ)`), then `|A| = ∏ᵢ sᵢ`. The paper uses this to
convert the invariant-factor description into the quantity `|I|` needed by the overlap and
doubling arguments. -/
theorem source_group_card_eq_prod_orders
    {A : Type*} [AddCommGroup A] [Finite A]
    {ι : Type*} [Fintype ι] (s : ι → ℕ)
    (e : A ≃+ ((i : ι) → ZMod (s i))) :
    Nat.card A = ∏ i, s i := by
  rw [Nat.card_congr e.toEquiv, Nat.card_pi]
  simp

end Qatlib.Papers.FiniteRing09.MainResults.SourceIdealProblems
