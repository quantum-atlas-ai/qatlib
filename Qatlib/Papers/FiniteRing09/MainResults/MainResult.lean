/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Additive representations of finite-ring ideals

The module proves existence of a decomposition of a finite-ring ideal into nontrivial cyclic
additive factors and bounds the number of factors by the binary logarithm of its cardinality.
Products of additive generators can be expressed as integer linear combinations of the same
generators, giving the multiplication data for an additive representation.

These constructions belong to the formalization of [WocjanEtAl2009].

## Main statements

* `source_cyclic_product_decomposition`: existence of a cyclic additive decomposition.
* `source_multiplication_tensor`: integer coefficients for products of additive generators.
* `source_additive_representation_exists`: packages the decomposition and multiplication
  statements.

## References

* [Wocjan et al., 2009][WocjanEtAl2009]
-/

set_option autoImplicit false

namespace Qatlib.Papers.FiniteRing09.MainResults.MainResult

/-- Every ideal of a finite ring is additively equivalent to a finite product of `ZMod` groups
with moduli greater than one. [WocjanEtAl2009] -/
theorem source_cyclic_product_decomposition
    {R : Type*} [Ring R] [Fintype R] (I : Ideal R) :
    ∃ (ι : Type) (_ : Fintype ι) (s : ι → ℕ) (_ : ∀ i, 1 < s i),
      Nonempty (I ≃+ ((i : ι) → ZMod (s i))) := by
  haveI : Finite I := inferInstance
  obtain ⟨ι, hι, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' I
  exact ⟨ι, hι, n, hn, ⟨e.trans (DirectSum.addEquivProd (fun i => ZMod (n i)))⟩⟩

/-- A decomposition into cyclic factors of orders greater than one has at most the binary
logarithm of the group cardinality many factors. See [WocjanEtAl2009]. -/
theorem source_cyclic_factor_count_bound
    {A : Type*} [AddCommGroup A] [Finite A]
    {ι : Type*} [Fintype ι] (s : ι → ℕ) (hs : ∀ i, 1 < s i)
    (e : A ≃+ ((i : ι) → ZMod (s i))) :
    Fintype.card ι ≤ Nat.log 2 (Nat.card A) := by
  have hcard : Nat.card A = ∏ i, s i := by
    rw [Nat.card_congr e.toEquiv, Nat.card_pi]
    simp
  have h2 : 2 ^ Fintype.card ι ≤ Nat.card A := by
    rw [hcard]
    calc 2 ^ Fintype.card ι = ∏ _i : ι, 2 := by simp
      _ ≤ ∏ i, s i :=
        Finset.prod_le_prod' (fun i _ => Nat.succ_le_of_lt (hs i))
  have hA : Nat.card A ≠ 0 := Nat.card_pos.ne'
  exact (Nat.le_log_iff_pow_le (by norm_num) hA).mpr h2

/-- If `h` additively generates an ideal, every product `h i * h j` is an integer linear
combination of the generators. See [WocjanEtAl2009]. -/
theorem source_multiplication_tensor
    {R : Type*} [Ring R] (I : Ideal R)
    (ℓ : ℕ) (h : Fin ℓ → R)
    (hgen : AddSubgroup.closure (Set.range h) = I.toAddSubgroup) :
    ∀ i j : Fin ℓ, ∃ c : Fin ℓ → ℤ, ∑ k, c k • h k = h i * h j := by
  intro i j
  have hj : h j ∈ I := by
    have h1 : h j ∈ AddSubgroup.closure (Set.range h) :=
      AddSubgroup.subset_closure (Set.mem_range_self j)
    have h2 : h j ∈ I.toAddSubgroup := hgen ▸ h1
    exact h2
  have hmem : h i * h j ∈ AddSubgroup.closure (Set.range h) := by
    rw [hgen]
    exact Ideal.mul_mem_left I (h i) hj
  have hspan : h i * h j ∈ Submodule.span ℤ (Set.range h) := by
    rw [← Submodule.mem_toAddSubgroup, Submodule.span_int_eq_addSubgroupClosure]
    exact hmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hspan
  exact ⟨c, hc⟩

/-- A finite-ring ideal possesses a finite cyclic additive decomposition with nontrivial
factors, and products in any finite additive generating family have integer-coordinate
expressions. [WocjanEtAl2009] -/
theorem source_additive_representation_exists
    {R : Type*} [Ring R] [Fintype R] (I : Ideal R) :
    (∃ (ι : Type) (_ : Fintype ι) (s : ι → ℕ) (_ : ∀ i, 1 < s i),
        Nonempty (I ≃+ ((i : ι) → ZMod (s i)))) ∧
    (∀ (ℓ : ℕ) (h : Fin ℓ → R),
      AddSubgroup.closure (Set.range h) = I.toAddSubgroup →
      ∀ i j : Fin ℓ, ∃ c : Fin ℓ → ℤ, ∑ k, c k • h k = h i * h j) :=
  ⟨source_cyclic_product_decomposition I,
   fun ℓ h hgen => source_multiplication_tensor I ℓ h hgen⟩

end Qatlib.Papers.FiniteRing09.MainResults.MainResult
