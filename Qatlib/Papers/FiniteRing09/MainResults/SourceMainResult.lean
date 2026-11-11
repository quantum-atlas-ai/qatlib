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

set_option backward.isDefEq.respectTransparency false

/-!
# FiniteRing09 — main result: additive basis (invariant-factor) representation of an ideal

Source: Wocjan, Jordan, Ahmadi, Brennan, *Efficient quantum processing of ideals in finite
rings*, fixed arXiv:0908.0022v2 (5 Jul 2023), Abstract p. 1 and §2--§3 pp. 2--4.

Abstract claim (p. 1): "Suppose we are given black-box access to a finite ring `R` … and a list of
generators for an ideal `I` in `R`. We show how to find an additive basis representation for `I`
in `poly(log |R|)` quantum time." §3 defines a *basis representation* of `I` as the invariant
factor (i.f.) generators `h₁, …, h_ℓ` of `(I, +)`, their additive orders `s₁, …, s_ℓ`, and the
multiplication tensor `Mᵢⱼₖ` with `hᵢ hⱼ = Σₖ Mᵢⱼₖ hₖ`.

The Lean development separates the two mathematical assertions:

1. `source_main_result_invariant_factor_basis` — the additive group of any finite left ideal is
   isomorphic to a finite product `∏ᵢ ZMod (sᵢ)` with `sᵢ > 1` (the i.f. decomposition). This is
   Mathlib's structure theorem `AddCommGroup.equiv_directSum_zmod_of_finite'`.
2. `source_multiplication_tensor` — for any additive generating family `h` of `I`, every product
   `hᵢ * hⱼ` is an integer combination of the generators, giving the paper's multiplication
   tensor.
3. `source_invariant_factor_rank_bound` — the number of i.f. generators is at most `log₂ |I|`.

The quantum cost of producing this representation (`poly(log|R|)` calls to arithmetic black boxes
plus Abelian-HSP subroutines) is recorded in the sibling file `SourceIterationCost` (the
combinatorial iteration/query bound) and relies on the granted primitives of [CM01, Wat01];
no Dev/Frozen statement of those subroutines exists, so no further bridging is claimed here.
-/

set_option autoImplicit false

namespace Qatlib.Papers.FiniteRing09.MainResults.SourceMainResult

/-- **FiniteRing09 main result (additive basis / invariant-factor decomposition), p. 1 and
§3 pp. 3--4.**

For a finite left ideal `I` of a finite ring `R`, there are an index type `ι`, orders
`s : ι → ℕ` with `s i > 1`, and an additive isomorphism from `(I, +)` onto `∏ᵢ ZMod (sᵢ)`.
This is the mathematical content of the paper's "additive basis representation": the i.f.
generators are the preimages of the standard basis vectors of the product, and the `sᵢ` are
their additive orders.

Proved from Mathlib's structure theorem for finite abelian groups; the theory-specific content
is the identification of `(I, +)` with a finite abelian group and the left-ideal structure of
`I` inside the (not necessarily commutative) ring. -/
theorem source_main_result_invariant_factor_basis
    {R : Type*} [Ring R] [Fintype R] (I : Ideal R) :
    ∃ (ι : Type) (_ : Fintype ι) (s : ι → ℕ) (_ : ∀ i, 1 < s i),
      Nonempty (I ≃+ ((i : ι) → ZMod (s i))) := by
  haveI : Finite I := inferInstance
  obtain ⟨ι, hι, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' I
  exact ⟨ι, hι, n, hn, ⟨e.trans (DirectSum.addEquivProd (fun i => ZMod (n i)))⟩⟩

/-- **FiniteRing09, number of invariant factors (pp. 1--4).**

If `A ≃+ ∏ᵢ ZMod (sᵢ)` with `sᵢ > 1`, then the number of cyclic factors is at most
`log₂ |A|`: indeed `2^ℓ ≤ ∏ᵢ sᵢ = |A|`. For `A = (I, +)` this is the paper's count of
additive generators produced by the algorithm, at most `log₂ |I| ≤ log₂ |R|`. -/
theorem source_invariant_factor_rank_bound
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

/-- **FiniteRing09, multiplication tensor (§3, pp. 3--4).**

Let `h : Fin ℓ → R` be an additive generating family of the left ideal `I`
(`AddSubgroup.closure (range h) = (I, +)`). Then for every pair `i, j` there is an integer
coefficient vector `c` with `hᵢ * hⱼ = Σₖ cₖ • hₖ`. These coefficients are the paper's
multiplication tensor `Mᵢⱼₖ`; they exist because the product lies in `I` and the `hₖ`
additively generate `I`. -/
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

/-- **FiniteRing09 main result (aggregate form), Abstract p. 1 and §3 pp. 3--4.**

A finite left ideal `I` of a finite ring admits an additive basis (invariant-factor)
representation (first conjunct) and, with respect to any additive generating family, its
multiplication is described by an integer multiplication tensor (second conjunct). The
`poly(log |R|)` quantum cost of computing the representation is formalized in
`SourceIterationCost` (iteration and query counts) and rests on the granted Abelian-HSP
subroutines of [CM01, Wat01]. -/
theorem source_main_result
    {R : Type*} [Ring R] [Fintype R] (I : Ideal R) :
    (∃ (ι : Type) (_ : Fintype ι) (s : ι → ℕ) (_ : ∀ i, 1 < s i),
        Nonempty (I ≃+ ((i : ι) → ZMod (s i)))) ∧
    (∀ (ℓ : ℕ) (h : Fin ℓ → R),
      AddSubgroup.closure (Set.range h) = I.toAddSubgroup →
      ∀ i j : Fin ℓ, ∃ c : Fin ℓ → ℤ, ∑ k, c k • h k = h i * h j) :=
  ⟨source_main_result_invariant_factor_basis I,
   fun ℓ h hgen => source_multiplication_tensor I ℓ h hgen⟩

end Qatlib.Papers.FiniteRing09.MainResults.SourceMainResult
