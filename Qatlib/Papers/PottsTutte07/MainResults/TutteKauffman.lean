/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PottsTutte07.MainResults.Definitions

/-!
# Tutte–Kauffman normalization identities

The loop-count relation identifies the Kauffman state sum with the Tutte subset sum after
scaling by a power of d and substituting q = d². The scalar form of `psiOp` is also transported
through arbitrary complex algebra homomorphisms [AharonovEtAl2007].

## Main statements

* `claim3_1_kauffman_tutte`: The loop-count relation gives the scaled Tutte–Kauffman identity.
* `claim4_1`: An algebra homomorphism sends the operator sum to the same bracket scalar times
  the identity.

## References

* [Aharonov et al., 2007][AharonovEtAl2007]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PottsTutte07.MainResults

open scoped BigOperators

/-- Under the loop-count and exponent bounds, `d ^ card V` times the Kauffman bracket equals the
Tutte sum at `q = d ^ 2` and edge weights `d * u e` [AharonovEtAl2007]. -/
theorem claim3_1_kauffman_tutte
    {V E : Type*} [Fintype V] [Fintype E]
    (k : Finset E → ℕ) (loops : Finset E → ℕ)
    (hloop : ∀ A : Finset E, loops A = 2 * k A + A.card - Fintype.card V)
    (hbound : ∀ A : Finset E, Fintype.card V ≤ 2 * k A + A.card)
    (d : ℂ) (u : E → ℂ) :
    d ^ (Fintype.card V) * kauffmanBracket loops d u
      = tuttePoly k (d ^ 2) (fun e => d * u e) := by
  rw [kauffmanBracket, tuttePoly, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro A _
  have hb : Fintype.card V ≤ 2 * k A + A.card := hbound A
  have hexp : Fintype.card V + loops A = 2 * k A + A.card := by
    rw [hloop A]; omega
  rw [kauffmanTerm, Finset.prod_mul_distrib, Finset.prod_const, ← pow_mul d 2 (k A)]
  rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add, hexp]

/-- The operator sum `psiOp` equals the Kauffman bracket times the identity [AharonovEtAl2007]. -/
theorem prop4_1 {E : Type*} [Fintype E]
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (loops : Finset E → ℕ) (d : ℂ) (u : E → ℂ) :
    psiOp (A := A) loops d u = kauffmanBracket loops d u • (1 : A) :=
  psiOp_eq_scalar_mul_one loops d u

/-- A complex algebra homomorphism sends `psiOp` to the Kauffman bracket times the identity of
the target algebra [AharonovEtAl2007]. -/
theorem claim4_1 {E : Type*} [Fintype E]
    {A B : Type*} [CommRing A] [Algebra ℂ A] [CommRing B] [Algebra ℂ B]
    (ρ : A →ₐ[ℂ] B) (loops : Finset E → ℕ) (d : ℂ) (u : E → ℂ) :
    ρ (psiOp (A := A) loops d u) = kauffmanBracket loops d u • (1 : B) := by
  rw [prop4_1, map_smul, map_one]

end Qatlib.Papers.PottsTutte07.MainResults
