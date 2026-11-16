/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.MonoidAlgebra.Defs
public import Mathlib.Algebra.CharP.Lemmas

@[expose] public section


/-! # Characteristic and torsion monomials in group algebras

The characteristic lift is supplied as a theorem, so importing
this module does not change global instance search. The nilpotency conclusion
is the algebraic input to Olson's finite-field zero-sum argument; it does not
provide a search algorithm.
-/

set_option autoImplicit false

namespace Qatlib.Foundations.FiniteGroupAlg.CharP

/-- The characteristic of a commutative coefficient ring lifts to its monoid algebra. -/
theorem charP_monoidAlgebra {R M : Type*} [CommRing R] [Monoid M] {p : ℕ}
    [CharP R p] : CharP (MonoidAlgebra R M) p where
  cast_eq_zero_iff n := by
    rw [MonoidAlgebra.natCast_def, MonoidAlgebra.single_eq_zero, CharP.cast_eq_zero_iff]

/-- The characteristic of a commutative coefficient ring lifts to its additive monoid algebra. -/
theorem charP_addMonoidAlgebra {R G : Type*} [CommRing R] [AddCommMonoid G] {p : ℕ}
    [CharP R p] : CharP (AddMonoidAlgebra R G) p where
  cast_eq_zero_iff n := by
    rw [AddMonoidAlgebra.natCast_def, AddMonoidAlgebra.single_eq_zero,
      CharP.cast_eq_zero_iff]

/-- The basis monomial at zero is the unit of the additive monoid algebra. -/
theorem of'_zero {R G : Type*} [CommSemiring R] [AddCommMonoid G] :
    AddMonoidAlgebra.of' R G (0 : G) = (1 : AddMonoidAlgebra R G) := by
  simp [AddMonoidAlgebra.one_def]

/-- A natural power of a basis monomial is the monomial of the corresponding multiple. -/
theorem of'_pow {R G : Type*} [CommSemiring R] [AddCommMonoid G] (g : G) (n : ℕ) :
    (AddMonoidAlgebra.of' R G g) ^ n = AddMonoidAlgebra.of' R G (n • g) := by
  induction n with
  | zero => rw [pow_zero, zero_smul, of'_zero]
  | succ n ih =>
    rw [pow_succ, ih, succ_nsmul]
    simp [AddMonoidAlgebra.of'_apply]

/-- In prime characteristic, a monomial of additive order dividing `p` minus one is `p`-nilpotent. -/
theorem of'_sub_one_pow_eq_zero {R G : Type*} [CommRing R] [AddCommGroup G] {p : ℕ}
    [Fact (Nat.Prime p)] [CharP R p] (g : G) (hg : p • g = 0) :
    (AddMonoidAlgebra.of' R G g - 1) ^ p = (0 : AddMonoidAlgebra R G) := by
  have : CharP (AddMonoidAlgebra R G) p := charP_addMonoidAlgebra
  rw [sub_pow_char, one_pow, of'_pow, hg, of'_zero, sub_self]

end Qatlib.Foundations.FiniteGroupAlg.CharP
