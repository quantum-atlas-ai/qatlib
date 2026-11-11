/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GaussSumEst02.RingEstimate.PrimitiveEigenphase
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Group.Prod

/-!
# Unit groups and Dirichlet-character conductors

This module records unit-group and conductor facts used for the composite-modulus Gauss-sum
algorithms of [VanDamSeroussi2002]. `crtUnits` factors the unit group of coprime moduli, and the
cardinality and cyclicity results describe prime-power unit groups and the moduli with cyclic
unit group.

The conductor results characterize primitive Dirichlet characters, recover a character from its
primitive representative, and bound the conductor of a product by a least common multiple.

## Main statements

* `crtUnits`: The Chinese-remainder equivalence of unit groups.
* `units_cyclic_iff`: Classification of moduli with cyclic unit group.
* `isPrimitive_iff_conductor`: Primitivity characterized by equality of conductor and level.
* `conductor_mul_dvd_lcm_conductor`: Divisibility bound for product conductors.

## References

* [van Dam and Seroussi, 2002][VanDamSeroussi2002]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GaussSumEst02.DirichletPhase

open Qatlib.Papers.GaussSumEst02.MainResults.Source

/-- The multiplicative equivalence from units modulo a product of coprime moduli to the product
of their unit groups. See [VanDamSeroussi2002]. -/
def crtUnits (m n : ℕ) (h : m.Coprime n) :
    (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

/-- For coprime nonzero moduli, the number of units modulo their product is the product of their
unit-group cardinalities. See [VanDamSeroussi2002]. -/
theorem crtUnits_card (m n : ℕ) (h : m.Coprime n) [NeZero m] [NeZero n] [NeZero (m * n)] :
    Fintype.card (ZMod (m * n))ˣ
      = Fintype.card (ZMod m)ˣ * Fintype.card (ZMod n)ˣ := by
  rw [Fintype.card_congr (crtUnits m n h).toEquiv, Fintype.card_prod]

/-- For nonzero `n`, the number of units modulo `n` equals Euler’s totient of `n`. See
[VanDamSeroussi2002]. -/
theorem card_units_eq_totient (n : ℕ) [NeZero n] :
    Fintype.card (ZMod n)ˣ = Nat.totient n :=
  ZMod.card_units_eq_totient n

/-- The unit group modulo any natural power of an odd prime is cyclic. See [VanDamSeroussi2002]. -/
theorem units_prime_pow_cyclic (p r : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    IsCyclic (ZMod (p ^ r))ˣ :=
  ZMod.isCyclic_units_of_prime_pow p hp hp2 r

/-- The unit group modulo `2 ^ r` is cyclic exactly when `r ≤ 2`. See [VanDamSeroussi2002]. -/
theorem units_two_pow_cyclic_iff (r : ℕ) : IsCyclic (ZMod (2 ^ r))ˣ ↔ r ≤ 2 :=
  ZMod.isCyclic_units_two_pow_iff r

/-- The unit group modulo `n` is cyclic exactly for `n = 0, 1, 2, 4`, an odd prime power with
positive exponent, or twice such a prime power. See [VanDamSeroussi2002]. -/
theorem units_cyclic_iff (n : ℕ) :
    IsCyclic (ZMod n)ˣ ↔
      n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 4 ∨
        ∃ (p m : ℕ), p.Prime ∧ Odd p ∧ 1 ≤ m ∧ (n = p ^ m ∨ n = 2 * p ^ m) :=
  ZMod.isCyclic_units_iff n

/-- For prime `p` and positive `r`, the unit group modulo `p ^ r` has cardinality `p ^ (r - 1) *
(p - 1)`. See [VanDamSeroussi2002]. -/
theorem card_units_prime_pow (p r : ℕ) (hp : p.Prime) (hr : 0 < r) [NeZero (p ^ r)] :
    Fintype.card (ZMod (p ^ r))ˣ = p ^ (r - 1) * (p - 1) := by
  rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow hp hr]

/-- For positive `r`, the unit group modulo `2 ^ r` has cardinality `2 ^ (r - 1)`. -/
theorem card_units_two_pow (r : ℕ) (hr : 0 < r) [NeZero (2 ^ r)] :
    Fintype.card (ZMod (2 ^ r))ˣ = 2 ^ (r - 1) := by
  simpa using card_units_prime_pow 2 r Nat.prime_two hr

/-- For `n ≥ 2`, the unit group modulo `n` is cyclic exactly when `n` is two, four, an odd prime
power with positive exponent, or twice such a power. -/
theorem units_cyclic_iff_prime_pow_form {n : ℕ} (hn : 2 ≤ n) :
    IsCyclic (ZMod n)ˣ ↔
      n = 2 ∨ n = 4 ∨
        ∃ (p m : ℕ), p.Prime ∧ Odd p ∧ 1 ≤ m ∧ (n = p ^ m ∨ n = 2 * p ^ m) := by
  rw [units_cyclic_iff]
  constructor
  · rintro (h | h | h | h | h)
    · omega
    · omega
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

section Conductor

variable {n : ℕ}

/-- The conductor of a complex Dirichlet character divides its level. See [VanDamSeroussi2002]. -/
theorem conductor_dvd_level (χ : DirichletCharacter ℂ n) : χ.conductor ∣ n :=
  χ.conductor_dvd_level

/-- Every complex Dirichlet character factors through its conductor. -/
theorem factorsThrough_conductor (χ : DirichletCharacter ℂ n) :
    χ.FactorsThrough χ.conductor :=
  χ.factorsThrough_conductor

/-- A complex Dirichlet character is primitive exactly when its conductor equals its level. See
[VanDamSeroussi2002]. -/
theorem isPrimitive_iff_conductor (χ : DirichletCharacter ℂ n) :
    χ.IsPrimitive ↔ χ.conductor = n :=
  χ.isPrimitive_def

/-- The primitive character associated with a Dirichlet character is primitive. -/
theorem primitiveCharacter_isPrimitive (χ : DirichletCharacter ℂ n) :
    χ.primitiveCharacter.IsPrimitive :=
  χ.primitiveCharacter_isPrimitive

/-- Changing the level of the associated primitive character back to the original level recovers
the original character. -/
theorem changeLevel_primitiveCharacter (χ : DirichletCharacter ℂ n) :
    χ.primitiveCharacter.changeLevel χ.conductor_dvd_level = χ :=
  χ.changeLevel_primitiveCharacter

/-- At a nonzero level, the principal Dirichlet character has conductor one. See
[VanDamSeroussi2002]. -/
theorem conductor_one [NeZero n] : (1 : DirichletCharacter ℂ n).conductor = 1 :=
  DirichletCharacter.conductor_one

/-- The conductor of the product of two Dirichlet characters divides the least common multiple
of their conductors. See [VanDamSeroussi2002]. -/
theorem conductor_mul_dvd_lcm_conductor (χ ψ : DirichletCharacter ℂ n) :
    (χ * ψ).conductor ∣ Nat.lcm χ.conductor ψ.conductor :=
  DirichletCharacter.conductor_mul_dvd_lcm_conductor χ ψ

end Conductor

end Qatlib.Papers.GaussSumEst02.DirichletPhase
