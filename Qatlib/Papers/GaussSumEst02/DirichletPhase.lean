/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GaussSumEst02.RingEstimate.PrimitiveEigenphase
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Group.Prod
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GaussSumEst02.DirichletPhase

open Qatlib.Papers.GaussSumEst02.MainResults.Source

def crtUnits (m n : ℕ) (h : m.Coprime n) :
    (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits

theorem crtUnits_card (m n : ℕ) (h : m.Coprime n) [NeZero m] [NeZero n] [NeZero (m * n)] :
    Fintype.card (ZMod (m * n))ˣ
      = Fintype.card (ZMod m)ˣ * Fintype.card (ZMod n)ˣ := by
  rw [Fintype.card_congr (crtUnits m n h).toEquiv, Fintype.card_prod]

theorem card_units_eq_totient (n : ℕ) [NeZero n] :
    Fintype.card (ZMod n)ˣ = Nat.totient n :=
  ZMod.card_units_eq_totient n

theorem units_prime_pow_cyclic (p r : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    IsCyclic (ZMod (p ^ r))ˣ :=
  ZMod.isCyclic_units_of_prime_pow p hp hp2 r

theorem units_two_pow_cyclic_iff (r : ℕ) : IsCyclic (ZMod (2 ^ r))ˣ ↔ r ≤ 2 :=
  ZMod.isCyclic_units_two_pow_iff r

theorem units_cyclic_iff (n : ℕ) :
    IsCyclic (ZMod n)ˣ ↔
      n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 4 ∨
        ∃ (p m : ℕ), p.Prime ∧ Odd p ∧ 1 ≤ m ∧ (n = p ^ m ∨ n = 2 * p ^ m) :=
  ZMod.isCyclic_units_iff n

theorem card_units_prime_pow (p r : ℕ) (hp : p.Prime) (hr : 0 < r) [NeZero (p ^ r)] :
    Fintype.card (ZMod (p ^ r))ˣ = p ^ (r - 1) * (p - 1) := by
  rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow hp hr]

theorem card_units_two_pow (r : ℕ) (hr : 0 < r) [NeZero (2 ^ r)] :
    Fintype.card (ZMod (2 ^ r))ˣ = 2 ^ (r - 1) := by
  simpa using card_units_prime_pow 2 r Nat.prime_two hr

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

theorem conductor_dvd_level (χ : DirichletCharacter ℂ n) : χ.conductor ∣ n :=
  χ.conductor_dvd_level

theorem factorsThrough_conductor (χ : DirichletCharacter ℂ n) :
    χ.FactorsThrough χ.conductor :=
  χ.factorsThrough_conductor

theorem isPrimitive_iff_conductor (χ : DirichletCharacter ℂ n) :
    χ.IsPrimitive ↔ χ.conductor = n :=
  χ.isPrimitive_def

theorem primitiveCharacter_isPrimitive (χ : DirichletCharacter ℂ n) :
    χ.primitiveCharacter.IsPrimitive :=
  χ.primitiveCharacter_isPrimitive

theorem changeLevel_primitiveCharacter (χ : DirichletCharacter ℂ n) :
    χ.primitiveCharacter.changeLevel χ.conductor_dvd_level = χ :=
  χ.changeLevel_primitiveCharacter

theorem conductor_one [NeZero n] : (1 : DirichletCharacter ℂ n).conductor = 1 :=
  DirichletCharacter.conductor_one

theorem conductor_mul_dvd_lcm_conductor (χ ψ : DirichletCharacter ℂ n) :
    (χ * ψ).conductor ∣ Nat.lcm χ.conductor ψ.conductor :=
  DirichletCharacter.conductor_mul_dvd_lcm_conductor χ ψ

end Conductor

end Qatlib.Papers.GaussSumEst02.DirichletPhase
