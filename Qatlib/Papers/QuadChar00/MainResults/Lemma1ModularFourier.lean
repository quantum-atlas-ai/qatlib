/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuadChar00.MainResults.Lemma4JacobiSum

/-!
# Jacobi Fourier amplitudes at zero and unit frequencies

This module proves the shifted Jacobi Fourier identity at zero frequency and at unit
frequencies. The unit-frequency argument uses multiplication by a unit to reindex the sum and
the fact that the Jacobi character is unchanged by inversion of that unit.

The result `lemma1_amplitude_unit_or_zero` combines these two cases of the unnormalized
amplitude formula in Lemma 1 of [VanDamHallgren2000]. The zero-frequency theorem also handles
the modulus-one case directly, while the unit-frequency reindexing argument applies to every
nonzero modulus under its stated interface.

## Main statements

* `jacobiCharZMod_unit_eq_one_or_neg_one`: Jacobi values on units are signs.
* `jacobiCharZMod_unit_inv_eq`: inversion preserves a unit's Jacobi value.
* `lemma1_amplitude_zero`: the shifted Fourier identity at frequency zero.
* `lemma1_amplitude_unit_or_zero`: the identity at either a unit or zero frequency.

## References

* [van Dam and Hallgren, 2000][VanDamHallgren2000]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadChar00.MainResults

open scoped BigOperators

/-- The Jacobi character of the residue one equals one for every modulus. -/
lemma jacobiCharZMod_one (n : ℕ) : jacobiCharZMod n (1 : ZMod n) = 1 := by
  rw [show (1 : ZMod n) = ((1 : ℕ) : ZMod n) from by push_cast; rfl,
    jacobiCharZMod_natCast]
  exact jacobiSym.one_left n

/-- For a nonzero modulus, the Jacobi character of a unit is either one or minus one. -/
lemma jacobiCharZMod_unit_eq_one_or_neg_one (n : ℕ) [NeZero n] (y : (ZMod n)ˣ) :
    jacobiCharZMod n (y : ZMod n) = 1 ∨ jacobiCharZMod n (y : ZMod n) = -1 := by
  have hu : IsUnit (((((y : ZMod n)).val : ℕ)) : ZMod n) := by
    rw [ZMod.natCast_zmod_val]
    exact y.isUnit
  have hcop : Nat.Coprime (((y : ZMod n)).val) n :=
    (ZMod.isUnit_iff_coprime (((y : ZMod n)).val) n).mp hu
  have hgcd : ((((y : ZMod n)).val : ℕ) : ℤ).gcd (n : ℤ) = 1 := by
    rw [Int.gcd_def, Int.natAbs_natCast, Int.natAbs_natCast]
    exact Nat.coprime_iff_gcd_eq_one.mp hcop
  have h := jacobiSym.eq_one_or_neg_one hgcd
  rwa [← jacobiCharZMod_natCast, ZMod.natCast_zmod_val] at h

/-- For a nonzero modulus, a unit and its inverse have the same Jacobi-character value. -/
lemma jacobiCharZMod_unit_inv_eq (n : ℕ) [NeZero n] (y : (ZMod n)ˣ) :
    jacobiCharZMod n ((y⁻¹ : (ZMod n)ˣ) : ZMod n) = jacobiCharZMod n (y : ZMod n) := by
  have hprod : jacobiCharZMod n (y : ZMod n) * jacobiCharZMod n ((y⁻¹ : (ZMod n)ˣ) : ZMod n) = 1 := by
    rw [← jacobiCharZMod_mul]
    have hyy : (y : ZMod n) * ((y⁻¹ : (ZMod n)ˣ) : ZMod n) = 1 := by
      rw [Units.mul_inv]
    rw [hyy, jacobiCharZMod_one]
  rcases jacobiCharZMod_unit_eq_one_or_neg_one n y with h | h <;> rw [h] at hprod ⊢
  · rw [one_mul] at hprod; exact hprod
  · omega

/-- For odd squarefree nonzero modulus, the shifted Jacobi Fourier sum at frequency zero equals
the Gauss sum times the zero-frequency phase and Jacobi factors. This zero-frequency case of
Lemma 1 of [VanDamHallgren2000] includes modulus one. -/
theorem lemma1_amplitude_zero (n : ℕ) [NeZero n] (hn : Odd n) (hsq : Squarefree n)
    (s : ZMod n) :
    ∑ x : ZMod n, ((jacobiCharZMod n (x + s) : ℤ) : ℂ) * ZMod.stdAddChar (x * (0 : ZMod n))
      = jacobiGaussSum n * ZMod.stdAddChar (-(s * (0 : ZMod n))) *
          ((jacobiCharZMod n (0 : ZMod n) : ℤ) : ℂ) := by
  classical
  rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)) with h1 | h1
  · subst h1
    have hconst : ∀ u : ZMod 1, ((jacobiCharZMod 1 u : ℤ) : ℂ) = ((jacobiCharZMod 1 0 : ℤ) : ℂ) :=
      fun u => by rw [Subsingleton.elim u 0]
    have hJ0 : jacobiCharZMod 1 (0 : ZMod 1) = 1 := by
      unfold jacobiCharZMod
      rw [ZMod.val_zero]
      exact jacobiSym.one_right 0
    have hψ : ∀ z : ZMod 1, ZMod.stdAddChar z = 1 := fun z => by
      rw [Subsingleton.elim z 0, AddChar.map_zero_eq_one]
    rw [jacobiGaussSum]
    simp only [hconst, hψ, hJ0, Int.cast_one]
    rw [Finset.sum_const, Finset.card_univ, ZMod.card]
    simp
  · have hJ0 : jacobiCharZMod n (0 : ZMod n) = 0 := lemma4_jacobiChar_zero n h1
    have hsum : (∑ x : ZMod n, ((jacobiCharZMod n (x + s) : ℤ) : ℂ)) = 0 := by
      have hbij : Function.Bijective (fun u : ZMod n => u + s) :=
        (Equiv.addRight s).bijective
      have hreindex :
          (∑ x : ZMod n, ((jacobiCharZMod n (x + s) : ℤ) : ℂ))
            = ∑ u : ZMod n, ((jacobiCharZMod n u : ℤ) : ℂ) :=
        Fintype.sum_bijective (fun u : ZMod n => u + s) hbij
          (fun x => ((jacobiCharZMod n (x + s) : ℤ) : ℂ))
          (fun u => ((jacobiCharZMod n u : ℤ) : ℂ)) (fun _ => rfl)
      rw [hreindex, ← Int.cast_sum, lemma4_jacobiSum n hn hsq h1]
      simp
    rw [show (∑ x : ZMod n, ((jacobiCharZMod n (x + s) : ℤ) : ℂ) *
          ZMod.stdAddChar (x * (0 : ZMod n)))
        = ∑ x : ZMod n, ((jacobiCharZMod n (x + s) : ℤ) : ℂ) from by
      apply Finset.sum_congr rfl
      intro x _
      rw [mul_zero, AddChar.map_zero_eq_one, mul_one]]
    rw [hsum, hJ0]
    simp

/-- At a unit frequency, the shifted Jacobi Fourier sum equals `jacobiGaussSum n` times the
shift phase at `-(s * y)` and the Jacobi value at `y`. This unit-frequency case of Lemma 1
of [VanDamHallgren2000] is proved by translation and multiplicative reindexing. -/
theorem lemma1_amplitude_unit (n : ℕ) [NeZero n] (_hn : Odd n) (_hsq : Squarefree n)
    (s y : ZMod n) (hy : IsUnit y) :
    ∑ x : ZMod n, ((jacobiCharZMod n (x + s) : ℤ) : ℂ) * ZMod.stdAddChar (x * y)
      = jacobiGaussSum n * ZMod.stdAddChar (-(s * y)) * ((jacobiCharZMod n y : ℤ) : ℂ) := by
  classical
  obtain ⟨yu, rfl⟩ := hy

  have hshift :
      (∑ x : ZMod n, ((jacobiCharZMod n (x + s) : ℤ) : ℂ) * ZMod.stdAddChar (x * (yu : ZMod n)))
      = ZMod.stdAddChar (-(s * (yu : ZMod n))) *
          ∑ u : ZMod n, ((jacobiCharZMod n u : ℤ) : ℂ) * ZMod.stdAddChar (u * (yu : ZMod n)) := by
    rw [Finset.mul_sum]
    refine Fintype.sum_bijective (fun u : ZMod n => u + s) (Equiv.addRight s).bijective
      (fun x => ((jacobiCharZMod n (x + s) : ℤ) : ℂ) * ZMod.stdAddChar (x * (yu : ZMod n)))
      (fun u => ZMod.stdAddChar (-(s * (yu : ZMod n))) *
        (((jacobiCharZMod n u : ℤ) : ℂ) * ZMod.stdAddChar (u * (yu : ZMod n)))) ?_
    intro u
    change ((jacobiCharZMod n (u + s) : ℤ) : ℂ) * ZMod.stdAddChar (u * (yu : ZMod n))
        = ZMod.stdAddChar (-(s * (yu : ZMod n))) *
            (((jacobiCharZMod n (u + s) : ℤ) : ℂ) * ZMod.stdAddChar ((u + s) * (yu : ZMod n)))
    rw [show (u + s) * (yu : ZMod n) = u * (yu : ZMod n) + s * (yu : ZMod n) by ring, AddChar.map_add_eq_mul]
    have hneg : ZMod.stdAddChar (-(s * (yu : ZMod n))) * ZMod.stdAddChar (s * (yu : ZMod n)) = 1 := by
      rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    calc
      ((jacobiCharZMod n (u + s) : ℤ) : ℂ) * ZMod.stdAddChar (u * (yu : ZMod n))
          = (((jacobiCharZMod n (u + s) : ℤ) : ℂ) * ZMod.stdAddChar (u * (yu : ZMod n))) * 1 := by ring
      _ = (((jacobiCharZMod n (u + s) : ℤ) : ℂ) * ZMod.stdAddChar (u * (yu : ZMod n))) *
            (ZMod.stdAddChar (-(s * (yu : ZMod n))) * ZMod.stdAddChar (s * (yu : ZMod n))) := by rw [hneg]
      _ = ZMod.stdAddChar (-(s * (yu : ZMod n))) *
            (((jacobiCharZMod n (u + s) : ℤ) : ℂ) *
              (ZMod.stdAddChar (u * (yu : ZMod n)) * ZMod.stdAddChar (s * (yu : ZMod n)))) := by ring

  have hbij : Function.Bijective (fun u : ZMod n => u * (yu : ZMod n)) := by
    constructor
    · intro a b hab
      have h := congrArg (fun z => z * ((yu⁻¹ : (ZMod n)ˣ) : ZMod n)) hab
      simpa only [mul_assoc, Units.mul_inv, mul_one] using h
    · intro v
      exact ⟨v * ((yu⁻¹ : (ZMod n)ˣ) : ZMod n), by
        show (v * ((yu⁻¹ : (ZMod n)ˣ) : ZMod n)) * (yu : ZMod n) = v
        rw [mul_assoc, Units.inv_mul, mul_one]⟩
  have hS :
      (∑ u : ZMod n, ((jacobiCharZMod n u : ℤ) : ℂ) * ZMod.stdAddChar (u * (yu : ZMod n)))
        = ((jacobiCharZMod n ((yu : ZMod n)) : ℤ) : ℂ) * jacobiGaussSum n := by
    have hreindex :
        (∑ u : ZMod n, ((jacobiCharZMod n u : ℤ) : ℂ) * ZMod.stdAddChar (u * (yu : ZMod n)))
          = ∑ v : ZMod n,
              ((jacobiCharZMod n (v * ((yu⁻¹ : (ZMod n)ˣ) : ZMod n)) : ℤ) : ℂ) * ZMod.stdAddChar v := by
      refine Fintype.sum_bijective (fun u : ZMod n => u * (yu : ZMod n)) hbij
        (fun u => ((jacobiCharZMod n u : ℤ) : ℂ) * ZMod.stdAddChar (u * (yu : ZMod n)))
        (fun v => ((jacobiCharZMod n (v * ((yu⁻¹ : (ZMod n)ˣ) : ZMod n)) : ℤ) : ℂ) * ZMod.stdAddChar v) ?_
      intro u
      show ((jacobiCharZMod n u : ℤ) : ℂ) * ZMod.stdAddChar (u * (yu : ZMod n))
          = ((jacobiCharZMod n ((u * (yu : ZMod n)) * ((yu⁻¹ : (ZMod n)ˣ) : ZMod n)) : ℤ) : ℂ) * ZMod.stdAddChar (u * (yu : ZMod n))
      rw [show (u * (yu : ZMod n)) * ((yu⁻¹ : (ZMod n)ˣ) : ZMod n) = u by
        rw [mul_assoc, Units.mul_inv, mul_one]]
    rw [hreindex]
    rw [show (∑ v : ZMod n, ((jacobiCharZMod n (v * ((yu⁻¹ : (ZMod n)ˣ) : ZMod n)) : ℤ) : ℂ) * ZMod.stdAddChar v)
        = ∑ v : ZMod n,
            (((jacobiCharZMod n ((yu : ZMod n)) : ℤ) : ℂ) * ((jacobiCharZMod n v : ℤ) : ℂ)) *
              ZMod.stdAddChar v from by
      apply Finset.sum_congr rfl
      intro v _
      rw [jacobiCharZMod_mul, jacobiCharZMod_unit_inv_eq]
      push_cast
      ring]
    rw [jacobiGaussSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [hshift, hS]
  ring

/-- For odd squarefree nonzero modulus, the shifted Jacobi Fourier identity holds whenever the
frequency is a unit or zero. This combines the two corresponding cases of Lemma 1 of
[VanDamHallgren2000]. -/
theorem lemma1_amplitude_unit_or_zero (n : ℕ) [NeZero n] (hn : Odd n) (hsq : Squarefree n)
    (s y : ZMod n) (hy : IsUnit y ∨ y = 0) :
    ∑ x : ZMod n, ((jacobiCharZMod n (x + s) : ℤ) : ℂ) * ZMod.stdAddChar (x * y)
      = jacobiGaussSum n * ZMod.stdAddChar (-(s * y)) * ((jacobiCharZMod n y : ℤ) : ℂ) := by
  rcases hy with hy | rfl
  · exact lemma1_amplitude_unit n hn hsq s y hy
  · exact lemma1_amplitude_zero n hn hsq s

end Qatlib.Papers.QuadChar00.MainResults
