/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQuery97.MainResults.DatabaseDefs
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Parity phases and coin-weighing amplitudes

`bAmplitude` supplies an alternating character on the even cyclic answer register, and a
subset-weight query induces the binary dot-product phase `queryPhase`. Orthogonality of these
phases evaluates the final Hadamard amplitude as a Kronecker delta. See [TerhalSmolin1998] for
the source development.

## Main statements

* `bAmplitude_shift`: identifies the phase introduced by a weighing-answer shift.
* `queryPhase_inner_sum`: proves orthogonality of the binary phase functions.
* `postHadamardAmplitude_eq`: evaluates the recovered-register amplitude.

## References

* [Terhal and Smolin, 1998][TerhalSmolin1998]
-/

namespace Qatlib.Papers.SingleQuery97.MainResults.CoinWeighing

open Finset
open Qatlib.Papers.SingleQuery97.MainResults.DatabaseDefs

/-- The parity sign of a finite sum of natural numbers is the product of their parity signs. -/
theorem signOfParity_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    signOfParity (∑ i ∈ s, f i) = ∏ i ∈ s, signOfParity (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, signOfParity_add, ih]

/-- The complex alternating amplitude on the cyclic answer register, defined by the parity of
the canonical representative. -/
noncomputable def bAmplitude (n : ℕ) (b : ZMod (registerN n)) : ℂ :=
  signOfParity b.val

/-- The alternating answer amplitude maps cyclic addition to multiplication of complex
amplitudes. -/
theorem bAmplitude_add (n : ℕ) (a b : ZMod (registerN n)) :
    bAmplitude n (a + b) = bAmplitude n a * bAmplitude n b := by
  unfold bAmplitude
  rw [ZMod.val_add, signOfParity_mod_of_dvd (two_dvd_registerN n), signOfParity_add]

/-- The alternating amplitude of a natural number cast into the answer register is its parity
sign. -/
theorem bAmplitude_natCast (n m : ℕ) :
    bAmplitude n (m : ZMod (registerN n)) = signOfParity m := by
  unfold bAmplitude
  rw [ZMod.val_natCast, signOfParity_mod_of_dvd (two_dvd_registerN n)]

/-- Shifting the answer register by the subset-intersection weight multiplies its alternating
amplitude by the parity sign of the query-database dot product. -/
theorem bAmplitude_shift (n : ℕ) (x y : DbVec n) (b : ZMod (registerN n)) :
    bAmplitude n ((weight (wedge x y) : ZMod (registerN n)) + b) =
      signOfParity (dot x y) * bAmplitude n b := by
  rw [bAmplitude_add, bAmplitude_natCast, weight_wedge_eq_dot]

/-- The binary query phase given by the parity sign of the dot product of query `x` and database
`y`. -/
noncomputable def queryPhase {n : ℕ} (y x : DbVec n) : ℂ :=
  signOfParity (dot x y)

/-- The query phase factors into the product of the parity signs of the coordinatewise bit
products. -/
theorem queryPhase_factor {n : ℕ} (y x : DbVec n) :
    queryPhase y x = ∏ i, signOfParity (bitVal (x i) * bitVal (y i)) := by
  unfold queryPhase dot
  rw [signOfParity_sum]

/-- The product of two database query phases equals the product of the coordinatewise signs of
the summed bit products. -/
theorem queryPhase_mul_eq {n : ℕ} (y y' x : DbVec n) :
    queryPhase y x * queryPhase y' x =
      ∏ i, signOfParity
        (bitVal (y i) * bitVal (x i) + bitVal (y' i) * bitVal (x i)) := by
  unfold queryPhase dot
  rw [signOfParity_sum, signOfParity_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro i _
  rw [← signOfParity_add]
  congr 1
  ring

/-- The sum over queries of the product of two database phases is `2 ^ n` when the databases
agree and zero otherwise. -/
theorem queryPhase_inner_sum {n : ℕ} (y y' : DbVec n) :
    (∑ x : DbVec n, queryPhase y x * queryPhase y' x) =
      if y = y' then ((2 : ℂ) ^ n) else 0 := by
  classical
  simp_rw [queryPhase_mul_eq]
  rw [← Fintype.prod_sum (κ := fun _ => Bool)
    (f := fun i (b : Bool) =>
      signOfParity (bitVal (y i) * bitVal b + bitVal (y' i) * bitVal b))]
  have hfac : ∀ i : Fin n,
      (∑ b : Bool,
          signOfParity (bitVal (y i) * bitVal b + bitVal (y' i) * bitVal b)) =
        if y i = y' i then (2 : ℂ) else 0 := by
    intro i
    rw [Fintype.sum_bool]
    cases hy : y i <;> cases hy' : y' i <;>
      norm_num [bitVal, signOfParity, hy, hy']
  simp_rw [hfac]
  by_cases h : y = y'
  · subst h
    simp [Finset.prod_const]
  · have hex : ∃ i, y i ≠ y' i := by
      by_contra hh
      simp only [not_exists, not_not] at hh
      exact h (funext hh)
    obtain ⟨i, hi⟩ := hex
    rw [if_neg h]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp [hi]

/-- The normalized phase-correlation sum giving the amplitude at candidate output `z` for hidden
database `y`. -/
noncomputable def postHadamardAmplitude {n : ℕ} (y z : DbVec n) : ℂ :=
  ((2 : ℂ) ^ n)⁻¹ * ∑ x : DbVec n, queryPhase y x * queryPhase z x

/-- The post-Hadamard amplitude is one at the hidden database and zero at every other database. -/
theorem postHadamardAmplitude_eq {n : ℕ} (y z : DbVec n) :
    postHadamardAmplitude y z = if y = z then 1 else 0 := by
  unfold postHadamardAmplitude
  rw [queryPhase_inner_sum]
  by_cases h : y = z
  · rw [if_pos h, if_pos h]
    exact inv_mul_cancel₀ (pow_ne_zero n (by norm_num))
  · rw [if_neg h, if_neg h, mul_zero]

/-- The cyclic answer-register size is even and strictly larger than the database length. -/
theorem register_properties (n : ℕ) :
    2 ∣ registerN n ∧ n < registerN n :=
  ⟨two_dvd_registerN n, n_lt_registerN n⟩

/-- Reducing a weighing answer modulo the answer-register size preserves the parity of the
query-database dot product. -/
theorem coinWeighing_uses_parity {n : ℕ} (x y : DbVec n) :
    (weight (wedge x y) % registerN n) % 2 = dot x y % 2 :=
  weight_mod_registerN_parity x y

/-- The weighing shift introduces the binary dot-product phase, and the post-Hadamard amplitude
is one exactly at the hidden database and zero elsewhere. -/
theorem coinWeighing_phase_identities {n : ℕ} (y z : DbVec n) :
    (∀ (x : DbVec n) (b : ZMod (registerN n)),
        bAmplitude n ((weight (wedge x y) : ZMod (registerN n)) + b) =
          signOfParity (dot x y) * bAmplitude n b) ∧
      postHadamardAmplitude y z = if z = y then 1 else 0 := by
  refine ⟨fun x b => bAmplitude_shift n x y b, ?_⟩
  rw [postHadamardAmplitude_eq]
  by_cases h : y = z
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun he => h he.symm)]

end Qatlib.Papers.SingleQuery97.MainResults.CoinWeighing
