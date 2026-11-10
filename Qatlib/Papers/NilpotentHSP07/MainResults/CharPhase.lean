/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NilpotentHSP07.MainResults

open scoped BigOperators

noncomputable def omega (p : ℕ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / p)

theorem omega_pow_p {p : ℕ} (hp : p ≠ 0) : omega p ^ p = 1 := by
  unfold omega
  rw [← Complex.exp_nat_mul]
  have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have h : (p : ℂ) * (2 * (Real.pi : ℂ) * Complex.I / p) = 2 * (Real.pi : ℂ) * Complex.I := by
    field_simp
  rw [h]
  exact Complex.exp_two_pi_mul_I

theorem omega_pow_mod {p : ℕ} (hp : p ≠ 0) (m : ℕ) : omega p ^ (m % p) = omega p ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m p]
  rw [pow_add, pow_mul, omega_pow_p hp, one_pow, one_mul]

variable {p : ℕ} [Fact p.Prime] {m d : ℕ}

def dot (u z : Fin d → ZMod p) : ZMod p := ∑ i, u i * z i

theorem dot_add (u z z' : Fin d → ZMod p) : dot u (z + z') = dot u z + dot u z' := by
  simp [dot, mul_add, Finset.sum_add_distrib]

theorem dot_smul (u z : Fin d → ZMod p) (a : ZMod p) : dot u (a • z) = a * dot u z := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem dot_zero (u : Fin d → ZMod p) : dot u 0 = 0 := by
  simp [dot]

noncomputable def charFun (u z : Fin d → ZMod p) : ℂ := omega p ^ (dot u z).val

theorem charFun_add (u z z' : Fin d → ZMod p) :
    charFun u (z + z') = charFun u z * charFun u z' := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : NeZero p := ⟨hp⟩
  unfold charFun
  rw [dot_add, ZMod.val_add, omega_pow_mod hp, pow_add]

theorem charFun_zero (u : Fin d → ZMod p) : charFun u 0 = 1 := by
  simp [charFun, dot_zero]

theorem charFun_smul (u z : Fin d → ZMod p) (a : ZMod p) :
    charFun u (a • z) = charFun u z ^ a.val := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  calc charFun u (a • z)
      = omega p ^ (a * dot u z).val := by simp only [charFun]; rw [dot_smul]
    _ = omega p ^ (a.val * (dot u z).val % p) := by rw [ZMod.val_mul]
    _ = omega p ^ (a.val * (dot u z).val) := omega_pow_mod hp _
    _ = (omega p ^ (dot u z).val) ^ a.val := by
          rw [← pow_mul, Nat.mul_comm]
    _ = charFun u z ^ a.val := by rw [charFun]

theorem charFun_neg (u z : Fin d → ZMod p) : charFun u (-z) = (charFun u z)⁻¹ := by
  have h : charFun u (z + -z) = charFun u z * charFun u (-z) := charFun_add u z (-z)
  rw [add_neg_cancel, charFun_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem charFun_phi_gPrime (u z : Fin d → ZMod p) (j : ZMod p) :
    charFun u ((j * j) • z) = charFun u z ^ ((j * j).val) :=
  charFun_smul u z (j * j)

theorem charFun_phi_h (u zh : Fin d → ZMod p) (j : ZMod p) :
    charFun u ((j - j * j) • zh) = charFun u zh ^ ((j - j * j).val) :=
  charFun_smul u zh (j - j * j)

theorem prod_charFun {n : ℕ} (U : Fin n → Fin d → ZMod p) (V : Fin n → Fin d → ZMod p) :
    ∏ i, charFun (U i) (V i) = omega p ^ (∑ i, dot (U i) (V i)).val := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : NeZero p := ⟨hp⟩
  induction (Finset.univ : Finset (Fin n)) using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, charFun, ih, ← pow_add,
        ZMod.val_add, omega_pow_mod hp]

theorem triplePhase_eq_one {n : ℕ} (U : Fin n → Fin d → ZMod p) (J : Fin n → ZMod p)
    (zh z : Fin d → ZMod p)
    (hquad : ∀ k, ∑ i, U i k * (J i * J i) = 0)
    (hlinear : ∀ k, ∑ i, U i k * J i = 0) :
    ∏ i, charFun (U i) ((J i - J i * J i) • zh + (J i * J i) • z) = 1 := by
  rw [prod_charFun]
  have hzero :
      (∑ i, dot (U i) ((J i - J i * J i) • zh + (J i * J i) • z)) = 0 := by
    have hsplit :
        (∑ i, dot (U i) ((J i - J i * J i) • zh + (J i * J i) • z))
          = (∑ i, (J i - J i * J i) * dot (U i) zh)
            + (∑ i, (J i * J i) * dot (U i) z) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by rw [dot_add, dot_smul, dot_smul])
    rw [hsplit]
    have hdiff : ∀ k, ∑ i, U i k * (J i - J i * J i) = 0 := by
      intro k
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [hlinear k, hquad k, sub_zero]

    have h1 : (∑ i, (J i - J i * J i) * dot (U i) zh)
        = ∑ k, zh k * (∑ i, U i k * (J i - J i * J i)) := by
      simp only [dot, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => by ring))
    have h2 : (∑ i, (J i * J i) * dot (U i) z)
        = ∑ k, z k * (∑ i, U i k * (J i * J i)) := by
      simp only [dot, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => by ring))
    rw [h1, h2]
    simp [hdiff, hquad]
  rw [hzero]
  simp

end Qatlib.Papers.NilpotentHSP07.MainResults
