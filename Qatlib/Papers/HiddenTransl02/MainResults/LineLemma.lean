/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
noncomputable section

namespace Qatlib.Papers.HiddenTransl02.MainResults.LineLemma

open Finset Matrix MvPolynomial

section Combination

variable {R : Type*} [CommRing R]

theorem add_mul_pow_expand (Z Y a : R) (k : ℕ) :
    (Z + a * Y) ^ k =
      ∑ i : Fin (k + 1), (Nat.choose k i.val : R) * a ^ (k - i.val) * Z ^ i.val *
        Y ^ (k - i.val) := by
  rw [add_pow]
  rw [← Fin.sum_univ_eq_sum_range (fun i => Z ^ i * (a * Y) ^ (k - i) * (Nat.choose k i : R))]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [mul_pow]
  ring

theorem line_combination_of_coeffs (Z Y : R) (k l : ℕ) (hl : l ≤ k) (c : Fin (k + 1) → R)
    (hc : ∀ i : Fin (k + 1),
      ∑ a : Fin (k + 1), c a * (Nat.choose k i.val : R) * (a.val : R) ^ (k - i.val) =
        if i.val = l then 1 else 0) :
    ∑ a : Fin (k + 1), c a * (Z + (a.val : R) * Y) ^ k = Z ^ l * Y ^ (k - l) := by
  have hexp : ∀ a : Fin (k + 1),
      c a * (Z + (a.val : R) * Y) ^ k =
        ∑ i : Fin (k + 1), c a * (Nat.choose k i.val : R) * (a.val : R) ^ (k - i.val) *
          Z ^ i.val * Y ^ (k - i.val) := by
    intro a
    rw [add_mul_pow_expand]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  rw [Finset.sum_congr rfl (fun a _ => hexp a)]
  rw [Finset.sum_comm]
  have hinner : ∀ i : Fin (k + 1),
      ∑ a : Fin (k + 1), c a * (Nat.choose k i.val : R) * (a.val : R) ^ (k - i.val) *
        Z ^ i.val * Y ^ (k - i.val) =
      (if i.val = l then 1 else 0) * Z ^ i.val * Y ^ (k - i.val) := by
    intro i
    rw [← Finset.sum_mul, ← Finset.sum_mul, hc i]
  rw [Finset.sum_congr rfl (fun i _ => hinner i)]
  rw [Finset.sum_eq_single (⟨l, by omega⟩ : Fin (k + 1))]
  · simp
  · intro i _ hi
    have hne : i.val ≠ l := by
      intro h
      exact hi (Fin.ext h)
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Combination

section Exists

variable {K : Type*} [Field K]

theorem coeffMatrix_mulVec_injective (k : ℕ)
    (hk : ∀ i ≤ k, (Nat.choose k i : K) ≠ 0)
    (hpt : Function.Injective (fun i : Fin (k + 1) => (i.val : K))) :
    Function.Injective
      (Matrix.of (fun (i a : Fin (k + 1)) =>
        (Nat.choose k i.val : K) * (a.val : K) ^ (k - i.val))).mulVec := by
  intro c d hcd
  have hzero : (Matrix.of (fun (i a : Fin (k + 1)) =>
      (Nat.choose k i.val : K) * (a.val : K) ^ (k - i.val))).mulVec (c - d) = 0 := by
    rw [Matrix.mulVec_sub, hcd, sub_self]
  have hsub : c - d = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
        (f := fun a : Fin (k + 1) => (a.val : K)) hpt
    intro i
    have hrow := congrFun hzero (Fin.rev i)
    simp only [Matrix.mulVec, Matrix.of_apply, dotProduct, Pi.zero_apply] at hrow

    have hval : (Fin.rev i).val = k - i.val := by
      rw [Fin.val_rev]
      omega
    have hchoice : (k - (Fin.rev i).val) = i.val := by omega
    have hcoef : ∀ a : Fin (k + 1),
        (Nat.choose k (Fin.rev i).val : K) * (a.val : K) ^ (k - (Fin.rev i).val) =
          (Nat.choose k i.val : K) * (a.val : K) ^ i.val := by
      intro a
      rw [hchoice]
      congr 1
      rw [hval]
      congr 1
      exact Nat.choose_symm (Nat.lt_succ_iff.mp i.isLt)
    simp_rw [hcoef] at hrow
    have hfac : (∑ a : Fin (k + 1), (Nat.choose k i.val : K) * (a.val : K) ^ i.val * (c - d) a)
        = (Nat.choose k i.val : K) * ∑ a : Fin (k + 1), (c - d) a * (a.val : K) ^ i.val := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro a _
      ring
    rw [hfac] at hrow
    have hne : (Nat.choose k i.val : K) ≠ 0 := hk i.val (Nat.lt_succ_iff.mp i.isLt)
    exact (mul_eq_zero.mp hrow).resolve_left hne
  exact sub_eq_zero.mp hsub

theorem exists_coeffs (k l : ℕ) (_hl : l ≤ k)
    (hk : ∀ i ≤ k, (Nat.choose k i : K) ≠ 0)
    (hpt : Function.Injective (fun i : Fin (k + 1) => (i.val : K))) :
    ∃ c : Fin (k + 1) → K,
      ∀ i : Fin (k + 1),
        ∑ a : Fin (k + 1), c a * (Nat.choose k i.val : K) * (a.val : K) ^ (k - i.val) =
          if i.val = l then 1 else 0 := by
  classical
  let M : Matrix (Fin (k + 1)) (Fin (k + 1)) K :=
    Matrix.of (fun (i a : Fin (k + 1)) =>
      (Nat.choose k i.val : K) * (a.val : K) ^ (k - i.val))
  have hinj : Function.Injective M.mulVec := coeffMatrix_mulVec_injective k hk hpt
  have hunit : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hsurj : Function.Surjective M.mulVec := Matrix.mulVec_surjective_iff_isUnit.mpr hunit
  let t : Fin (k + 1) → K := fun i => if i.val = l then 1 else 0
  obtain ⟨c, hc⟩ := hsurj t
  refine ⟨c, fun i => ?_⟩
  have hrow := congrFun hc i
  simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply, t] at hrow
  rw [← hrow]
  refine Finset.sum_congr rfl ?_
  intro a _
  ring

end Exists

section ZMod

theorem zmod_choose_ne_zero {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : k < p) {i : ℕ} (hi : i ≤ k) :
    (Nat.choose k i : ZMod p) ≠ 0 := by
  intro hzero
  have hfact : (Nat.choose k i : ZMod p) * (i.factorial : ZMod p) * ((k - i).factorial : ZMod p)
      = (k.factorial : ZMod p) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, Nat.choose_mul_factorial_mul_factorial hi]
  rw [hzero, zero_mul, zero_mul] at hfact
  have hkfact : (k.factorial : ZMod p) ≠ 0 := by
    intro hdvd
    rw [ZMod.natCast_eq_zero_iff] at hdvd
    exact absurd (Nat.Prime.dvd_factorial hp |>.mp hdvd) (by omega)
  exact hkfact hfact.symm

theorem zmod_natCast_injective_on_fin {p : ℕ} (_hp : p.Prime) {k : ℕ} (hk : k < p) :
    Function.Injective (fun i : Fin (k + 1) => (i.val : ZMod p)) := by
  intro i j hij
  have hi : i.val < p := by have := i.isLt; omega
  have hj : j.val < p := by have := j.isLt; omega
  have := (ZMod.natCast_eq_natCast_iff' i.val j.val p).mp hij
  rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  exact Fin.ext this

end ZMod

end Qatlib.Papers.HiddenTransl02.MainResults.LineLemma
