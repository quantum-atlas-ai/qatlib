/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ModularReversibleWord
import Qatlib.Concepts.HspRecovery.RecordExtract.ExecutionSemantics
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.MatrixAccess.RitzPipeline
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.RecordExtract
open scoped Classical

namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Lcg

def lcg {R : Type*} [CommSemiring R] (a c x : R) : ℕ → R
  | 0 => x
  | r+1 => a * lcg a c x r + c

def geometric {R : Type*} [CommSemiring R] (a : R) (r : ℕ) : R := ∑ q ∈ Finset.range r, a^q

theorem lcg_formula {R : Type*} [CommSemiring R] (a c x : R) (r : ℕ) :
    lcg a c x r = a^r*x + c*geometric a r := by
  induction r with
  | zero => simp [lcg, geometric]
  | succ r ih =>
    rw [lcg, ih]
    simp only [geometric, geom_sum_succ, pow_succ]
    ring

theorem lcg_restart {R : Type*} [CommSemiring R] (a c x : R) (j r : ℕ) :
    lcg a c x (j+r) = lcg a c (lcg a c x j) r := by
  induction r with
  | zero => simp [lcg]
  | succ r ih => exact congrArg (fun y => a*y+c) ih

theorem lcg_skip (n : ℕ) (a c x : ZMod (2^n)) (j r : ℕ) :
    lcg a c x (j+r) = a^r*lcg a c x j + c*∑ q ∈ Finset.range r, a^q := by
  rw [lcg_restart, lcg_formula]
  rfl

theorem lcg_one (n : ℕ) (c x : ZMod (2^n)) (r : ℕ) : lcg 1 c x r = x + c*(r:ZMod (2^n)) := by
  rw [lcg_formula]
  simp [geometric]

def natLcg (a c modulus seed : ℕ) : ℕ → ℕ
  | 0 => seed%modulus
  | r+1 => (a * natLcg a c modulus seed r + c)%modulus

theorem natLcg_cast (a c modulus seed r : ℕ) [NeZero modulus] :
    (natLcg a c modulus seed r : ZMod modulus) = lcg (a:ZMod modulus) (c:ZMod modulus) seed r := by
  induction r with
  | zero => simp [natLcg, lcg]
  | succ r ih => simp [natLcg, lcg, ih]

theorem natLcg_formula (a c modulus seed r : ℕ) [NeZero modulus] :
    natLcg a c modulus seed r = (a^r*seed+c*∑q ∈ Finset.range r, a^q)%modulus := by
  have hcast := natLcg_cast a c modulus seed r
  rw [lcg_formula] at hcast
  have hc : (natLcg a c modulus seed r : ZMod modulus) =
      ((a^r*seed+c*∑q ∈ Finset.range r, a^q : ℕ) : ZMod modulus) := by
    simpa only [geometric, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_sum] using! hcast
  have hval := congrArg ZMod.val hc
  have hbound : natLcg a c modulus seed r < modulus := by
    cases r <;> simp only [natLcg] <;> exact Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne modulus))
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hbound] using! hval

def lcgEquiv (n : ℕ) (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) : Equiv.Perm (ZMod (2^n)) where
  toFun x := (a:ZMod (2^n))*x+c
  invFun y := ((a⁻¹ : (ZMod (2^n))ˣ):ZMod (2^n))*(y-c)
  left_inv x := by
    (try dsimp only)
    rw [add_sub_cancel_right, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  right_inv y := by
    (try dsimp only)
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul, sub_add_cancel]

noncomputable def lcgMatrix (n : ℕ) (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) :
    Matrix (ZMod (2^n)) (ZMod (2^n)) ℂ := permMatrix (lcgEquiv n a c)

theorem lcgMatrix_unitary (n : ℕ) (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) :
    lcgMatrix n a c ∈ Matrix.unitaryGroup (ZMod (2^n)) ℂ :=
  permMatrix_unitary_of_injective (lcgEquiv n a c).injective

theorem lcgMatrix_basis (n : ℕ) (a : (ZMod (2^n))ˣ) (c x : ZMod (2^n)) :
    lcgMatrix n a c *ᵥ Ket x = Ket ((a:ZMod (2^n))*x+c) := by
  ext y
  simp [lcgMatrix, permMatrix, Matrix.mulVec, dotProduct,
    Qatlib.Foundations.PureStateMath.Ket, lcgEquiv]

def strided (D : ℕ) {N : ℕ} (j : Fin N) (i : Fin (D+1)) : ℕ := j.val*(D+1)+i.val+1

theorem strided_source (D : ℕ) {N : ℕ} (j : Fin N) (i : Fin (D+1)) :
    strided D j i = ((j.val+1)-1)*(D+1)+i.val+1 := by simp [strided]

theorem strided_bounds (D : ℕ) {N : ℕ} (j : Fin N) (i : Fin (D+1)) :
    0 < strided D j i ∧ strided D j i ≤ N*(D+1) := by
  constructor
  · unfold strided; omega
  · calc
      strided D j i ≤ j.val*(D+1)+(D+1) := by unfold strided; omega
      _ = (j.val+1)*(D+1) := by ring
      _ ≤ N*(D+1) := Nat.mul_le_mul_right (D+1) j.isLt

theorem strided_bit_bound (s d : ℕ) (hd : 0<d) (j : Fin (2^s)) (i : Fin (2^d+1)) :
    strided (2^d) j i < 2^(s+d+1) := by
  have hD : 2 ≤ 2^d := by
    have h := Nat.pow_le_pow_right (by omega : 1≤2) hd
    simpa using! h
  have hN : 0<2^s := by positivity
  have hmax : 2^s*(2^d+1) < 2^s*(2*2^d) := Nat.mul_lt_mul_of_pos_left (by omega) hN
  have hp : 2^s*(2*2^d) = 2^(s+d+1) := by rw [pow_succ, pow_add]; ring
  exact (strided_bounds (2^d) j i).2.trans_lt (hmax.trans_eq hp)

theorem strided_max (N D : ℕ) (hN : 0<N) :
    strided D (⟨N-1,by omega⟩ : Fin N) (⟨D,by omega⟩ : Fin (D+1)) = N*(D+1) := by
  unfold strided
  have h : N-1+1=N := by omega
  calc
    _ = (N-1+1)*(D+1) := by ring
    _ = _ := by rw [h]

theorem strided_old_width_fails (s d : ℕ) :
    ¬ (strided (2^d) (⟨2^s-1,Nat.sub_lt (by positivity : 0<2^s) (by decide : 0<1)⟩ : Fin (2^s))
      (⟨2^d,by omega⟩ : Fin (2^d+1)) < 2^(s+d)) := by
  rw [strided_max _ _ (by positivity), pow_add]
  have hp : 0<2^s := by positivity
  nlinarith

theorem strided_dimension_one_max (s : ℕ) :
    strided 1 (⟨2^s-1,Nat.sub_lt (by positivity : 0<2^s) (by decide : 0<1)⟩ : Fin (2^s)) (⟨1,by omega⟩ : Fin 2) = 2^(s+1) := by
  rw [strided_max _ _ (by positivity), pow_succ]

end Qatlib.Papers.MonteCarloInt20.PrnJump.Lcg
