/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ModularReversibleWord
import Qatlib.Concepts.HspRecovery.RecordExtract.ExecutionSemantics

/-!
# Linear congruential recurrences and stride bounds

`lcg` iterates an affine recurrence over a commutative semiring, and `lcg_formula` expresses its
jump using a finite geometric sum without division. The module relates this recurrence to
natural-number modular iteration and to unitary permutation matrices over power-of-two residues.

The `strided` index reserves one common variate per sample in addition to its individual
variates. Its bounds establish the extra bit required for the largest source position in the PRN
indexing convention. See [KanekoEtAl2020].

## Main statements

* `lcg_formula` and `natLcg_formula`: division-free jump formulas.
* `lcgMatrix_basis`: basis action of the affine permutation matrix.
* `strided_bit_bound` and `strided_old_width_fails`: sufficient and insufficient source-index
  widths.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

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

/-- Iterates the affine recurrence `x ↦ a*x+c` from an initial state over a commutative
semiring. -/
def lcg {R : Type*} [CommSemiring R] (a c x : R) : ℕ → R
  | 0 => x
  | r+1 => a * lcg a c x r + c

/-- The finite geometric sum of the first `r` powers of `a`. -/
def geometric {R : Type*} [CommSemiring R] (a : R) (r : ℕ) : R := ∑ q ∈ Finset.range r, a^q

/-- The affine recurrence after `r` steps equals `a^r*x` plus `c` times the finite geometric
sum. -/
theorem lcg_formula {R : Type*} [CommSemiring R] (a c x : R) (r : ℕ) :
    lcg a c x r = a^r*x + c*geometric a r := by
  induction r with
  | zero => simp [lcg, geometric]
  | succ r ih =>
    rw [lcg, ih]
    simp only [geometric, geom_sum_succ, pow_succ]
    ring

/-- Restarting the recurrence after `j` steps and taking `r` further steps equals taking `j+r`
steps. -/
theorem lcg_restart {R : Type*} [CommSemiring R] (a c x : R) (j r : ℕ) :
    lcg a c x (j+r) = lcg a c (lcg a c x j) r := by
  induction r with
  | zero => simp [lcg]
  | succ r ih => exact congrArg (fun y => a*y+c) ih

/-- The power-of-two modular recurrence has the division-free jump formula from the state at
position `j`. -/
theorem lcg_skip (n : ℕ) (a c x : ZMod (2^n)) (j r : ℕ) :
    lcg a c x (j+r) = a^r*lcg a c x j + c*∑ q ∈ Finset.range r, a^q := by
  rw [lcg_restart, lcg_formula]
  rfl

/-- With multiplier one, the recurrence is the initial state plus `r` increments modulo `2^n`.
See [KanekoEtAl2020]. -/
theorem lcg_one (n : ℕ) (c x : ZMod (2^n)) (r : ℕ) : lcg 1 c x r = x + c*(r:ZMod (2^n)) := by
  rw [lcg_formula]
  simp [geometric]

/-- Iterates a natural-number linear congruential generator, reducing the seed and every update
modulo `modulus`. -/
def natLcg (a c modulus seed : ℕ) : ℕ → ℕ
  | 0 => seed%modulus
  | r+1 => (a * natLcg a c modulus seed r + c)%modulus

/-- Casting the natural-number generator to a nonzero residue ring agrees with the affine
recurrence there. -/
theorem natLcg_cast (a c modulus seed r : ℕ) [NeZero modulus] :
    (natLcg a c modulus seed r : ZMod modulus) = lcg (a:ZMod modulus) (c:ZMod modulus) seed r := by
  induction r with
  | zero => simp [natLcg, lcg]
  | succ r ih => simp [natLcg, lcg, ih]

/-- The natural-number generator equals the division-free affine jump expression reduced modulo
its nonzero modulus. See [KanekoEtAl2020]. -/
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

/-- The affine permutation of power-of-two residues induced by a unit multiplier and an
arbitrary increment. -/
def lcgEquiv (n : ℕ) (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) : Equiv.Perm (ZMod (2^n)) where
  toFun x := (a:ZMod (2^n))*x+c
  invFun y := ((a⁻¹ : (ZMod (2^n))ˣ):ZMod (2^n))*(y-c)
  left_inv x := by
    (try dsimp only)
    rw [add_sub_cancel_right, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  right_inv y := by
    (try dsimp only)
    rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul, sub_add_cancel]

/-- The permutation matrix of the affine residue update. -/
noncomputable def lcgMatrix (n : ℕ) (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) :
    Matrix (ZMod (2^n)) (ZMod (2^n)) ℂ := permMatrix (lcgEquiv n a c)

/-- The matrix of the affine residue permutation is unitary. -/
theorem lcgMatrix_unitary (n : ℕ) (a : (ZMod (2^n))ˣ) (c : ZMod (2^n)) :
    lcgMatrix n a c ∈ Matrix.unitaryGroup (ZMod (2^n)) ℂ :=
  permMatrix_unitary_of_injective (lcgEquiv n a c).injective

/-- The affine permutation matrix sends the basis state at `x` to the basis state at `a*x+c`. -/
theorem lcgMatrix_basis (n : ℕ) (a : (ZMod (2^n))ˣ) (c x : ZMod (2^n)) :
    lcgMatrix n a c *ᵥ Ket x = Ket ((a:ZMod (2^n))*x+c) := by
  ext y
  simp [lcgMatrix, permMatrix, Matrix.mulVec, dotProduct,
    Qatlib.Foundations.PureStateMath.Ket, lcgEquiv]

/-- The one-based source position for a zero-based sample index and a coordinate among `D+1`
variates. -/
def strided (D : ℕ) {N : ℕ} (j : Fin N) (i : Fin (D+1)) : ℕ := j.val*(D+1)+i.val+1

/-- The zero-based sample convention for `strided` agrees with the displayed one-based source
formula. -/
theorem strided_source (D : ℕ) {N : ℕ} (j : Fin N) (i : Fin (D+1)) :
    strided D j i = ((j.val+1)-1)*(D+1)+i.val+1 := by simp [strided]

/-- Every strided source position is positive and at most `N*(D+1)`. -/
theorem strided_bounds (D : ℕ) {N : ℕ} (j : Fin N) (i : Fin (D+1)) :
    0 < strided D j i ∧ strided D j i ≤ N*(D+1) := by
  constructor
  · unfold strided; omega
  · calc
      strided D j i ≤ j.val*(D+1)+(D+1) := by unfold strided; omega
      _ = (j.val+1)*(D+1) := by ring
      _ ≤ N*(D+1) := Nat.mul_le_mul_right (D+1) j.isLt

/-- For positive `d`, every source position for `2^s` samples and `2^d` dimensions fits in
`s+d+1` bits. -/
theorem strided_bit_bound (s d : ℕ) (hd : 0<d) (j : Fin (2^s)) (i : Fin (2^d+1)) :
    strided (2^d) j i < 2^(s+d+1) := by
  have hD : 2 ≤ 2^d := by
    have h := Nat.pow_le_pow_right (by omega : 1≤2) hd
    simpa using! h
  have hN : 0<2^s := by positivity
  have hmax : 2^s*(2^d+1) < 2^s*(2*2^d) := Nat.mul_lt_mul_of_pos_left (by omega) hN
  have hp : 2^s*(2*2^d) = 2^(s+d+1) := by rw [pow_succ, pow_add]; ring
  exact (strided_bounds (2^d) j i).2.trans_lt (hmax.trans_eq hp)

/-- The final sample and final coordinate attain source position `N*(D+1)` when there is at
least one sample. -/
theorem strided_max (N D : ℕ) (hN : 0<N) :
    strided D (⟨N-1,by omega⟩ : Fin N) (⟨D,by omega⟩ : Fin (D+1)) = N*(D+1) := by
  unfold strided
  have h : N-1+1=N := by omega
  calc
    _ = (N-1+1)*(D+1) := by ring
    _ = _ := by rw [h]

/-- The largest strided source position does not fit in `s+d` bits. See [KanekoEtAl2020]. -/
theorem strided_old_width_fails (s d : ℕ) :
    ¬ (strided (2^d) (⟨2^s-1,Nat.sub_lt (by positivity : 0<2^s) (by decide : 0<1)⟩ : Fin (2^s))
      (⟨2^d,by omega⟩ : Fin (2^d+1)) < 2^(s+d)) := by
  rw [strided_max _ _ (by positivity), pow_add]
  have hp : 0<2^s := by positivity
  nlinarith

/-- With one dimension, the last source position for `2^s` samples is exactly `2^(s+1)`. -/
theorem strided_dimension_one_max (s : ℕ) :
    strided 1 (⟨2^s-1,Nat.sub_lt (by positivity : 0<2^s) (by decide : 0<1)⟩ : Fin (2^s)) (⟨1,by omega⟩ : Fin 2) = 2^(s+1) := by
  rw [strided_max _ _ (by positivity), pow_succ]

end Qatlib.Papers.MonteCarloInt20.PrnJump.Lcg
