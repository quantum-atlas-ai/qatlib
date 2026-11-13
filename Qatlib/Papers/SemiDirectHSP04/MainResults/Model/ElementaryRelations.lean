/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemiDirectHSP04.MainResults.Model.SemidirectGroup
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Elementary relations in cyclic semidirect products

`px` and `py` embed the two cyclic factors of `Ppr`, giving a normal form and the action
commutation relation. Powers of the canonical unit reduce to a linear expression modulo `p ^ r`;
`pow_formula` uses such a linear action formula and an annihilation hypothesis to compute powers
of a general normal-form element. See [InuiLeGall2007] for the mathematical setting.

## Main statements

* `normal_form`: writes every element as a product of its two cyclic coordinates.
* `py_mul_px`: computes the action when interchanging the cyclic factors.
* `pow_formula`: gives the normal form of a power using a binomial coefficient.

## References

* [Inui and Le Gall, 2007][InuiLeGall2007]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP04.MainResults.Model

variable {p r : ℕ}

/-- Embeds a residue modulo `p ^ r` into the left factor of `Ppr` with identity right
coordinate. -/
def px (p r : ℕ) (u : (ZMod (p ^ r))ˣ) (hu : u ^ p = 1) (a : ZMod (p ^ r)) :
    Ppr p r u hu :=
  SemidirectProduct.inl (Multiplicative.ofAdd a)

/-- Embeds a residue modulo `p` into the right factor of `Ppr` with identity left coordinate. -/
def py (p r : ℕ) (u : (ZMod (p ^ r))ˣ) (hu : u ^ p = 1) (b : ZMod p) :
    Ppr p r u hu :=
  SemidirectProduct.inr (Multiplicative.ofAdd b)

/-- The left embedding sends zero to the group identity. -/
@[simp] theorem px_zero (u : (ZMod (p ^ r))ˣ) (hu : u ^ p = 1) :
    px p r u hu 0 = 1 := by simp [px]

/-- The right embedding sends zero to the group identity. -/
@[simp] theorem py_zero (u : (ZMod (p ^ r))ˣ) (hu : u ^ p = 1) :
    py p r u hu 0 = 1 := by simp [py]

/-- The left embedding sends addition of residues to multiplication in `Ppr`. -/
theorem px_add (u : (ZMod (p ^ r))ˣ) (hu : u ^ p = 1) (a a' : ZMod (p ^ r)) :
    px p r u hu (a + a') = px p r u hu a * px p r u hu a' := by
  simp [px, ofAdd_add]

/-- The right embedding sends addition of residues to multiplication in `Ppr`. -/
theorem py_add (u : (ZMod (p ^ r))ˣ) (hu : u ^ p = 1) (b b' : ZMod p) :
    py p r u hu (b + b') = py p r u hu b * py p r u hu b' := by
  simp [py, ofAdd_add]

/-- A natural power of a left-embedded residue multiplies that residue by the exponent. -/
theorem px_pow (u : (ZMod (p ^ r))ˣ) (hu : u ^ p = 1) (a : ZMod (p ^ r)) (n : ℕ) :
    px p r u hu a ^ n = px p r u hu (n * a) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, ← px_add]
    congr 1
    push_cast
    ring

/-- A natural power of a right-embedded residue multiplies that residue by the exponent. -/
theorem py_pow (u : (ZMod (p ^ r))ˣ) (hu : u ^ p = 1) (b : ZMod p) (n : ℕ) :
    py p r u hu b ^ n = py p r u hu (n * b) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, ← py_add]
    congr 1
    push_cast
    ring

/-- Every element of `Ppr` is the product of the left embedding of its left coordinate and the
right embedding of its right coordinate. -/
theorem normal_form (u : (ZMod (p ^ r))ˣ) (hu : u ^ p = 1) (g : Ppr p r u hu) :
    g = px p r u hu g.left.toAdd * py p r u hu g.right.toAdd := by
  conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right g]
  simp [px, py]

/-- Taking a natural power of the multiplication automorphism is equivalent to taking that power
of its defining unit. -/
theorem unitMulAut_pow (n k : ℕ) (u : (ZMod n)ˣ) :
    (unitMulAut n u) ^ k = unitMulAut n (u ^ k) := by
  change (unitMulAutHom n u) ^ k = unitMulAutHom n (u ^ k)
  rw [← map_pow]

/-- The `k`th power of the multiplication automorphism acts by multiplication by the residue `u
^ k`. -/
theorem unitMulAut_pow_apply (n k : ℕ) (u : (ZMod n)ˣ) (a : Cyc n) :
    ((unitMulAut n u) ^ k) a
      = Multiplicative.ofAdd ((u : ZMod n) ^ k * Multiplicative.toAdd a) := by
  rw [unitMulAut_pow]
  conv_lhs => rw [show a = Multiplicative.ofAdd (Multiplicative.toAdd a) from rfl]
  rw [unitMulAut_apply, Units.val_pow_eq_pow_val]

/-- The cyclic action at residue `b` multiplies the left coordinate by `u ^ b.val` when `p` is
nonzero. -/
theorem cyclicAction_ofAdd_apply [NeZero p] (u : (ZMod (p ^ r))ˣ) (hu : u ^ p = 1)
    (b : ZMod p) (a : ZMod (p ^ r)) :
    cyclicAction p (p ^ r) u hu (Multiplicative.ofAdd b) (Multiplicative.ofAdd a)
      = Multiplicative.ofAdd ((u : ZMod (p ^ r)) ^ b.val * a) := by
  unfold cyclicAction
  rw [AddMonoidHom.coe_toMultiplicativeLeft]
  simp only [Function.comp_apply]
  have hcast : (Multiplicative.toAdd (Multiplicative.ofAdd b) : ZMod p)
      = ((b.val : ℕ) : ZMod p) := by
    rw [toAdd_ofAdd]
    exact (ZMod.natCast_zmod_val b).symm
  have hcast2 : (((b.val : ℕ)) : ZMod p) = (((b.val : ℕ)) : ℤ) := by push_cast; ring
  rw [hcast, hcast2, ZMod.lift_coe]
  simp only [zmultiplesHom_apply]
  rw [← ofMul_zpow, zpow_natCast]
  exact unitMulAut_pow_apply (p ^ r) b.val u (Multiplicative.ofAdd a)

/-- Interchanging a right-embedded residue with a left-embedded residue multiplies the latter by
`u ^ b.val`. -/
theorem py_mul_px [NeZero p] (u : (ZMod (p ^ r))ˣ) (hu : u ^ p = 1)
    (b : ZMod p) (a : ZMod (p ^ r)) :
    py p r u hu b * px p r u hu a =
      px p r u hu ((u : ZMod (p ^ r)) ^ b.val * a) * py p r u hu b := by
  ext
  · simp [px, py, cyclicAction_ofAdd_apply]
  · simp [px, py]

/-- The canonical unit has underlying residue `1 + p ^ (r - 1)`. -/
theorem canonicalUnit_coe (p r : ℕ) (hp : p.Prime) (hr : 2 ≤ r) :
    ((canonicalUnit p r hp hr : (ZMod (p ^ r))ˣ) : ZMod (p ^ r))
      = 1 + (p ^ (r - 1) : ℕ) := by
  simp only [canonicalUnit, ZMod.coe_unitOfCoprime]
  push_cast
  ring

/-- For `r ≥ 2`, the square of `p ^ (r - 1)` vanishes modulo `p ^ r`. -/
theorem primePow_sq_zero (p r : ℕ) (hr : 2 ≤ r) :
    ((p ^ (r - 1) : ℕ) : ZMod (p ^ r)) ^ 2 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  refine ⟨p ^ (r - 2), ?_⟩
  rw [pow_two, ← pow_add, ← pow_add]
  congr 1
  omega

/-- For `r ≥ 2`, the `k`th power of `1 + p ^ (r - 1)` is `1 + k * p ^ (r - 1)` modulo `p ^ r`. -/
theorem one_add_primePow_pow (p r : ℕ) (hr : 2 ≤ r) (k : ℕ) :
    (1 + ((p ^ (r - 1) : ℕ) : ZMod (p ^ r))) ^ k
      = 1 + (k : ZMod (p ^ r)) * ((p ^ (r - 1) : ℕ) : ZMod (p ^ r)) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    have h2 : ((p ^ (r - 1) : ℕ) : ZMod (p ^ r)) *
        ((p ^ (r - 1) : ℕ) : ZMod (p ^ r)) = 0 := by
      rw [← pow_two]
      exact primePow_sq_zero p r hr
    rw [mul_add, mul_one, add_mul, one_mul, mul_assoc, h2, mul_zero, add_zero]
    push_cast
    ring

/-- The underlying residue of the `k`th canonical-unit power is `1 + k * p ^ (r - 1)`. -/
theorem canonicalUnit_pow_coe (p r : ℕ) (hp : p.Prime) (hr : 2 ≤ r) (k : ℕ) :
    (((canonicalUnit p r hp hr) ^ k : (ZMod (p ^ r))ˣ) : ZMod (p ^ r))
      = 1 + (k : ZMod (p ^ r)) * ((p ^ (r - 1) : ℕ) : ZMod (p ^ r)) := by
  rw [Units.val_pow_eq_pow_val, canonicalUnit_coe p r hp hr,
    one_add_primePow_pow p r hr]

/-- A unit whose `p`th power is one has equal powers at natural exponents congruent modulo `p`. -/
theorem unit_pow_eq_pow_of_modEq (u : (ZMod (p ^ r))ˣ) (hu : u ^ p = 1) {a b : ℕ}
    (h : a ≡ b [MOD p]) : u ^ a = u ^ b := by
  rw [pow_eq_pow_iff_modEq]
  exact h.of_dvd (orderOf_dvd_of_pow_eq_one hu)

/-- The representative of `n * b` is congruent to `n * b.val` modulo nonzero `p`. -/
theorem val_mul_modEq [NeZero p] (b : ZMod p) (n : ℕ) :
    (n * b).val ≡ n * b.val [MOD p] := by
  rw [← ZMod.natCast_eq_natCast_iff]
  rw [ZMod.natCast_zmod_val, Nat.cast_mul, ZMod.natCast_zmod_val]

/-- Congruent natural numbers modulo `p` act equally on any residue annihilated by `p`. -/
theorem natCast_mul_eq_of_modEq [NeZero p] {P : ZMod (p ^ r)}
    (hPp : (p : ZMod (p ^ r)) * P = 0) {a b : ℕ} (h : a ≡ b [MOD p]) :
    (a : ZMod (p ^ r)) * P = (b : ZMod (p ^ r)) * P := by
  have hd : (p : ℤ) ∣ (b : ℤ) - (a : ℤ) := Nat.modEq_iff_dvd.mp h
  obtain ⟨m, hm⟩ := hd
  have hcast : (b : ZMod (p ^ r)) - (a : ZMod (p ^ r))
      = (p : ZMod (p ^ r)) * (m : ZMod (p ^ r)) := by
    have h2 : ((b : ℤ) - (a : ℤ) : ℤ) = (p : ℤ) * m := hm
    calc (b : ZMod (p ^ r)) - (a : ZMod (p ^ r))
        = (((b : ℤ) - (a : ℤ) : ℤ) : ZMod (p ^ r)) := by push_cast; ring
      _ = (((p : ℤ) * m : ℤ) : ZMod (p ^ r)) := by rw [h2]
      _ = (p : ZMod (p ^ r)) * (m : ZMod (p ^ r)) := by push_cast; ring
  have hzero : (p : ZMod (p ^ r)) * (m : ZMod (p ^ r)) * P = 0 := by
    rw [mul_assoc, mul_comm (m : ZMod (p ^ r)) P, ← mul_assoc, hPp, zero_mul]
  have hsub : (a : ZMod (p ^ r))
      = (b : ZMod (p ^ r)) - (p : ZMod (p ^ r)) * (m : ZMod (p ^ r)) := by
    rw [← hcast]; ring
  rw [hsub, sub_mul, hzero, sub_zero]

/-- Under the linear power formula for `u` and the condition `p * P = 0`, computes the `c`th
power of a normal-form element using `c.choose 2`. See [Inui and Le Gall, 2007, Proposition
7][InuiLeGall2007]. -/
theorem pow_formula [NeZero p] (u : (ZMod (p ^ r))ˣ) (hu : u ^ p = 1) (P : ZMod (p ^ r))
    (hP : ∀ k : ℕ, (u : ZMod (p ^ r)) ^ k = 1 + (k : ZMod (p ^ r)) * P)
    (hPp : (p : ZMod (p ^ r)) * P = 0)
    (a : ZMod (p ^ r)) (b : ZMod p) (c : ℕ) :
    (px p r u hu a * py p r u hu b) ^ c
      = px p r u hu (a * ((c : ZMod (p ^ r)) +
            ((c.choose 2 : ℕ) : ZMod (p ^ r)) * (b.val : ZMod (p ^ r)) * P))
        * py p r u hu (c * b) := by
  induction c with
  | zero => simp [px, py]
  | succ n ih =>
    have hstep : px p r u hu (a * ((n : ZMod (p ^ r)) +
          ((n.choose 2 : ℕ) : ZMod (p ^ r)) * (b.val : ZMod (p ^ r)) * P))
        * py p r u hu ((n : ZMod p) * b) * (px p r u hu a * py p r u hu b)
        = px p r u hu (a * ((n : ZMod (p ^ r)) +
            ((n.choose 2 : ℕ) : ZMod (p ^ r)) * (b.val : ZMod (p ^ r)) * P)
            + (1 + ((((n : ZMod p) * b).val : ℕ) : ZMod (p ^ r)) * P) * a)
          * py p r u hu ((n : ZMod p) * b + b) := by
      simp only [mul_assoc]
      rw [← mul_assoc (py p r u hu ((n : ZMod p) * b)) (px p r u hu a) (py p r u hu b)]
      rw [py_mul_px, hP ((((n : ZMod p) * b).val))]
      rw [mul_assoc (px p r u hu _)]
      rw [← mul_assoc (px p r u hu _) (px p r u hu _) (py p r u hu ((n : ZMod p) * b) * py p r u hu b)]
      rw [← px_add, ← py_add]
    have hval : (1 + (((((n : ZMod p) * b).val : ℕ)) : ZMod (p ^ r)) * P)
        = 1 + ((n * b.val : ℕ) : ZMod (p ^ r)) * P := by
      rw [natCast_mul_eq_of_modEq (r := r) hPp (val_mul_modEq b n)]
    have hchoose : ((n + 1).choose 2 : ZMod (p ^ r))
        = (n.choose 2 : ZMod (p ^ r)) + (n : ZMod (p ^ r)) := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      push_cast
      ring
    rw [pow_succ, ih, hstep, hval]
    congr 1
    · rw [hchoose]
      push_cast
      ring
    · push_cast
      ring

end Qatlib.Papers.SemiDirectHSP04.MainResults.Model
