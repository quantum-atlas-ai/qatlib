/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SemiDirectHSP04.MainResults.Model.SemidirectGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.OrderOfElement

/-!
# Isomorphic cyclic semidirect products from equal-order units

The action calculations express powers of `unitMulAut` and evaluate `cyclicAction` using natural
residue representatives. `prop5_isomorphic_of_same_order` then identifies semidirect products
defined by units of the same prime order modulo an odd prime power. See [InuiLeGall2007] for the
mathematical setting.

## Main statements

* `prop5_isomorphic_of_same_order`: produces an isomorphism between the two unit-defined
  semidirect products.

## References

* [Inui and Le Gall, 2007][InuiLeGall2007]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemiDirectHSP04.MainResults.Proposition5

open Qatlib.Papers.SemiDirectHSP04.MainResults.Model

/-- The `k`th power of multiplication by `u` is multiplication by `u ^ k`. -/
theorem unitMulAut_pow (n k : ℕ) (u : (ZMod n)ˣ) :
    (unitMulAut n u) ^ k = unitMulAut n (u ^ k) := by
  change (unitMulAutHom n u) ^ k = unitMulAutHom n (u ^ k)
  rw [← map_pow]

/-- The `k`th automorphism power multiplies the underlying additive coordinate by the residue `u
^ k`. -/
theorem unitMulAut_pow_apply (n k : ℕ) (u : (ZMod n)ˣ) (a : Cyc n) :
    ((unitMulAut n u) ^ k) a
      = Multiplicative.ofAdd ((u : ZMod n) ^ k * Multiplicative.toAdd a) := by
  rw [unitMulAut_pow]
  conv_lhs => rw [show a = Multiplicative.ofAdd (Multiplicative.toAdd a) from rfl]
  rw [unitMulAut_apply, Units.val_pow_eq_pow_val]

/-- For nonzero `q`, the cyclic action at `h` multiplies by `u` raised to the natural
representative of `h`. -/
theorem cyclicAction_apply (q n : ℕ) [NeZero q] (u : (ZMod n)ˣ) (hu : u ^ q = 1)
    (h : Cyc q) (a : Cyc n) :
    cyclicAction q n u hu h a
      = Multiplicative.ofAdd
          ((u : ZMod n) ^ (Multiplicative.toAdd h).val * Multiplicative.toAdd a) := by
  unfold cyclicAction
  rw [AddMonoidHom.coe_toMultiplicativeLeft]
  simp only [Function.comp_apply]
  have hcast : Multiplicative.toAdd h
      = (((Multiplicative.toAdd h).val : ℕ) : ZMod q) := (ZMod.natCast_zmod_val _).symm
  conv_lhs => rw [hcast]
  have hcast2 : ((((Multiplicative.toAdd h).val : ℕ)) : ZMod q)
      = (((Multiplicative.toAdd h).val : ℤ) : ZMod q) := by push_cast; ring
  rw [hcast2, ZMod.lift_coe]
  simp only [zmultiplesHom_apply]
  rw [← ofMul_zpow, zpow_natCast]
  exact unitMulAut_pow_apply n _ u a

/-- If `u ^ q = 1`, natural exponents congruent modulo `q` give equal powers of `u`. -/
theorem unit_pow_eq_pow_of_modEq (n q a b : ℕ) (u : (ZMod n)ˣ) (hu : u ^ q = 1)
    (h : a ≡ b [MOD q]) : u ^ a = u ^ b := by
  rw [pow_eq_pow_iff_modEq]
  exact h.of_dvd (orderOf_dvd_of_pow_eq_one hu)

/-- For odd prime `p`, prime `q`, and `r ≥ 1`, two units modulo `p ^ r` of order `q` define
isomorphic cyclic semidirect products. See [Inui and Le Gall, 2007, Proposition
5][InuiLeGall2007]. -/
theorem prop5_isomorphic_of_same_order
    (p q r : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hr : 1 ≤ r)
    (u v : (ZMod (p ^ r))ˣ) (hu : u ^ q = 1) (hv : v ^ q = 1)
    (hou : orderOf u = q) (hov : orderOf v = q) :
    Nonempty (Pqr q (p ^ r) u hu ≃* Pqr q (p ^ r) v hv) := by
  classical
  have _ := hr
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsCyclic (ZMod (p ^ r))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 r

  set K : Subgroup (ZMod (p ^ r))ˣ := (powMonoidHom q).ker with hK
  have hKcard_le : Nat.card K ≤ q := by
    rw [hK, IsCyclic.card_powMonoidHom_ker]
    exact Nat.gcd_le_right _ hq.pos
  have huK : u ∈ K := by
    rw [hK, MonoidHom.mem_ker]
    exact hu
  have hle : Subgroup.zpowers u ≤ K := Subgroup.zpowers_le.mpr huK
  have hKu : Subgroup.zpowers u = K := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, hou]
    exact hKcard_le

  have hvK : v ∈ K := by
    rw [hK, MonoidHom.mem_ker]
    exact hv
  have hvzp : v ∈ Subgroup.zpowers u := hKu ▸ hvK
  rw [mem_zpowers_iff_mem_range_orderOf, hou] at hvzp
  obtain ⟨c, hc_mem, hc⟩ := Finset.mem_image.mp hvzp
  have hc_lt : c < q := Finset.mem_range.mp hc_mem

  have hcne : c ≠ 0 := by
    intro h0
    have hv1 : v = 1 := by rw [← hc, h0, pow_zero]
    rw [hv1, orderOf_one] at hov
    exact hq.ne_one hov.symm

  have hgcd : Nat.gcd q c = 1 := by
    have hord : q / Nat.gcd q c = q := by
      have hpow : orderOf (u ^ c) = q := by rw [hc, hov]
      rw [orderOf_pow' (x := u) hcne, hou] at hpow
      exact hpow
    have hdvd : Nat.gcd q c ∣ q := Nat.gcd_dvd_left q c
    have hmul : q = q * Nat.gcd q c := by
      have h1 : q / Nat.gcd q c * Nat.gcd q c = q := Nat.div_mul_cancel hdvd
      rw [hord] at h1
      exact h1.symm
    have h2 : q * 1 = q * Nat.gcd q c := by rw [mul_one]; exact hmul
    exact (Nat.eq_of_mul_eq_mul_left hq.pos h2).symm
  have hcop : Nat.Coprime c q :=
    (Nat.coprime_comm).mpr (Nat.coprime_iff_gcd_eq_one.mpr hgcd)

  let cn : (ZMod q)ˣ := ZMod.unitOfCoprime c hcop
  have hcn : (cn : ZMod q) = (c : ZMod q) := ZMod.coe_unitOfCoprime c hcop
  have hcnval : (cn : ZMod q).val = c := by
    rw [hcn, ZMod.val_natCast_of_lt hc_lt]
  let τ : MulAut (Cyc q) := unitMulAut q cn
  have hτ_toAdd : ∀ g : Cyc q, Multiplicative.toAdd (τ g)
      = (cn : ZMod q) * Multiplicative.toAdd g := by
    intro g
    show Multiplicative.toAdd
        ((unitMulAut q cn) (Multiplicative.ofAdd (Multiplicative.toAdd g)))
      = (cn : ZMod q) * Multiplicative.toAdd g
    rw [unitMulAut_apply]
    rfl

  have hact : ∀ g : Cyc q,
      cyclicAction q (p ^ r) v hv g = cyclicAction q (p ^ r) u hu (τ g) := by
    intro g
    apply MulEquiv.ext
    intro a
    rw [cyclicAction_apply, cyclicAction_apply]
    have hkey : (v : ZMod (p ^ r)) ^ (Multiplicative.toAdd g).val
        = (u : ZMod (p ^ r)) ^ (Multiplicative.toAdd (τ g)).val := by
      have hL : (v : ZMod (p ^ r)) ^ (Multiplicative.toAdd g).val
          = (u : ZMod (p ^ r)) ^ (c * (Multiplicative.toAdd g).val) := by
        rw [← hc, Units.val_pow_eq_pow_val, pow_mul]
      have hmod : (Multiplicative.toAdd (τ g)).val
          ≡ c * (Multiplicative.toAdd g).val [MOD q] := by
        rw [hτ_toAdd, ZMod.val_mul, hcnval]
        exact Nat.mod_modEq _ _
      have hR : (u : ZMod (p ^ r)) ^ (Multiplicative.toAdd (τ g)).val
          = (u : ZMod (p ^ r)) ^ (c * (Multiplicative.toAdd g).val) := by
        have h := unit_pow_eq_pow_of_modEq (p ^ r) q
          (Multiplicative.toAdd (τ g)).val (c * (Multiplicative.toAdd g).val) u hu hmod
        rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, h]
      rw [hL, hR]
    rw [hkey]
  have hcomm : ∀ g : Cyc q,
      (cyclicAction q (p ^ r) v hv g).trans (MulEquiv.refl (Cyc (p ^ r)))
        = (MulEquiv.refl (Cyc (p ^ r))).trans
            (cyclicAction q (p ^ r) u hu (τ g)) := by
    intro g
    apply MulEquiv.ext
    intro a
    simpa using congrArg (fun f : MulAut (Cyc (p ^ r)) => f a) (hact g)
  exact ⟨(SemidirectProduct.congr (MulEquiv.refl (Cyc (p ^ r))) τ hcomm).symm⟩

end Qatlib.Papers.SemiDirectHSP04.MainResults.Proposition5
