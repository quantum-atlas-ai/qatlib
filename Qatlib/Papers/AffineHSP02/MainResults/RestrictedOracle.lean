/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Index
import Mathlib.Tactic
import Qatlib.Papers.AffineHSP02.MainResults.QHedralConjugates
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.AffineHSP02.MainResults

section Abstract

variable {G S : Type*} [Group G] {n : ℕ}

def restrictedOracle (f : G → S) (φ : G →* Multiplicative (ZMod n)) (x : G) :
    S × Multiplicative (ZMod n) :=
  (f x, φ x)

theorem restrictedOracle_constant {H : Subgroup G} {φ : G →* Multiplicative (ZMod n)}
    {f : G → S} (hconst : ∀ (k g : G), k ∈ H → f (k * g) = f g) :
    ∀ (k : G), k ∈ H ⊓ φ.ker → ∀ g : G,
      restrictedOracle f φ (k * g) = restrictedOracle f φ g := by
  intro k hk g
  have hkH : k ∈ H := hk.1
  have hkker : φ k = 1 := MonoidHom.mem_ker.mp hk.2
  apply Prod.ext
  · exact hconst k g hkH
  · change φ (k * g) = φ g
    rw [map_mul, hkker, one_mul]

theorem restrictedOracle_separates {H : Subgroup G} {φ : G →* Multiplicative (ZMod n)}
    {f : G → S} (hsep : ∀ (k g : G), f (k * g) = f g → k ∈ H) :
    ∀ (k g : G), restrictedOracle f φ (k * g) = restrictedOracle f φ g →
      k ∈ H ⊓ φ.ker := by
  intro k g h
  constructor
  · exact hsep k g (congrArg Prod.fst h)
  · change φ k = 1
    have h1 : φ (k * g) = φ g := congrArg Prod.snd h
    rw [map_mul] at h1
    exact (mul_right_cancel_iff (a := φ g)).mp (by simpa using h1)

theorem restrictedOracle_eq_iff {H : Subgroup G} {φ : G →* Multiplicative (ZMod n)}
    {f : G → S} (hconst : ∀ (k g : G), k ∈ H → f (k * g) = f g)
    (hsep : ∀ (k g : G), f (k * g) = f g → k ∈ H) (k g : G) :
    restrictedOracle f φ (k * g) = restrictedOracle f φ g ↔ k ∈ H ⊓ φ.ker :=
  ⟨restrictedOracle_separates hsep k g, fun hk => restrictedOracle_constant hconst k hk g⟩

end Abstract

namespace QHG

variable {p q : ℕ} [NeZero q] (M : MultFamily p q)

def powHom (r : ℕ) : QHG M →* Multiplicative (ZMod q) where
  toFun g := Multiplicative.ofAdd ((r : ZMod q) * g.s)
  map_one' := by
    change Multiplicative.ofAdd ((r : ZMod q) * (0 : ZMod q)) = 1
    rw [mul_zero, ofAdd_zero]
  map_mul' := by
    intro a b
    change Multiplicative.ofAdd ((r : ZMod q) * (a.s + b.s))
      = Multiplicative.ofAdd ((r : ZMod q) * a.s) * Multiplicative.ofAdd ((r : ZMod q) * b.s)
    rw [mul_add, ofAdd_add]

def powerKernel (r : ℕ) : Subgroup (QHG M) := (powHom M r).ker

omit [NeZero q] in

theorem mem_powerKernel_iff (r : ℕ) (g : QHG M) :
    g ∈ powerKernel M r ↔ (r : ZMod q) * g.s = 0 := by
  rw [powerKernel, MonoidHom.mem_ker]
  change Multiplicative.ofAdd ((r : ZMod q) * g.s) = 1 ↔ _
  rw [ofAdd_eq_one]

omit [NeZero q] in

theorem powerKernel_normal (r : ℕ) : (powerKernel M r).Normal := by
  rw [powerKernel]
  exact MonoidHom.normal_ker (powHom M r)

theorem mem_multiplierSubgroup_iff (x : QHG M) :
    x ∈ multiplierSubgroup M ↔ ∃ s : ZMod q, x = ⟨0, s⟩ := by
  rw [multiplierSubgroup, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨(t : ZMod q), by rw [zpow_multiplier]⟩
  · rintro ⟨s, rfl⟩
    refine ⟨(s.val : ℤ), ?_⟩
    rw [zpow_multiplier]
    have hs : ((s.val : ℤ) : ZMod q) = s := by
      rw [Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]
    rw [hs]

omit [NeZero q] in

theorem pow_shiftKernel (m k : ℕ) :
    (⟨0, (m : ZMod q)⟩ : QHG M) ^ k = ⟨0, (k : ZMod q) * (m : ZMod q)⟩ := by
  induction k with
  | zero => ext <;> simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext
    · simp
    · simp only [mul_s]
      push_cast
      ring

def shiftHom (m : ℕ) : Multiplicative (ZMod q) →* QHG M where
  toFun u := ⟨0, Multiplicative.toAdd u * (m : ZMod q)⟩
  map_one' := by
    change (⟨0, (0 : ZMod q) * (m : ZMod q)⟩ : QHG M) = 1
    ext <;> simp
  map_mul' := by
    intro a b
    ext
    · simp
    · have h : Multiplicative.toAdd (a * b)
          = Multiplicative.toAdd a + Multiplicative.toAdd b := rfl
      rw [h]
      rw [show (⟨0, Multiplicative.toAdd a * (m : ZMod q)⟩ : QHG M)
            * ⟨0, Multiplicative.toAdd b * (m : ZMod q)⟩
          = ⟨0, Multiplicative.toAdd a * (m : ZMod q)
              + Multiplicative.toAdd b * (m : ZMod q)⟩ from by ext <;> simp]
      ring

omit [NeZero q] in

theorem ofAdd_zpow_one (t : ℤ) :
    (Multiplicative.ofAdd (1 : ZMod q) : Multiplicative (ZMod q)) ^ t
      = Multiplicative.ofAdd ((t : ZMod q)) := by
  rw [← ofAdd_zsmul]
  congr 1
  rw [zsmul_eq_mul, mul_one]

omit [NeZero q] in

theorem zpow_shiftKernel (m : ℕ) (t : ℤ) :
    (⟨0, (m : ZMod q)⟩ : QHG M) ^ t = ⟨0, (t : ZMod q) * (m : ZMod q)⟩ := by
  have h1 : (⟨0, (m : ZMod q)⟩ : QHG M)
      = shiftHom M m (Multiplicative.ofAdd (1 : ZMod q)) := by
    ext <;> simp [shiftHom]
  rw [h1, ← map_zpow, ofAdd_zpow_one]
  rfl

theorem exists_mul_of_smul_eq_zero (r m : ℕ) (hq : q = r * m) (_hm : 0 < m)
    (s : ZMod q) (hs : (r : ZMod q) * s = 0) :
    ∃ u : ℕ, s = (m : ZMod q) * (u : ZMod q) := by
  subst hq
  have hrpos : 0 < r := by
    by_contra h
    have hr0 : r = 0 := Nat.eq_zero_of_not_pos h
    subst hr0
    have hne : (0 * m : ℕ) ≠ 0 := NeZero.ne (0 * m)
    simp at hne
  have hsv : ((s.val : ℕ) : ZMod (r * m)) = s := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  have hz : ((r * s.val : ℕ) : ZMod (r * m)) = 0 := by
    rw [Nat.cast_mul]
    rw [← hsv] at hs
    exact hs
  have hdiv : r * m ∣ r * s.val := (ZMod.natCast_eq_zero_iff _ _).mp hz
  have hmdiv : m ∣ s.val := Nat.dvd_of_mul_dvd_mul_left hrpos hdiv
  refine ⟨s.val / m, ?_⟩
  have hcalc : (m : ZMod (r * m)) * ((s.val / m : ℕ) : ZMod (r * m))
      = ((s.val : ℕ) : ZMod (r * m)) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hmdiv]
  rw [hcalc, hsv]

theorem multiplier_inter_powerKernel (r m : ℕ) (hq : q = r * m) (hm : 0 < m) :
    multiplierSubgroup M ⊓ powerKernel M r
      = Subgroup.zpowers ((⟨0, (m : ZMod q)⟩ : QHG M)) := by
  ext x
  rw [Subgroup.mem_inf, mem_multiplierSubgroup_iff, mem_powerKernel_iff]
  constructor
  · rintro ⟨⟨s, rfl⟩, hs⟩
    obtain ⟨u, hu⟩ := exists_mul_of_smul_eq_zero r m hq hm s hs
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨(u : ℤ), ?_⟩
    rw [zpow_shiftKernel, hu]
    congr 1
    rw [Int.cast_natCast]
    exact mul_comm ((u : ℕ) : ZMod q) (m : ZMod q)
  · intro hx
    rw [Subgroup.mem_zpowers_iff] at hx
    obtain ⟨t, rfl⟩ := hx
    rw [zpow_shiftKernel]
    constructor
    · exact ⟨(t : ZMod q) * (m : ZMod q), rfl⟩
    · change (r : ZMod q) * ((t : ZMod q) * (m : ZMod q)) = 0
      have hcast : ((r : ZMod q)) * (m : ZMod q) = (q : ZMod q) := by
        rw [← Nat.cast_mul, hq]
      rw [← mul_assoc, mul_comm (r : ZMod q) (t : ZMod q), mul_assoc, hcast,
        ZMod.natCast_self, mul_zero]

omit [NeZero q] in

theorem orderOf_shiftKernel (m : ℕ) :
    orderOf (⟨0, (m : ZMod q)⟩ : QHG M) = addOrderOf ((m : ZMod q)) := by
  apply Nat.dvd_antisymm
  · rw [orderOf_dvd_iff_pow_eq_one, pow_shiftKernel]
    have h : addOrderOf ((m : ZMod q)) • (m : ZMod q) = 0 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.mp dvd_rfl
    rw [nsmul_eq_mul] at h
    ext
    · simp
    · simpa using h
  · rw [addOrderOf_dvd_iff_nsmul_eq_zero, nsmul_eq_mul]
    have h := pow_orderOf_eq_one (⟨0, (m : ZMod q)⟩ : QHG M)
    rw [pow_shiftKernel] at h
    have h2 := congrArg QHG.s h
    simpa using h2

theorem orderOf_shift (s : ZMod q) :
    orderOf (⟨0, s⟩ : QHG M) = addOrderOf s := by
  have hs : ((s.val : ℕ) : ZMod q) = s := by
    rw [ZMod.natCast_val, ZMod.cast_id]
  rw [← hs]
  exact orderOf_shiftKernel M s.val

theorem orderOf_eq_addOrderOf_of_mult_ne_one [Fact p.Prime] (g : QHG M)
    (hs : (M.m g.s : ZMod p) ≠ 1) :
    orderOf g = addOrderOf (g.s) := by
  obtain ⟨b, hb⟩ := conj_translation_eq_of_ne_one M g hs
  have hbg : (MulAut.conj (translation M b)) g = ⟨0, g.s⟩ := by
    rw [MulAut.conj_apply]
    exact hb
  have h := MulEquiv.orderOf_eq (MulAut.conj (translation M b)) g
  rw [hbg, orderOf_shift] at h
  exact h.symm

theorem orderOf_dvd_of_mult_ne_one [Fact p.Prime] (g : QHG M)
    (hs : (M.m g.s : ZMod p) ≠ 1) :
    orderOf g ∣ q := by
  rw [orderOf_eq_addOrderOf_of_mult_ne_one M g hs]
  have h := addOrderOf_dvd_natCard (g.s)
  rwa [Nat.card_zmod] at h

theorem card_multiplier_inter_powerKernel (r m : ℕ) (hq : q = r * m) (hm : 0 < m) :
    Nat.card ↥(multiplierSubgroup M ⊓ powerKernel M r) = r := by
  rw [multiplier_inter_powerKernel M r m hq hm, Nat.card_zpowers, orderOf_shiftKernel,
    ZMod.addOrderOf_coe m (NeZero.ne q)]
  have hgcd : q.gcd m = m := by
    rw [hq, Nat.gcd_comm, Nat.gcd_eq_left (dvd_mul_left m r)]
  rw [hgcd, hq, Nat.mul_div_cancel r hm]

end QHG

end Qatlib.Papers.AffineHSP02.MainResults
