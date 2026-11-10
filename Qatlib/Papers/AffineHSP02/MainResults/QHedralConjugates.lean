/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AffineHSP02.MainResults.QHedralGroup

set_option autoImplicit false

namespace Qatlib.Papers.AffineHSP02.MainResults

namespace QHG

variable {p q : ℕ} (M : MultFamily p q)

def multiplier : QHG M := ⟨0, 1⟩

def translation (b : ZMod p) : QHG M := ⟨b, 0⟩

@[simp] theorem multiplier_x : (multiplier M).x = 0 := rfl

@[simp] theorem multiplier_s : (multiplier M).s = 1 := rfl

@[simp] theorem translation_x (b : ZMod p) : (translation M b).x = b := rfl

@[simp] theorem translation_s (b : ZMod p) : (translation M b).s = 0 := rfl

@[simp] theorem inv_translation (b : ZMod p) :
    (translation M b)⁻¹ = translation M (-b) := by
  ext <;> simp [translation, M.m_zero]

theorem zpow_multiplier (t : ℤ) :
    (multiplier M) ^ t = ⟨0, (t : ZMod q)⟩ := by
  induction t using Int.induction_on with
  | zero => ext <;> simp [multiplier]
  | succ n ih =>
    rw [zpow_add_one, ih]
    ext
    · simp
    · simp only [mul_s, multiplier_s]
      push_cast
      ring
  | pred n ih =>
    rw [zpow_sub_one, ih]
    ext
    · simp
    · simp only [mul_s, inv_s, multiplier_s]
      push_cast
      ring

theorem conj_translation_multiplier (b : ZMod p) (t : ℤ) :
    translation M b * (multiplier M) ^ t * (translation M b)⁻¹
      = ⟨(1 - (M.m (t : ZMod q) : ZMod p)) * b, (t : ZMod q)⟩ := by
  rw [zpow_multiplier]
  ext
  · simp [M.m_zero, Units.val_one]
    ring
  · simp [translation]

theorem conj_translation (b : ZMod p) (g : QHG M) :
    translation M b * g * (translation M b)⁻¹
      = ⟨g.x + (1 - (M.m g.s : ZMod p)) * b, g.s⟩ := by
  rw [inv_translation]
  ext
  · simp [translation]
    ring
  · simp [translation]

theorem conj_translation_eq_of_ne_one [Fact p.Prime] (g : QHG M)
    (hs : (M.m g.s : ZMod p) ≠ 1) :
    ∃ b : ZMod p, translation M b * g * (translation M b)⁻¹ = ⟨0, g.s⟩ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hne : (1 - (M.m g.s : ZMod p)) ≠ 0 := by
    intro h
    exact hs (sub_eq_zero.mp h).symm
  refine ⟨-((1 - (M.m g.s : ZMod p))⁻¹ * g.x), ?_⟩
  rw [conj_translation]
  ext
  · show g.x + (1 - (M.m g.s : ZMod p)) * (-((1 - (M.m g.s : ZMod p))⁻¹ * g.x)) = 0
    rw [show (1 - (M.m g.s : ZMod p)) * (-((1 - (M.m g.s : ZMod p))⁻¹ * g.x))
        = -g.x by
      rw [mul_neg]
      congr 1
      rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]]
    ring
  · rfl

theorem exists_conjugate_zpowers_le_multiplierSubgroup [NeZero q] [Fact p.Prime]
    (g : QHG M) (hs : (M.m g.s : ZMod p) ≠ 1) :
    ∃ b : ZMod p,
      Subgroup.map (MulAut.conj (translation M b) : QHG M →* QHG M)
        (Subgroup.zpowers g) ≤ Subgroup.zpowers (multiplier M) := by
  obtain ⟨b, hb⟩ := conj_translation_eq_of_ne_one M g hs
  refine ⟨b, ?_⟩
  intro y hy
  rw [Subgroup.mem_map] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  rw [Subgroup.mem_zpowers_iff] at hz
  obtain ⟨t, rfl⟩ := hz
  change (MulAut.conj (translation M b)) (g ^ t) ∈ Subgroup.zpowers (multiplier M)
  rw [map_zpow]
  have hbg : (MulAut.conj (translation M b)) g = ⟨0, g.s⟩ := by
    rw [MulAut.conj_apply]
    exact hb
  rw [hbg]
  have hgs : (⟨0, g.s⟩ : QHG M) = (multiplier M) ^ (g.s.val : ℤ) := by
    rw [zpow_multiplier]
    congr 1
    rw [Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]
  rw [hgs, ← zpow_mul]
  exact Subgroup.zpow_mem_zpowers _ _

def conjugate (b : ZMod p) : Subgroup (QHG M) :=
  (Subgroup.zpowers (multiplier M)).map
    (MulAut.conj (translation M b) : QHG M →* QHG M)

theorem mem_conjugate_iff [NeZero q] (b : ZMod p) (x : QHG M) :
    x ∈ conjugate M b ↔
      ∃ s : ZMod q, x = ⟨(1 - (M.m s : ZMod p)) * b, s⟩ := by
  unfold conjugate
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_zpowers_iff] at hy
    obtain ⟨t, rfl⟩ := hy
    refine ⟨(t : ZMod q), ?_⟩
    change (MulAut.conj (translation M b)) (multiplier M ^ t)
      = ⟨(1 - (M.m (t : ZMod q) : ZMod p)) * b, (t : ZMod q)⟩
    rw [MulAut.conj_apply, conj_translation_multiplier]
  · rintro ⟨s, rfl⟩
    refine ⟨(multiplier M) ^ (s.val : ℤ), Subgroup.zpow_mem_zpowers _ _, ?_⟩
    change (MulAut.conj (translation M b)) (multiplier M ^ (s.val : ℤ))
      = ⟨(1 - (M.m s : ZMod p)) * b, s⟩
    rw [MulAut.conj_apply, conj_translation_multiplier]
    have hs : ((s.val : ℤ) : ZMod q) = s := by
      rw [Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id]
    rw [hs]

theorem conjugate_injective [NeZero q] [Fact p.Prime] (h1 : M.m 1 ≠ 1) :
    Function.Injective (conjugate M) := by
  intro b b' hbb'
  by_cases hb : b = b'
  · exact hb
  exfalso
  have hmem : (⟨(1 - (M.m (1 : ZMod q) : ZMod p)) * b, (1 : ZMod q)⟩ : QHG M)
      ∈ conjugate M b := by
    rw [mem_conjugate_iff]
    exact ⟨1, rfl⟩
  rw [hbb'] at hmem
  rw [mem_conjugate_iff] at hmem
  obtain ⟨s, hs⟩ := hmem
  have hs1 : s = 1 := by
    have := congrArg QHG.s hs
    simpa using this.symm
  subst hs1
  have hx : (1 - (M.m (1 : ZMod q) : ZMod p)) * b
      = (1 - (M.m (1 : ZMod q) : ZMod p)) * b' := by
    have := congrArg QHG.x hs
    simpa using this
  have hne : (1 - (M.m (1 : ZMod q) : ZMod p)) ≠ 0 := by
    intro h
    have hx1 : (M.m (1 : ZMod q) : ZMod p) = 1 := (sub_eq_zero.mp h).symm
    exact h1 (Units.val_injective hx1)
  exact hb (mul_left_cancel₀ hne hx)

def multiplierSubgroup : Subgroup (QHG M) := Subgroup.zpowers (multiplier M)

theorem card_multiplierSubgroup [NeZero q] :
    Nat.card (multiplierSubgroup M) = q := by
  rw [multiplierSubgroup, Nat.card_zpowers]
  simpa [multiplier] using orderOf_multiplier (M := M)

theorem card_conjugate [NeZero q] (b : ZMod p) :
    Nat.card (conjugate M b) = q := by
  unfold conjugate
  rw [← Nat.card_congr (Subgroup.equivMapOfInjective (Subgroup.zpowers (multiplier M))
    (MulAut.conj (translation M b) : QHG M →* QHG M)
    (MulAut.conj (translation M b)).injective).toEquiv]
  exact card_multiplierSubgroup M

end QHG

end Qatlib.Papers.AffineHSP02.MainResults
