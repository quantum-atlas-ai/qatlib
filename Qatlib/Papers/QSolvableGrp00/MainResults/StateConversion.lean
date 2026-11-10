/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Papers.QSolvableGrp00.MainResults.OrderFinding
set_option warningAsError false

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.QSolvableGrp00.MainResults.StateConversion

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.QSolvableGrp00.MainResults.OrderFinding

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

attribute [local instance] Classical.propDecidable

noncomputable def cosetState (H : Subgroup G) (g : G) : QState G :=
  fun x => uniformSubgroupState H (g⁻¹ * x)

theorem cosetState_apply (H : Subgroup G) (g x : G) :
    cosetState H g x =
      if g⁻¹ * x ∈ H then (((Real.sqrt (Nat.card ↥H) : ℝ)) : ℂ)⁻¹ else 0 := rfl

theorem cosetAmplitude_ne_zero (H : Subgroup G) :
    (((Real.sqrt (Nat.card ↥H) : ℝ)) : ℂ)⁻¹ ≠ 0 := by
  haveI : Nonempty ↥H := ⟨⟨1, H.one_mem⟩⟩
  have hpos : (0 : ℝ) < Nat.card ↥H := by exact_mod_cast Nat.card_pos
  have hsqrt : Real.sqrt (Nat.card ↥H) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  exact inv_ne_zero (Complex.ofReal_ne_zero.mpr hsqrt)

theorem cosetState_apply_self (H : Subgroup G) (g : G) :
    cosetState H g g = (((Real.sqrt (Nat.card ↥H) : ℝ)) : ℂ)⁻¹ := by
  rw [cosetState_apply]
  have h1 : g⁻¹ * g ∈ H := by rw [inv_mul_cancel]; exact H.one_mem
  rw [if_pos h1]

theorem cosetState_left_mul (H : Subgroup G) (a g : G) :
    cosetState H (a * g) = fun y => cosetState H g (a⁻¹ * y) := by
  funext y
  simp only [cosetState, mul_inv_rev]
  congr 1
  group

theorem normalized_cosetState (H : Subgroup G) (g : G) : Normalized (cosetState H g) := by
  unfold Normalized
  have h : ∑ x, ‖cosetState H g x‖ ^ 2
      = ∑ x, ‖uniformSubgroupState H x‖ ^ 2 := by
    refine Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ ?_
    intro x
    rfl
  rw [h]
  exact normalized_uniformSubgroupState H

theorem inner_cosetState_self (H : Subgroup G) (g : G) :
    Inner (cosetState H g) (cosetState H g) = 1 :=
  (normalized_iff_inner_self _).mp (normalized_cosetState H g)

theorem cosetState_congr_iff (H : Subgroup G) {g g' : G} :
    cosetState H g = cosetState H g' ↔ g⁻¹ * g' ∈ H := by
  constructor
  · intro hst
    have h1 : cosetState H g g = cosetState H g' g := by rw [hst]
    rw [cosetState_apply_self, cosetState_apply] at h1
    by_cases hmem : (g')⁻¹ * g ∈ H
    · have hinv : ((g')⁻¹ * g)⁻¹ ∈ H := H.inv_mem hmem
      simpa [mul_inv_rev] using hinv
    · rw [if_neg hmem] at h1
      exact (cosetAmplitude_ne_zero H h1).elim
  · intro hmem
    funext x
    rw [cosetState_apply, cosetState_apply]
    have hiff : g⁻¹ * x ∈ H ↔ (g')⁻¹ * x ∈ H := by
      constructor
      · intro hx
        have h2 : (g')⁻¹ * x = ((g')⁻¹ * g) * (g⁻¹ * x) := by group
        rw [h2]
        exact H.mul_mem (by simpa [mul_inv_rev] using H.inv_mem hmem) hx
      · intro hx
        have h2 : g⁻¹ * x = (g⁻¹ * g') * ((g')⁻¹ * x) := by group
        rw [h2]
        exact H.mul_mem hmem hx
    by_cases hx : g⁻¹ * x ∈ H
    · rw [if_pos hx, if_pos (hiff.mp hx)]
    · rw [if_neg hx, if_neg (fun h => hx (hiff.mpr h))]

theorem inner_cosetState_eq (H : Subgroup G) (g g' : G) :
    Inner (cosetState H g) (cosetState H g') =
      if g⁻¹ * g' ∈ H then 1 else 0 := by
  by_cases hmem : g⁻¹ * g' ∈ H
  · rw [if_pos hmem, (cosetState_congr_iff H).mpr hmem]
    exact inner_cosetState_self H g'
  · rw [if_neg hmem, inner_apply]
    refine Finset.sum_eq_zero fun x _ => ?_
    rcases Classical.em (g⁻¹ * x ∈ H) with hx | hx
    · have hx' : ¬((g')⁻¹ * x ∈ H) := by
        intro hc
        apply hmem
        have h2 : g⁻¹ * g' = (g⁻¹ * x) * ((g')⁻¹ * x)⁻¹ := by group
        rw [h2]
        exact H.mul_mem hx (H.inv_mem hc)
      rw [cosetState_apply, cosetState_apply, if_neg hx']
      simp
    · rw [cosetState_apply, if_neg hx]
      simp

noncomputable def leftMulState (a : G) (ψ : QState G) : QState G := fun y => ψ (a⁻¹ * y)

theorem leftMulState_cosetState (H : Subgroup G) (a g : G) :
    leftMulState a (cosetState H g) = cosetState H (a * g) := by
  funext y
  exact congrFun (cosetState_left_mul H a g).symm y

theorem cosetState_mul_mem (H : Subgroup G) (g : G) {x : G} (hx : x ∈ H) :
    cosetState H (g * x) = cosetState H g := by
  refine (cosetState_congr_iff H).mpr ?_
  have h : (g * x)⁻¹ * g = x⁻¹ := by group
  rw [h]
  exact H.inv_mem hx

theorem conj_pow_mem_of_mem_normalizer (H : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) (j : ℕ) {h : G} (hh : h ∈ H) :
    (g ^ j)⁻¹ * h * g ^ j ∈ H := by
  have hgpow : g ^ j ∈ Subgroup.normalizer (H : Set G) := by
    simpa using Subgroup.zpow_mem (Subgroup.normalizer (H : Set G)) hg (j : ℤ)
  have hmem : ∀ x : G, x ∈ H ↔ (g ^ j)⁻¹ * x * g ^ j ∈ H := by
    have := Subgroup.mem_normalizer_iff''.mp hgpow
    intro x
    exact this x
  exact (hmem h).mp hh

theorem leftMul_cosetState_of_mem_normalizer (H : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) (j a : ℕ) {h₀ : G} (hh₀ : h₀ ∈ H) :
    leftMulState (g ^ j * h₀) (cosetState H (g ^ a)) = cosetState H (g ^ (a + j)) := by
  rw [leftMulState_cosetState]

  have hconj : (g ^ a)⁻¹ * h₀ * g ^ a ∈ H := conj_pow_mem_of_mem_normalizer H hg a hh₀
  have hfac : g ^ j * h₀ * g ^ a = g ^ (a + j) * ((g ^ a)⁻¹ * h₀ * g ^ a) := by
    group
  rw [hfac, cosetState_mul_mem H _ hconj]

section RelOrder

theorem relOrder_exists (H : Subgroup G) (g : G) : ∃ n, 0 < n ∧ g ^ n ∈ H := by
  refine ⟨orderOf g, orderOf_pos g, ?_⟩
  rw [pow_orderOf_eq_one]
  exact H.one_mem

noncomputable def relOrder (H : Subgroup G) (g : G) : ℕ :=
  Nat.find (relOrder_exists H g)

theorem relOrder_spec (H : Subgroup G) (g : G) :
    0 < relOrder H g ∧ g ^ relOrder H g ∈ H :=
  Nat.find_spec (relOrder_exists H g)

theorem relOrder_pos (H : Subgroup G) (g : G) : 0 < relOrder H g :=
  (relOrder_spec H g).1

theorem pow_relOrder_mem (H : Subgroup G) (g : G) : g ^ relOrder H g ∈ H :=
  (relOrder_spec H g).2

theorem relOrder_min (H : Subgroup G) (g : G) {k : ℕ} (hk : 0 < k) (hmem : g ^ k ∈ H) :
    relOrder H g ≤ k :=
  Nat.find_min' (relOrder_exists H g) ⟨hk, hmem⟩

theorem pow_relOrder_mul_mem (H : Subgroup G) (g : G) (t : ℕ) :
    g ^ (relOrder H g * t) ∈ H := by
  rw [pow_mul]
  exact H.pow_mem (pow_relOrder_mem H g) t

theorem cosetState_pow_add_mul_eq (H : Subgroup G) (g : G) (n t : ℕ) :
    cosetState H (g ^ (n + relOrder H g * t)) = cosetState H (g ^ n) := by
  rw [pow_add]
  refine (cosetState_congr_iff H).mpr ?_
  have h : g ^ (relOrder H g * t) ∈ H := pow_relOrder_mul_mem H g t
  simpa [mul_inv_rev, mul_assoc] using H.inv_mem h

theorem cosetState_pow_add_mul_eq_of_eq (H : Subgroup G) (g : G) {r : ℕ}
    (hr : relOrder H g = r) (n t : ℕ) :
    cosetState H (g ^ (n + r * t)) = cosetState H (g ^ n) := by
  rw [← hr]
  exact cosetState_pow_add_mul_eq H g n t

end RelOrder

section Fourier

variable {r : ℕ} [NeZero r]

noncomputable def phaseState (H : Subgroup G) (g : G) (b : ZMod r) : QState G :=
  fun x => (((Real.sqrt (r : ℝ) : ℝ)) : ℂ)⁻¹ *
    ∑ a : ZMod r, ZMod.stdAddChar (a * b) * cosetState H (g ^ a.val) x

theorem zmod_val_add_nat (a : ZMod r) (j : ℕ) :
    (a + (j : ZMod r)).val = (a.val + j) % r := by
  rw [ZMod.val_add, ZMod.val_natCast]
  conv_rhs => rw [Nat.add_mod, Nat.mod_eq_of_lt (ZMod.val_lt a)]

theorem zmod_val_add_nat_eq (a : ZMod r) (j : ℕ) :
    a.val + j = (a + (j : ZMod r)).val + r * ((a.val + j) / r) := by
  rw [zmod_val_add_nat]
  exact (Nat.mod_add_div (a.val + j) r).symm

theorem cosetState_pow_val_add (H : Subgroup G) (g : G) (hr : r = relOrder H g)
    (a : ZMod r) (j : ℕ) :
    cosetState H (g ^ (a.val + j)) = cosetState H (g ^ (a + (j : ZMod r)).val) := by
  have hval := zmod_val_add_nat_eq (r := r) a j
  rw [hval]
  exact cosetState_pow_add_mul_eq_of_eq H g hr.symm _ _

theorem leftMul_phaseState_of_mem_normalizer (H : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) (hr : r = relOrder H g)
    (b : ZMod r) (j : ℕ) {h₀ : G} (hh₀ : h₀ ∈ H) :
    leftMulState (g ^ j * h₀) (phaseState H g b) =
      fun x => ZMod.stdAddChar (-((j : ZMod r) * b)) * phaseState H g b x := by
  funext x
  unfold leftMulState phaseState
  have hterm : ∀ a : ZMod r,
      ZMod.stdAddChar (a * b) * cosetState H (g ^ a.val) ((g ^ j * h₀)⁻¹ * x)
        = ZMod.stdAddChar (a * b) * cosetState H (g ^ (a + (j : ZMod r)).val) x := by
    intro a
    congr 1
    have h1 : cosetState H (g ^ a.val) ((g ^ j * h₀)⁻¹ * x)
        = cosetState H (g ^ (a.val + j)) x :=
      congrFun (leftMul_cosetState_of_mem_normalizer H hg j a.val hh₀) x
    rw [h1, cosetState_pow_val_add H g hr a j]
  rw [Finset.sum_congr rfl (fun a _ => hterm a)]

  have hreindex :
      (∑ a : ZMod r,
          ZMod.stdAddChar (a * b) * cosetState H (g ^ (a + (j : ZMod r)).val) x)
        = ∑ a' : ZMod r,
            ZMod.stdAddChar ((a' - (j : ZMod r)) * b) *
              cosetState H (g ^ a'.val) x := by
    refine Finset.sum_equiv (Equiv.addRight (j : ZMod r)) ?_ ?_
    · intro a
      simp
    · intro a _
      change ZMod.stdAddChar (a * b) * cosetState H (g ^ (a + (j : ZMod r)).val) x
        = ZMod.stdAddChar ((a + (j : ZMod r) - (j : ZMod r)) * b) *
            cosetState H (g ^ (a + (j : ZMod r)).val) x
      rw [add_sub_cancel_right]
  rw [hreindex]
  have hfactor : ∀ a' : ZMod r,
      ZMod.stdAddChar ((a' - (j : ZMod r)) * b) =
        ZMod.stdAddChar (a' * b) * ZMod.stdAddChar (-((j : ZMod r) * b)) := by
    intro a'
    rw [show (a' - (j : ZMod r)) * b = a' * b + (-((j : ZMod r) * b)) by ring,
      AddChar.map_add_eq_mul]
  rw [Finset.sum_congr rfl (fun a' _ => by rw [hfactor a'])]
  have hpull :
      (∑ a' : ZMod r,
          (ZMod.stdAddChar (a' * b) * ZMod.stdAddChar (-((j : ZMod r) * b))) *
            cosetState H (g ^ a'.val) x)
        = ZMod.stdAddChar (-((j : ZMod r) * b)) *
            ∑ a' : ZMod r, ZMod.stdAddChar (a' * b) * cosetState H (g ^ a'.val) x := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro a' _
    ring
  rw [hpull]
  ring

end Fourier

theorem conj_zpow_mem_of_mem_normalizer (H : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) (j : ℤ) {h : G} (hh : h ∈ H) :
    (g ^ j)⁻¹ * h * g ^ j ∈ H := by
  have hgpow : g ^ j ∈ Subgroup.normalizer (H : Set G) :=
    Subgroup.zpow_mem (Subgroup.normalizer (H : Set G)) hg j
  exact (Subgroup.mem_normalizer_iff''.mp hgpow h).mp hh

theorem mem_sup_zpowers_rep (H : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) {x : G}
    (hx : x ∈ H ⊔ Subgroup.zpowers g) :
    ∃ (j : ℤ) (h : G), h ∈ H ∧ x = g ^ j * h := by
  let P : Subgroup G :=
    { carrier := { x | ∃ (j : ℤ) (h : G), h ∈ H ∧ x = g ^ j * h }
      one_mem' := ⟨0, 1, H.one_mem, by simp⟩
      mul_mem' := by
        rintro x1 x2 ⟨j1, h1, hh1, e1⟩ ⟨j2, h2, hh2, e2⟩
        refine ⟨j1 + j2, (g ^ j2)⁻¹ * h1 * g ^ j2 * h2, ?_, ?_⟩
        · exact H.mul_mem (conj_zpow_mem_of_mem_normalizer H hg j2 hh1) hh2
        · rw [e1, e2, zpow_add]; group
      inv_mem' := by
        rintro x ⟨j, h, hh, e⟩
        refine ⟨-j, g ^ j * h⁻¹ * (g ^ j)⁻¹, ?_, ?_⟩
        · have hcj := conj_zpow_mem_of_mem_normalizer H hg (-j) (H.inv_mem hh)
          simpa [zpow_neg] using hcj
        · rw [e]; group }
  have hHP : H ≤ P := fun y hy => ⟨0, y, hy, by simp⟩
  have hGP : Subgroup.zpowers g ≤ P := by
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ⟨j, 1, H.one_mem, by simp⟩
  exact sup_le hHP hGP hx

theorem mem_sup_zpowers_rep_mod (H : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) (r : ℕ) (hr : r = relOrder H g)
    {x : G} (hx : x ∈ H ⊔ Subgroup.zpowers g) :
    ∃ (a : ZMod r) (h : G), h ∈ H ∧ x = g ^ a.val * h := by
  obtain ⟨j, h, hh, rfl⟩ := mem_sup_zpowers_rep H hg hx
  have hrpos : 0 < r := hr.symm ▸ relOrder_pos H g
  haveI : NeZero r := ⟨hrpos.ne'⟩
  set s : ℤ := j % (r : ℤ) with hsdef
  have hsnonneg : 0 ≤ s := Int.emod_nonneg j (by exact_mod_cast hrpos.ne')
  have hslt : s < (r : ℤ) := by
    rw [hsdef]; exact Int.emod_lt_of_pos j (by exact_mod_cast hrpos)
  set aN : ℕ := s.toNat with haNdef
  have haN : (aN : ℤ) = s := Int.toNat_of_nonneg hsnonneg
  have haNlt : aN < r := by
    have : (aN : ℤ) < (r : ℤ) := by rw [haN]; exact hslt
    exact_mod_cast this
  have haNs : (aN : ℤ) = j % (r : ℤ) := by rw [haN, hsdef]
  have hdecomp : j = (aN : ℤ) + (r : ℤ) * (j / (r : ℤ)) := by
    have h := Int.emod_add_mul_ediv j (r : ℤ)
    rw [haNs]; exact h.symm
  have hpow : g ^ j = g ^ aN * (g ^ r) ^ (j / (r : ℤ)) := by
    conv_lhs => rw [hdecomp]
    rw [zpow_add, zpow_mul]
    simp only [zpow_natCast]
  have hgr : g ^ r ∈ H := by
    rw [hr]; exact pow_relOrder_mem H g
  refine ⟨(aN : ZMod r), (g ^ r) ^ (j / (r : ℤ)) * h, H.mul_mem (H.zpow_mem hgr _) hh, ?_⟩
  have hval : ((aN : ZMod r)).val = aN := ZMod.val_cast_of_lt haNlt
  rw [hval, hpow]
  group

noncomputable def cosetRep (H : Subgroup G) (g : G) (r : ℕ) :
    ZMod r × ↥H → ↥(H ⊔ Subgroup.zpowers g) :=
  fun p => ⟨g ^ p.1.val * (p.2 : G), by
    have h1 : g ^ p.1.val ∈ Subgroup.zpowers g :=
      Subgroup.mem_zpowers_iff.mpr ⟨(p.1.val : ℤ), by simp⟩
    have h2 : (p.2 : G) ∈ H := p.2.2
    exact show g ^ p.1.val * (p.2 : G) ∈ H ⊔ Subgroup.zpowers g from by
      rw [sup_comm]; exact Subgroup.mul_mem_sup h1 h2⟩

theorem cosetRep_injective (H : Subgroup G) {g : G} (r : ℕ) (hr : r = relOrder H g) :
    Function.Injective (cosetRep H g r) := by
  have hrpos : 0 < r := hr.symm ▸ relOrder_pos H g
  haveI : NeZero r := ⟨hrpos.ne'⟩
  rintro ⟨a, h⟩ ⟨a', h'⟩ heq
  simp only [cosetRep, Subtype.mk.injEq] at heq
  have hmemH : ∀ {d : ℕ}, 0 < d → d < r → g ^ d ∉ H := by
    intro d hd0 hdr hdH
    have hle : relOrder H g ≤ d := relOrder_min H g hd0 hdH
    rw [← hr] at hle
    omega
  have hmem : (h : G) * (h' : G)⁻¹ ∈ H := H.mul_mem h.2 (H.inv_mem h'.2)
  have key : g ^ a.val * ((h : G) * (h' : G)⁻¹) = g ^ a'.val := by
    have hc := congrArg (fun t => t * (h' : G)⁻¹) heq
    simpa [mul_assoc] using hc
  by_cases hle : a.val ≤ a'.val
  · have hpow : g ^ a'.val = g ^ a.val * g ^ (a'.val - a.val) := by
      rw [← pow_add, Nat.add_sub_of_le hle]
    have hd : g ^ (a'.val - a.val) = (h : G) * (h' : G)⁻¹ := by
      have hkey := key
      rw [hpow] at hkey
      exact (mul_left_cancel hkey).symm
    by_cases hd0 : a'.val - a.val = 0
    · have hae : a = a' := by
        apply ZMod.val_injective
        omega
      subst a'
      have hh : (h : G) = (h' : G) := mul_left_cancel heq
      exact Prod.ext rfl (Subtype.ext hh)
    · have hpos : 0 < a'.val - a.val := Nat.pos_of_ne_zero hd0
      have hlt' : a'.val - a.val < r := by
        have : a'.val < r := ZMod.val_lt a'
        omega
      have : g ^ (a'.val - a.val) ∈ H := by rw [hd]; exact hmem
      exact (hmemH hpos hlt' this).elim
  · have hlt : a'.val < a.val := by omega
    have hpow : g ^ a.val = g ^ a'.val * g ^ (a.val - a'.val) := by
      rw [← pow_add, Nat.add_sub_of_le hlt.le]
    have key2 : g ^ (a.val - a'.val) * ((h : G) * (h' : G)⁻¹) = 1 := by
      have hkey := key
      rw [hpow, mul_assoc] at hkey
      have h1 : g ^ a'.val * (g ^ (a.val - a'.val) * ((h : G) * (h' : G)⁻¹)) =
          g ^ a'.val * 1 := by
        rw [hkey, mul_one]
      exact mul_left_cancel h1
    have hd : g ^ (a.val - a'.val) = ((h : G) * (h' : G)⁻¹)⁻¹ := by
      have h := congrArg (fun t => t * ((h : G) * (h' : G)⁻¹)⁻¹) key2
      simpa [mul_assoc] using h
    have hpos : 0 < a.val - a'.val := Nat.sub_pos_of_lt hlt
    have hlt' : a.val - a'.val < r := by
      have : a.val < r := ZMod.val_lt a
      omega
    have : g ^ (a.val - a'.val) ∈ H := by
      rw [hd]; exact H.inv_mem hmem
    exact (hmemH hpos hlt' this).elim

theorem cosetRep_surjective (H : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) (r : ℕ) (hr : r = relOrder H g) :
    Function.Surjective (cosetRep H g r) := by
  intro x
  obtain ⟨a, h, hh, hx⟩ := mem_sup_zpowers_rep_mod H hg r hr x.2
  refine ⟨(a, ⟨h, hh⟩), ?_⟩
  apply Subtype.ext
  simp only [cosetRep]
  exact hx.symm

theorem card_sup_zpowers (H : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    Nat.card ↥(H ⊔ Subgroup.zpowers g) = relOrder H g * Nat.card ↥H := by
  set r := relOrder H g with hr
  have hrpos : 0 < r := hr.symm ▸ relOrder_pos H g
  haveI : NeZero r := ⟨hrpos.ne'⟩
  have e : ZMod r × ↥H ≃ ↥(H ⊔ Subgroup.zpowers g) :=
    Equiv.ofBijective (cosetRep H g r)
      ⟨cosetRep_injective H r hr.symm, cosetRep_surjective H hg r hr.symm⟩
  rw [← Nat.card_congr e, Nat.card_prod]
  have hz : Nat.card (ZMod r) = r := by
    rw [Nat.card_eq_fintype_card]; exact ZMod.card r
  rw [hz]

end Qatlib.Papers.QSolvableGrp00.MainResults.StateConversion
