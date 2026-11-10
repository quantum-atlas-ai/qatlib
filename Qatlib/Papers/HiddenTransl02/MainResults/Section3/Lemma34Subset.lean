/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic
import Qatlib.Papers.HiddenTransl02.MainResults.Section3.HiddenTranslationElementaryAbelian
import Qatlib.Papers.HiddenTransl02.MainResults.Section3.LineLemmaPoly
import Qatlib.Papers.HiddenTransl02.MainResults.Section3.Lemma34Ratio
import Qatlib.Papers.HiddenTransl02.MainResults.Section3.Prop33Span
import Mathlib.Tactic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option warningAsError false
noncomputable section

namespace Qatlib.Papers.HiddenTransl02.MainResults.Section3

open MvPolynomial Finset

attribute [local instance] Classical.propDecidable

variable {n p : ℕ}

theorem dotU_add_line (u y : Fin n → ZMod p) (hyu : dotU u y = 1)
    (t : Fin n → ZMod p) (a : ZMod p) :
    dotU u (t + a • y) = dotU u t + a := by
  rw [map_add, dotU_smul, hyu, mul_one]

theorem projAlong_add_line (y : Fin n → ZMod p) (i : Fin n)
    (hπ : projAlong y i y = 1) (t : Fin n → ZMod p) (a : ZMod p) :
    projAlong y i (t + a • y) = projAlong y i t + a := by
  rw [map_add, projAlong_smul, hπ, mul_one]

variable [Fintype (ZMod p)]

def TZero (y : Fin n → ZMod p) (i : Fin n) : Finset (Fin n → ZMod p) :=
  univ.filter (fun t => projAlong y i t = 0)

def SNonzero (u : Fin n → ZMod p)
    (W : Submodule (ZMod p) (MvPolynomial (Fin n) (ZMod p))) :
    Finset (Fin n → ZMod p) :=
  univ.filter (fun x => lin x ^ (p - 1) ∈ W ∧ dotU u x ≠ 0)

def aZero (u : Fin n → ZMod p) (t : Fin n → ZMod p) : ZMod p :=
  -dotU u t

theorem VSet_one_card_eq_tzero (hp : p.Prime) (u y : Fin n → ZMod p) {i : Fin n}
    (hi : y i ≠ 0) (hyu : dotU u y = 1) : (VSet u 1).card = (TZero y i).card := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hπ : projAlong y i y = 1 := projAlong_self hp hi
  have hcard := Finset.card_nbij'
    (s := VSet u 1) (t := TZero y i)
    (i := fun x => x - projAlong y i x • y)
    (j := fun t => t + (1 - dotU u t) • y)
    (by
      intro x hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show projAlong y i (x - projAlong y i x • y) = 0
      rw [map_sub, projAlong_smul, hπ, mul_one, sub_self])
    (by
      intro t ht
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show dotU u (t + (1 - dotU u t) • y) = 1
      rw [dotU_add_line u y hyu]
      ring)
    (by
      intro x hx
      have hx1 : dotU u x = 1 := (Finset.mem_filter.mp hx).2
      have hb : 1 - dotU u (x - projAlong y i x • y) = projAlong y i x := by
        rw [map_sub, dotU_smul, hyu, mul_one, hx1]
        ring
      show x - projAlong y i x • y + (1 - dotU u (x - projAlong y i x • y)) • y = x
      rw [hb]
      exact sub_add_cancel x (projAlong y i x • y))
    (by
      intro t ht
      have ht0 : projAlong y i t = 0 := (Finset.mem_filter.mp ht).2
      have hb : projAlong y i (t + (1 - dotU u t) • y) = 1 - dotU u t := by
        rw [projAlong_add_line y i hπ, ht0, zero_add]
      show t + (1 - dotU u t) • y - projAlong y i (t + (1 - dotU u t) • y) • y = t
      rw [hb]
      exact add_sub_cancel_right t ((1 - dotU u t) • y))
  exact hcard

set_option maxHeartbeats 1000000 in

theorem SNonzero_card_le (hp : p.Prime) (u y : Fin n → ZMod p) {i : Fin n}
    (hi : y i ≠ 0) (hyu : dotU u y = 1)
    (W : Submodule (ZMod p) (MvPolynomial (Fin n) (ZMod p)))
    (hyR : lin y ^ (p - 1) ∉ W)
    (hV0 : ∀ t : Fin n → ZMod p, dotU u t = 0 → lin t ^ (p - 1) ∈ W) :
    (SNonzero u W).card ≤ (TZero y i).card * (p - 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hπ : projAlong y i y = 1 := projAlong_self hp hi
  have hsum := Finset.card_eq_sum_card_fiberwise
    (M := Fin n → ZMod p) (ι := Fin n → ZMod p)
    (s := SNonzero u W) (t := TZero y i)
    (f := fun x => x - projAlong y i x • y)
    (by
      intro x hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show projAlong y i (x - projAlong y i x • y) = 0
      rw [map_sub, projAlong_smul, hπ, mul_one, sub_self])
  rw [hsum]
  have hbound : ∀ t ∈ TZero y i,
      ((SNonzero u W).filter (fun x => x - projAlong y i x • y = t)).card ≤ p - 2 := by
    intro t ht
    have ht0 : projAlong y i t = 0 := (Finset.mem_filter.mp ht).2
    have hfib : ((SNonzero u W).filter (fun x => x - projAlong y i x • y = t)).card
        = ((goodScalars y W t).erase (aZero u t)).card := by
      have hbij := Finset.card_nbij'
        (s := (goodScalars y W t).erase (aZero u t))
        (t := (SNonzero u W).filter (fun x => x - projAlong y i x • y = t))
        (i := fun a => t + a • y) (j := fun x => projAlong y i x)
        (by
          intro a ha
          obtain ⟨hane, hag⟩ := Finset.mem_erase.mp ha
          have haW : lin (t + a • y) ^ (p - 1) ∈ W := (Finset.mem_filter.mp hag).2
          refine Finset.mem_filter.mpr ⟨?_, ?_⟩
          · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            refine ⟨haW, ?_⟩
            show dotU u (t + a • y) ≠ 0
            rw [dotU_add_line u y hyu]
            intro hzero
            apply hane
            show a = aZero u t
            rw [aZero]
            linear_combination hzero
          · show t + a • y - projAlong y i (t + a • y) • y = t
            rw [projAlong_add_line y i hπ, ht0, zero_add]
            exact add_sub_cancel_right t (a • y))
        (by
          intro x hx
          obtain ⟨hxS, hxt⟩ := Finset.mem_filter.mp hx
          obtain ⟨_, hxW, hxne⟩ := Finset.mem_filter.mp hxS
          have hxeq : x = t + projAlong y i x • y := sub_eq_iff_eq_add.mp hxt
          refine Finset.mem_erase.mpr ⟨?_, ?_⟩
          · show projAlong y i x ≠ aZero u t
            intro hEq
            apply hxne
            rw [hxeq, hEq, dotU_add_line u y hyu, aZero]
            ring
          · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            show lin (t + projAlong y i x • y) ^ (p - 1) ∈ W
            rw [← hxeq]
            exact hxW)
        (by
          intro a _
          show projAlong y i (t + a • y) = a
          rw [projAlong_add_line y i hπ, ht0, zero_add])
        (by
          intro x hx
          obtain ⟨_, hxt⟩ := Finset.mem_filter.mp hx
          show t + projAlong y i x • y = x
          rw [← hxt]
          exact sub_add_cancel x (projAlong y i x • y))
      exact hbij.symm
    rw [hfib]
    have ha0 : aZero u t ∈ goodScalars y W t := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show lin (t + aZero u t • y) ^ (p - 1) ∈ W
      apply hV0
      rw [dotU_add_line u y hyu, aZero]
      ring
    have hcard := Finset.card_erase_of_mem ha0
    rw [hcard]
    have hgood := goodScalars_card_le hp W t y hyR
    have hp2 : 2 ≤ p := hp.two_le
    omega
  calc ∑ t ∈ TZero y i,
        ((SNonzero u W).filter (fun x => x - projAlong y i x • y = t)).card
      ≤ ∑ _t ∈ TZero y i, (p - 2) := Finset.sum_le_sum hbound
    _ = (TZero y i).card * (p - 2) := Finset.sum_const_nat (fun _ _ => rfl)

theorem SNonzero_card_eq (hp : p.Prime) (u : Fin n → ZMod p)
    (W : Submodule (ZMod p) (MvPolynomial (Fin n) (ZMod p))) :
    (SNonzero u W).card = (RSet u W 1).card * (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard := Finset.card_nbij'
    (s := SNonzero u W) (t := RSet u W 1 ×ˢ (univ.erase (0 : ZMod p)))
    (i := fun x => ((dotU u x)⁻¹ • x, dotU u x))
    (j := fun q => q.2 • q.1)
    (by
      intro x hx
      obtain ⟨_, hxW, hxne⟩ := Finset.mem_filter.mp hx
      refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
        · show lin ((dotU u x)⁻¹ • x) ^ (p - 1) ∈ W
          rw [lin_smul_pow_card_sub_one hp (dotU u x)⁻¹ (inv_ne_zero hxne) x]
          exact hxW
        · show dotU u ((dotU u x)⁻¹ • x) = 1
          rw [dotU_smul, inv_mul_cancel₀ hxne]
      · exact Finset.mem_erase.mpr ⟨hxne, Finset.mem_univ _⟩)
    (by
      intro q hq
      obtain ⟨hqR, hqk⟩ := Finset.mem_product.mp hq
      obtain ⟨hk0, _⟩ := Finset.mem_erase.mp hqk
      obtain ⟨_, hqW, hqd⟩ := Finset.mem_filter.mp hqR
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · show lin (q.2 • q.1) ^ (p - 1) ∈ W
        rw [lin_smul_pow_card_sub_one hp q.2 hk0 q.1]
        exact hqW
      · show dotU u (q.2 • q.1) ≠ 0
        rw [dotU_smul, hqd, mul_one]
        exact hk0)
    (by
      intro x hx
      obtain ⟨_, _, hxne⟩ := Finset.mem_filter.mp hx
      show dotU u x • ((dotU u x)⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ hxne, one_smul])
    (by
      intro q hq
      obtain ⟨hqR, hqk⟩ := Finset.mem_product.mp hq
      obtain ⟨hk0, _⟩ := Finset.mem_erase.mp hqk
      obtain ⟨_, _, hqd⟩ := Finset.mem_filter.mp hqR
      refine Prod.ext ?_ ?_
      · show (dotU u (q.2 • q.1))⁻¹ • (q.2 • q.1) = q.1
        rw [dotU_smul, hqd, mul_one, smul_smul, inv_mul_cancel₀ hk0, one_smul]
      · show dotU u (q.2 • q.1) = q.2
        rw [dotU_smul, hqd, mul_one])
  rw [hcard, Finset.card_product, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, ZMod.card]

theorem lemma_3_4_ratio_V0_sub (hp : p.Prime) (u : Fin n → ZMod p)
    (W : Submodule (ZMod p) (MvPolynomial (Fin n) (ZMod p)))
    (hW : ¬ (MvPolynomial.homogeneousSubmodule (Fin n) (ZMod p) (p - 1) ≤ W))
    (hV0 : ∀ t : Fin n → ZMod p, dotU u t = 0 → lin t ^ (p - 1) ∈ W)
    {k : ZMod p} (hk : k ≠ 0) :
    p * (RSet u W k).card ≤ (p - 1) * (VSet u k).card := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hRne : ∃ x : Fin n → ZMod p, lin x ^ (p - 1) ∉ W := by
    by_contra h
    push Not at h
    apply hW
    rw [← span_lin_pow_eq_homogeneous hp (p - 1) (by omega) le_rfl]
    exact Submodule.span_le.mpr (by rintro _ ⟨x, rfl⟩; exact h x)
  have hY : ∃ y : Fin n → ZMod p, dotU u y = 1 ∧ lin y ^ (p - 1) ∉ W := by
    by_contra h
    push Not at h
    obtain ⟨x, hx⟩ := hRne
    have hx0 : dotU u x = 0 := by
      by_contra hk0
      have hmem : lin ((dotU u x)⁻¹ • x) ^ (p - 1) ∈ W :=
        h ((dotU u x)⁻¹ • x) (by rw [dotU_smul, inv_mul_cancel₀ hk0])
      rw [lin_smul_pow_card_sub_one hp (dotU u x)⁻¹ (inv_ne_zero hk0) x] at hmem
      exact hx hmem
    exact hx (hV0 x hx0)
  obtain ⟨y, hyu, hyR⟩ := hY
  have hy0 : y ≠ 0 := by
    intro h0
    apply hyR
    rw [h0, lin_zero]
    simp [zero_pow (by omega : p - 1 ≠ 0)]
  obtain ⟨i, hi⟩ : ∃ i : Fin n, y i ≠ 0 := by
    by_contra h
    push Not at h
    exact hy0 (funext fun i => h i)
  have hS := SNonzero_card_le hp u y hi hyu W hyR hV0
  have hSeq := SNonzero_card_eq hp u W
  have hVT : (VSet u 1).card = (TZero y i).card := VSet_one_card_eq_tzero hp u y hi hyu
  have hR1 : (p - 1) * (RSet u W 1).card ≤ (p - 2) * (VSet u 1).card := by
    calc (p - 1) * (RSet u W 1).card = (SNonzero u W).card := by rw [hSeq]; ring
      _ ≤ (TZero y i).card * (p - 2) := hS
      _ = (p - 2) * (VSet u 1).card := by rw [← hVT]; ring
  have hkey : p * (RSet u W 1).card ≤ (p - 1) * (VSet u 1).card := by
    have hkey' : p * (p - 2) ≤ (p - 1) * (p - 1) := by
      have h2 : p - 2 + 2 = p := Nat.sub_add_cancel hp2
      have h1' : p - 1 + 1 = p := Nat.sub_add_cancel (by omega : 1 ≤ p)
      nlinarith
    have hstep : p * ((p - 1) * (RSet u W 1).card)
        ≤ p * ((p - 2) * (VSet u 1).card) := Nat.mul_le_mul_left p hR1
    have h2 : p * ((p - 2) * (VSet u 1).card)
        ≤ (p - 1) * ((p - 1) * (VSet u 1).card) := by
      have := Nat.mul_le_mul_right (VSet u 1).card hkey'
      calc p * ((p - 2) * (VSet u 1).card) = (p * (p - 2)) * (VSet u 1).card := by ring
        _ ≤ ((p - 1) * (p - 1)) * (VSet u 1).card := this
        _ = (p - 1) * ((p - 1) * (VSet u 1).card) := by ring
    have hchain : (p - 1) * (p * (RSet u W 1).card)
        ≤ (p - 1) * ((p - 1) * (VSet u 1).card) := by
      calc (p - 1) * (p * (RSet u W 1).card) = p * ((p - 1) * (RSet u W 1).card) := by ring
        _ ≤ p * ((p - 2) * (VSet u 1).card) := hstep
        _ ≤ (p - 1) * ((p - 1) * (VSet u 1).card) := h2
    exact Nat.le_of_mul_le_mul_left hchain (by omega)
  rw [RSet_card_eq_smul hp u W hk, VSet_card_eq_smul hp u hk]
  exact hkey

theorem lemma34_ratio (hp : p.Prime) (u : Fin n → ZMod p)
    (W : Submodule (ZMod p) (MvPolynomial (Fin n) (ZMod p)))
    (hW : ¬ (MvPolynomial.homogeneousSubmodule (Fin n) (ZMod p) (p - 1) ≤ W))
    {k : ZMod p} (hk : k ≠ 0) :
    p * (RSet u W k).card ≤ (p - 1) * (VSet u k).card := by
  by_cases h : ∃ y : Fin n → ZMod p, dotU u y = 0 ∧ lin y ^ (p - 1) ∉ W
  · obtain ⟨y, hyu0, hyR⟩ := h
    have hy0 : y ≠ 0 := by
      intro h0
      apply hyR
      rw [h0, lin_zero]
      simp [zero_pow (by have := hp.two_le; omega : p - 1 ≠ 0)]
    obtain ⟨i, hi⟩ : ∃ i : Fin n, y i ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hy0 (funext fun i => hc i)
    exact lemma_3_4_ratio_zero_fiber hp u y hi hyu0 W hyR k
  · push Not at h
    exact lemma_3_4_ratio_V0_sub hp u W hW h hk

end Qatlib.Papers.HiddenTransl02.MainResults.Section3
