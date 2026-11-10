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

def projAlong (y0 : Fin n → ZMod p) (i : Fin n) : (Fin n → ZMod p) →+ ZMod p where
  toFun z := z i * (y0 i)⁻¹
  map_zero' := by simp
  map_add' := by
    intro a b
    show (a + b) i * (y0 i)⁻¹ = a i * (y0 i)⁻¹ + b i * (y0 i)⁻¹
    rw [Pi.add_apply, add_mul]

theorem projAlong_self (hp : p.Prime) {y0 : Fin n → ZMod p} {i : Fin n}
    (hi : y0 i ≠ 0) : projAlong y0 i y0 = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  show y0 i * (y0 i)⁻¹ = 1
  exact mul_inv_cancel₀ hi

theorem projAlong_smul (y0 : Fin n → ZMod p) (i : Fin n) (a : ZMod p)
    (z : Fin n → ZMod p) : projAlong y0 i (a • z) = a * projAlong y0 i z := by
  show (a • z) i * (y0 i)⁻¹ = a * (z i * (y0 i)⁻¹)
  rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem dotU_smul (u : Fin n → ZMod p) (a : ZMod p) (y : Fin n → ZMod p) :
    dotU u (a • y) = a * dotU u y := by
  change (∑ i, (a • y) i * u i) = a * ∑ i, y i * u i
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Pi.smul_apply, smul_eq_mul]
  ring

theorem line_pow_mem_of_all_mem_zmod (hp : p.Prime)
    (W : Submodule (ZMod p) (MvPolynomial (Fin n) (ZMod p)))
    (z y : Fin n → ZMod p)
    (h : ∀ a : ZMod p, lin (z + a • y) ^ (p - 1) ∈ W) :
    lin y ^ (p - 1) ∈ W :=
  line_pow_mem_of_all_mem hp W z y (fun a : Fin p => h (a.val : ZMod p))

variable [Fintype (ZMod p)]

def VSet (u : Fin n → ZMod p) (k : ZMod p) : Finset (Fin n → ZMod p) :=
  univ.filter (fun x => dotU u x = k)

def RSet (u : Fin n → ZMod p)
    (W : Submodule (ZMod p) (MvPolynomial (Fin n) (ZMod p))) (k : ZMod p) :
    Finset (Fin n → ZMod p) :=
  univ.filter (fun x => lin x ^ (p - 1) ∈ W ∧ dotU u x = k)

def TSet (y0 : Fin n → ZMod p) (i : Fin n) (u : Fin n → ZMod p) (k : ZMod p) :
    Finset (Fin n → ZMod p) :=
  univ.filter (fun t => projAlong y0 i t = 0 ∧ dotU u t = k)

def goodScalars (y0 : Fin n → ZMod p)
    (W : Submodule (ZMod p) (MvPolynomial (Fin n) (ZMod p))) (t : Fin n → ZMod p) :
    Finset (ZMod p) :=
  univ.filter (fun a => lin (t + a • y0) ^ (p - 1) ∈ W)

def RProd (y0 : Fin n → ZMod p) (i : Fin n) (u : Fin n → ZMod p)
    (W : Submodule (ZMod p) (MvPolynomial (Fin n) (ZMod p))) (k : ZMod p) :
    Finset ((Fin n → ZMod p) × ZMod p) :=
  ((TSet y0 i u k) ×ˢ (univ : Finset (ZMod p))).filter
    (fun q => lin (q.1 + q.2 • y0) ^ (p - 1) ∈ W)

theorem VSet_card_eq (hp : p.Prime) (u y0 : Fin n → ZMod p) {i : Fin n}
    (hi : y0 i ≠ 0) (hy0u : dotU u y0 = 0) (k : ZMod p) :
    (VSet u k).card = (TSet y0 i u k).card * p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hπ : projAlong y0 i y0 = 1 := projAlong_self hp hi
  have hcard := Finset.card_nbij'
    (s := VSet u k) (t := (TSet y0 i u k) ×ˢ (univ : Finset (ZMod p)))
    (i := fun x => (x - projAlong y0 i x • y0, projAlong y0 i x))
    (j := fun q => q.1 + q.2 • y0)
    (by
      intro x hx
      have hx' : dotU u x = k := (Finset.mem_filter.mp hx).2
      refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · show projAlong y0 i (x - projAlong y0 i x • y0) = 0
        rw [map_sub, projAlong_smul, hπ, mul_one, sub_self]
      · show dotU u (x - projAlong y0 i x • y0) = k
        rw [map_sub, dotU_smul, hy0u, mul_zero, sub_zero, hx'])
    (by
      intro q hq
      obtain ⟨hq1, _⟩ := Finset.mem_product.mp hq
      obtain ⟨_, hqd, hqk⟩ := Finset.mem_filter.mp hq1
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show dotU u (q.1 + q.2 • y0) = k
      rw [map_add, dotU_smul, hy0u, mul_zero, add_zero, hqk])
    (by
      intro x _
      show x - projAlong y0 i x • y0 + projAlong y0 i x • y0 = x
      exact sub_add_cancel x (projAlong y0 i x • y0))
    (by
      intro q hq
      obtain ⟨hq1, _⟩ := Finset.mem_product.mp hq
      obtain ⟨_, hqd, _⟩ := Finset.mem_filter.mp hq1
      refine Prod.ext ?_ ?_
      · show q.1 + q.2 • y0 - projAlong y0 i (q.1 + q.2 • y0) • y0 = q.1
        rw [map_add, projAlong_smul, hπ, mul_one, hqd, zero_add]
        exact add_sub_cancel_right q.1 (q.2 • y0)
      · show projAlong y0 i (q.1 + q.2 • y0) = q.2
        rw [map_add, projAlong_smul, hπ, mul_one, hqd, zero_add])
  rw [hcard, Finset.card_product, Finset.card_univ, ZMod.card]

theorem RSet_card_eq (hp : p.Prime) (u y0 : Fin n → ZMod p) {i : Fin n}
    (hi : y0 i ≠ 0) (hy0u : dotU u y0 = 0)
    (W : Submodule (ZMod p) (MvPolynomial (Fin n) (ZMod p))) (k : ZMod p) :
    (RSet u W k).card = (RProd y0 i u W k).card := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hπ : projAlong y0 i y0 = 1 := projAlong_self hp hi
  have hcard := Finset.card_nbij'
    (s := RSet u W k) (t := RProd y0 i u W k)
    (i := fun x => (x - projAlong y0 i x • y0, projAlong y0 i x))
    (j := fun q => q.1 + q.2 • y0)
    (by
      intro x hx
      obtain ⟨_, hxW, hxk⟩ := Finset.mem_filter.mp hx
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · refine Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
        · show projAlong y0 i (x - projAlong y0 i x • y0) = 0
          rw [map_sub, projAlong_smul, hπ, mul_one, sub_self]
        · show dotU u (x - projAlong y0 i x • y0) = k
          rw [map_sub, dotU_smul, hy0u, mul_zero, sub_zero, hxk]
      · show lin ((x - projAlong y0 i x • y0) + projAlong y0 i x • y0) ^ (p - 1) ∈ W
        rw [sub_add_cancel]
        exact hxW)
    (by
      intro q hq
      obtain ⟨hqProd, hqW⟩ := Finset.mem_filter.mp hq
      obtain ⟨hq1, _⟩ := Finset.mem_product.mp hqProd
      obtain ⟨_, hqd, hqk⟩ := Finset.mem_filter.mp hq1
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · show lin (q.1 + q.2 • y0) ^ (p - 1) ∈ W
        exact hqW
      · show dotU u (q.1 + q.2 • y0) = k
        rw [map_add, dotU_smul, hy0u, mul_zero, add_zero, hqk])
    (by
      intro x _
      show x - projAlong y0 i x • y0 + projAlong y0 i x • y0 = x
      exact sub_add_cancel x (projAlong y0 i x • y0))
    (by
      intro q hq
      obtain ⟨hqProd, _⟩ := Finset.mem_filter.mp hq
      obtain ⟨hq1, _⟩ := Finset.mem_product.mp hqProd
      obtain ⟨_, hqd, _⟩ := Finset.mem_filter.mp hq1
      refine Prod.ext ?_ ?_
      · show q.1 + q.2 • y0 - projAlong y0 i (q.1 + q.2 • y0) • y0 = q.1
        rw [map_add, projAlong_smul, hπ, mul_one, hqd, zero_add]
        exact add_sub_cancel_right q.1 (q.2 • y0)
      · show projAlong y0 i (q.1 + q.2 • y0) = q.2
        rw [map_add, projAlong_smul, hπ, mul_one, hqd, zero_add])
  exact hcard

theorem VSet_card_eq_smul (hp : p.Prime) (u : Fin n → ZMod p) {k : ZMod p}
    (hk : k ≠ 0) : (VSet u k).card = (VSet u 1).card := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hk1 : k⁻¹ * k = 1 := inv_mul_cancel₀ hk
  have h1k : k * k⁻¹ = 1 := mul_inv_cancel₀ hk
  have hcard := Finset.card_nbij'
    (s := VSet u 1) (t := VSet u k)
    (i := fun y => k • y) (j := fun y => k⁻¹ • y)
    (by
      intro y hy
      have hy' : dotU u y = 1 := (Finset.mem_filter.mp hy).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show dotU u (k • y) = k
      rw [dotU_smul, hy', mul_one])
    (by
      intro y hy
      have hy' : dotU u y = k := (Finset.mem_filter.mp hy).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      show dotU u (k⁻¹ • y) = 1
      rw [dotU_smul, hy', hk1])
    (by
      intro y _
      show k⁻¹ • (k • y) = y
      rw [smul_smul, hk1, one_smul])
    (by
      intro y _
      show k • (k⁻¹ • y) = y
      rw [smul_smul, h1k, one_smul])
  exact hcard.symm

theorem RSet_card_eq_smul (hp : p.Prime) (u : Fin n → ZMod p)
    (W : Submodule (ZMod p) (MvPolynomial (Fin n) (ZMod p))) {k : ZMod p}
    (hk : k ≠ 0) : (RSet u W k).card = (RSet u W 1).card := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hk1 : k⁻¹ * k = 1 := inv_mul_cancel₀ hk
  have h1k : k * k⁻¹ = 1 := mul_inv_cancel₀ hk
  have hcard := Finset.card_nbij'
    (s := RSet u W 1) (t := RSet u W k)
    (i := fun y => k • y) (j := fun y => k⁻¹ • y)
    (by
      intro y hy
      obtain ⟨_, hyW, hyd⟩ := Finset.mem_filter.mp hy
      have hy' : dotU u y = 1 := hyd
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · show lin (k • y) ^ (p - 1) ∈ W
        rw [lin_smul_pow_card_sub_one hp k hk y]
        exact hyW
      · show dotU u (k • y) = k
        rw [dotU_smul, hy', mul_one])
    (by
      intro y hy
      obtain ⟨_, hyW, hyd⟩ := Finset.mem_filter.mp hy
      have hy' : dotU u y = k := hyd
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
      · show lin (k⁻¹ • y) ^ (p - 1) ∈ W
        rw [lin_smul_pow_card_sub_one hp k⁻¹ (inv_ne_zero hk) y]
        exact hyW
      · show dotU u (k⁻¹ • y) = 1
        rw [dotU_smul, hy', hk1])
    (by
      intro y _
      show k⁻¹ • (k • y) = y
      rw [smul_smul, hk1, one_smul])
    (by
      intro y _
      show k • (k⁻¹ • y) = y
      rw [smul_smul, h1k, one_smul])
  exact hcard.symm

theorem goodScalars_card_le (hp : p.Prime)
    (W : Submodule (ZMod p) (MvPolynomial (Fin n) (ZMod p)))
    (t y0 : Fin n → ZMod p) (hy0R : lin y0 ^ (p - 1) ∉ W) :
    (goodScalars y0 W t).card ≤ p - 1 := by
  have hlt : (goodScalars y0 W t).card < p := by
    have hne : goodScalars y0 W t ≠ univ := by
      intro h
      apply hy0R
      refine line_pow_mem_of_all_mem_zmod hp W t y0 ?_
      intro a
      have ha : a ∈ goodScalars y0 W t := by rw [h]; exact Finset.mem_univ a
      exact (Finset.mem_filter.mp ha).2
    have hproper : goodScalars y0 W t ⊂ (univ : Finset (ZMod p)) :=
      Finset.ssubset_univ_iff.mpr hne
    have hc := Finset.card_lt_card hproper
    rwa [Finset.card_univ, ZMod.card] at hc
  omega

set_option maxHeartbeats 1000000 in

theorem RProd_card_le (hp : p.Prime) {u y0 : Fin n → ZMod p} {i : Fin n}
    (W : Submodule (ZMod p) (MvPolynomial (Fin n) (ZMod p)))
    (hy0R : lin y0 ^ (p - 1) ∉ W) (k : ZMod p) :
    (RProd y0 i u W k).card ≤ (TSet y0 i u k).card * (p - 1) := by
  have hsum := Finset.card_eq_sum_card_fiberwise
    (M := Fin n → ZMod p) (ι := (Fin n → ZMod p) × ZMod p)
    (s := RProd y0 i u W k) (t := TSet y0 i u k) (f := fun q => q.1)
    (by
      intro q hq
      have hqProd := (Finset.mem_filter.mp hq).1
      exact (Finset.mem_product.mp hqProd).1)
  rw [hsum]
  have hbound : ∀ t ∈ TSet y0 i u k,
      ((RProd y0 i u W k).filter (fun q => q.1 = t)).card ≤ p - 1 := by
    intro t ht
    have hfib : ((RProd y0 i u W k).filter (fun q => q.1 = t)).card
        = (goodScalars y0 W t).card := by
      have hbij := Finset.card_nbij'
        (s := goodScalars y0 W t) (t := (RProd y0 i u W k).filter (fun q => q.1 = t))
        (i := fun a => (t, a)) (j := fun q => q.2)
        (by
          intro a ha
          have haW : lin (t + a • y0) ^ (p - 1) ∈ W := (Finset.mem_filter.mp ha).2
          refine Finset.mem_filter.mpr ⟨?_, ?_⟩
          · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
            · exact Finset.mem_product.mpr ⟨ht, Finset.mem_univ _⟩
            · show lin (t + a • y0) ^ (p - 1) ∈ W
              exact haW
          · rfl)
        (by
          intro q hq
          have hq1 : q.1 = t := (Finset.mem_filter.mp hq).2
          have hqW : lin (q.1 + q.2 • y0) ^ (p - 1) ∈ W :=
            (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          rw [hq1] at hqW
          exact hqW)
        (by intro a _; rfl)
        (by
          intro q hq
          have hq1 : q.1 = t := (Finset.mem_filter.mp hq).2
          show (t, q.2) = q
          rw [← hq1])
      exact hbij.symm
    rw [hfib]
    exact goodScalars_card_le hp W t y0 hy0R
  calc ∑ t ∈ TSet y0 i u k, ((RProd y0 i u W k).filter (fun q => q.1 = t)).card
      ≤ ∑ _t ∈ TSet y0 i u k, (p - 1) := Finset.sum_le_sum hbound
    _ = (TSet y0 i u k).card * (p - 1) :=
        Finset.sum_const_nat (fun _ _ => rfl)

theorem lemma_3_4_ratio_zero_fiber (hp : p.Prime) (u y0 : Fin n → ZMod p) {i : Fin n}
    (hi : y0 i ≠ 0) (hy0u : dotU u y0 = 0)
    (W : Submodule (ZMod p) (MvPolynomial (Fin n) (ZMod p)))
    (hy0R : lin y0 ^ (p - 1) ∉ W) (k : ZMod p) :
    p * (RSet u W k).card ≤ (p - 1) * (VSet u k).card := by
  have hV : (VSet u k).card = (TSet y0 i u k).card * p := VSet_card_eq hp u y0 hi hy0u k
  have hR : (RSet u W k).card = (RProd y0 i u W k).card :=
    RSet_card_eq hp u y0 hi hy0u W k
  have hB : (RProd y0 i u W k).card ≤ (TSet y0 i u k).card * (p - 1) :=
    RProd_card_le hp W hy0R k
  rw [hR]
  calc p * (RProd y0 i u W k).card
      ≤ p * ((TSet y0 i u k).card * (p - 1)) := Nat.mul_le_mul_left p hB
    _ = (p - 1) * ((TSet y0 i u k).card * p) := by ring
    _ = (p - 1) * (VSet u k).card := by rw [hV]

end Qatlib.Papers.HiddenTransl02.MainResults.Section3
