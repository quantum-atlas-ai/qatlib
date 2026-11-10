/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

set_option autoImplicit false

namespace Qatlib.Papers.QQueryGraph04.MainResults.LowerBounds

open Finset

abbrev ZeroMat (d k : ℕ) := Fin d → Fin k

def lowPos (k : ℕ) : Finset (Fin k) :=
  (univ : Finset (Fin (k / 2))).image (Fin.castLE (Nat.div_le_self k 2))

theorem mem_lowPos {k : ℕ} {j : Fin k} : j ∈ lowPos k ↔ j.val < k / 2 := by
  show j ∈ (univ : Finset (Fin (k / 2))).image (Fin.castLE (Nat.div_le_self k 2)) ↔ _
  constructor
  · intro h
    obtain ⟨x, -, rfl⟩ := mem_image.mp h
    exact x.isLt
  · intro h
    exact mem_image.mpr ⟨⟨j.val, h⟩, mem_univ _, Fin.ext rfl⟩

theorem lowPos_card (k : ℕ) : (lowPos k).card = k / 2 := by
  show ((univ : Finset (Fin (k / 2))).image (Fin.castLE (Nat.div_le_self k 2))).card = k / 2
  rw [show ((univ : Finset (Fin (k / 2))).image (Fin.castLE (Nat.div_le_self k 2))).card
      = (univ : Finset (Fin (k / 2))).card from
    card_image_of_injOn (by
      intro a _ b _ hab
      exact Fin.ext (by simpa using congrArg (fun x : Fin k => x.val) hab))]
  simp

def lowRows {d k : ℕ} (z : ZeroMat d k) : Finset (Fin d) :=
  univ.filter (fun i => (z i).val < k / 2)

def highRows {d k : ℕ} (z : ZeroMat d k) : Finset (Fin d) :=
  univ.filter (fun i => k / 2 ≤ (z i).val)

theorem mem_lowRows {d k : ℕ} {z : ZeroMat d k} {i : Fin d} :
    i ∈ lowRows z ↔ (z i).val < k / 2 := by
  simp [lowRows]

theorem mem_highRows {d k : ℕ} {z : ZeroMat d k} {i : Fin d} :
    i ∈ highRows z ↔ k / 2 ≤ (z i).val := by
  simp [highRows]

theorem lowRows_card_add_highRows_card {d k : ℕ} (z : ZeroMat d k) :
    (lowRows z).card + (highRows z).card = d := by
  have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin d)))
    (p := fun i => (z i).val < k / 2)
  have e : (univ.filter fun i : Fin d => ¬ (z i).val < k / 2) = highRows z := by
    apply filter_congr
    intro i _
    exact Nat.not_lt
  rw [e] at h
  simpa [lowRows] using h

theorem highRows_card_eq {d k : ℕ} (z : ZeroMat d k) :
    (highRows z).card = d - (lowRows z).card := by
  have h := lowRows_card_add_highRows_card z
  omega

def setRow {d k : ℕ} (z : ZeroMat d k) (i : Fin d) (p : Fin k) : ZeroMat d k :=
  Function.update z i p

theorem setRow_self {d k : ℕ} (z : ZeroMat d k) (i : Fin d) (p : Fin k) :
    setRow z i p i = p := by
  simp [setRow, Function.update]

theorem setRow_of_ne {d k : ℕ} (z : ZeroMat d k) {i j : Fin d} (h : j ≠ i) (p : Fin k) :
    setRow z i p j = z j := by
  simp [setRow, Function.update, h]

def RelStep {d k : ℕ} (z z' : ZeroMat d k) : Prop :=
  ∃ i : Fin d, z i ≠ z' i ∧ (∀ j : Fin d, j ≠ i → z j = z' j) ∧
    k / 2 ≤ (z i).val ∧ (z' i).val < k / 2

noncomputable def relSet {d k : ℕ} (z : ZeroMat d k) : Finset (ZeroMat d k) := by
  classical
  exact ((highRows z) ×ˢ (lowPos k)).image
    (fun q : Fin d × Fin k => setRow z q.1 q.2)

theorem mem_relSet {d k : ℕ} {z z' : ZeroMat d k} :
    z' ∈ relSet z ↔
      ∃ i, i ∈ highRows z ∧ ∃ p, p ∈ lowPos k ∧ setRow z i p = z' := by
  constructor
  · intro h
    unfold relSet at h
    obtain ⟨q, hq, hqz⟩ := mem_image.mp h
    obtain ⟨hi, hp⟩ := mem_product.mp hq
    exact ⟨q.1, hi, q.2, hp, hqz⟩
  · rintro ⟨i, hi, p, hp, rfl⟩
    show setRow z i p ∈ ((highRows z) ×ˢ (lowPos k)).image
      (fun q : Fin d × Fin k => setRow z q.1 q.2)
    exact mem_image.mpr ⟨(i, p), mem_product.mpr ⟨hi, hp⟩, rfl⟩

theorem relSet_apply_of_not_mem {d k : ℕ} {z z' : ZeroMat d k} (hz' : z' ∈ relSet z)
    {i : Fin d} (hi : i ∉ highRows z) : z' i = z i := by
  obtain ⟨a, ha, p, hp, rfl⟩ := mem_relSet.mp hz'
  exact setRow_of_ne z (fun h => hi (by rw [h]; exact ha)) p

theorem relSet_filter_row_move {d k : ℕ} (z : ZeroMat d k) {i : Fin d}
    (hi : i ∈ highRows z) :
    ((relSet z).filter (fun z' => z' i ≠ z i)).card = k / 2 := by
  classical
  have hset : (relSet z).filter (fun z' => z' i ≠ z i) =
      (lowPos k).image (fun p => setRow z i p) := by
    ext z'
    constructor
    · intro hz'
      obtain ⟨hz'rel, hne⟩ := mem_filter.mp hz'
      obtain ⟨a, ha, p, hp, rfl⟩ := mem_relSet.mp hz'rel
      by_cases hai : a = i
      · subst hai
        exact mem_image.mpr ⟨p, hp, rfl⟩
      · exact absurd (setRow_of_ne z (fun h => hai h.symm) p) hne
    · intro hz'
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hz'
      rw [mem_filter]
      refine ⟨mem_relSet.mpr ⟨i, hi, p, hp, rfl⟩, ?_⟩
      rw [setRow_self]
      intro h
      have hp' : p.val < k / 2 := mem_lowPos.mp hp
      have hh : k / 2 ≤ (z i).val := mem_highRows.mp hi
      rw [h] at hp'
      omega
  rw [hset]
  rw [show ((lowPos k).image (fun p => setRow z i p)).card = (lowPos k).card from
    card_image_of_injOn (by
      intro a _ b _ hab
      simpa [setRow_self] using congrArg (fun f : ZeroMat d k => f i) hab)]
  exact lowPos_card k

theorem relSet_filter_apply {d k : ℕ} (z : ZeroMat d k) {i : Fin d} {j : Fin k}
    (hi : i ∈ highRows z) (hj : j ∈ lowPos k) :
    ((relSet z).filter (fun z' => z' i = j)).card = 1 := by
  classical
  have hset : (relSet z).filter (fun z' => z' i = j) = {setRow z i j} := by
    ext z'
    constructor
    · intro hz'
      obtain ⟨hz'rel, hzj⟩ := mem_filter.mp hz'
      obtain ⟨a, ha, p, hp, rfl⟩ := mem_relSet.mp hz'rel
      by_cases hai : a = i
      · subst hai
        rw [setRow_self] at hzj
        rw [hzj]
        exact mem_singleton_self _
      · exfalso
        have he : setRow z a p i = z i :=
          setRow_of_ne z (fun h => hai h.symm) p
        rw [he] at hzj
        have h1 : k / 2 ≤ (z i).val := mem_highRows.mp hi
        have h2 : j.val < k / 2 := mem_lowPos.mp hj
        rw [hzj] at h1
        omega
    · intro hz'
      rw [mem_singleton] at hz'
      subst hz'
      rw [mem_filter]
      exact ⟨mem_relSet.mpr ⟨i, hi, j, hj, rfl⟩, setRow_self z i j⟩
  rw [hset, card_singleton]

abbrev diffAt {d k : ℕ} (z z' : ZeroMat d k) (i : Fin d) (j : Fin k) : Prop :=
  (z i = j) ↔ ¬ (z' i = j)

theorem relSet_entry_le {d k : ℕ} (z : ZeroMat d k) (i : Fin d) (j : Fin k) :
    ((relSet z).filter (fun z' => diffAt z z' i j)).card ≤ k / 2 := by
  classical
  change ((relSet z).filter (fun z' => (z i = j) ↔ ¬ (z' i = j))).card ≤ k / 2
  by_cases hi : i ∈ highRows z
  · by_cases hzij : z i = j
    · have hset : (relSet z).filter (fun z' => (z i = j) ↔ ¬ (z' i = j)) =
          (relSet z).filter (fun z' => z' i ≠ z i) := by
        apply filter_congr
        intro z' _
        rcases hzij with rfl
        simp
      rw [hset, relSet_filter_row_move z hi]
    · have hset : (relSet z).filter (fun z' => (z i = j) ↔ ¬ (z' i = j)) =
          (relSet z).filter (fun z' => z' i = j) := by
        apply filter_congr
        intro z' _
        exact ⟨fun h => by_contra fun hq => hzij (h.mpr hq),
          fun hq => ⟨fun hp' _ => hzij hp', fun hnq => absurd hq hnq⟩⟩
      by_cases hj : j ∈ lowPos k
      · rw [hset, relSet_filter_apply z hi hj]
        have h2 : j.val < k / 2 := mem_lowPos.mp hj
        omega
      · have hempty : (relSet z).filter (fun z' => z' i = j) = ∅ := by
          apply filter_false_of_mem
          intro z' hz'rel
          obtain ⟨a, ha, a', ha', rfl⟩ := mem_relSet.mp hz'rel
          by_cases hai : a = i
          · subst hai
            rw [setRow_self]
            exact fun h => hj (by rw [← h]; exact ha')
          · rw [show setRow z a a' i = z i from setRow_of_ne z (fun h => hai h.symm) a']
            exact hzij
        rw [hset, hempty, card_empty]
        exact Nat.zero_le _
  · have hempty : (relSet z).filter (fun z' => (z i = j) ↔ ¬ (z' i = j)) = ∅ := by
      apply filter_false_of_mem
      intro z' hz'rel
      have hii : z' i = z i := relSet_apply_of_not_mem hz'rel hi
      intro hd
      rw [hii] at hd
      have hq : ¬ (z i = j) := fun hp' => hd.mp hp' hp'
      exact hq (hd.mpr hq)
    rw [hempty, card_empty]
    exact Nat.zero_le _

theorem relSet_card {d k : ℕ} (z : ZeroMat d k) :
    (relSet z).card = (highRows z).card * (k / 2) := by
  classical
  have hinj : Set.InjOn (fun q : Fin d × Fin k => setRow z q.1 q.2)
      ↑((highRows z) ×ˢ (lowPos k)) := by
    intro a ha b hb heq
    obtain ⟨hai, hap⟩ := mem_product.mp ha
    obtain ⟨_hbi, _hbp⟩ := mem_product.mp hb
    by_cases h : a.1 = b.1
    · have hp : a.2 = b.2 := by
        have h2 : setRow z a.1 a.2 b.1 = setRow z b.1 b.2 b.1 := by
          have := congrFun heq b.1
          simpa using this
        rw [h] at h2
        rwa [setRow_self, setRow_self] at h2
      exact Prod.ext h hp
    · exfalso
      have h3 : setRow z a.1 a.2 a.1 = setRow z b.1 b.2 a.1 := by
        have := congrFun heq a.1
        simpa using this
      rw [setRow_self] at h3
      rw [setRow_of_ne z h b.2] at h3
      have hle : k / 2 ≤ a.2.val := by
        rw [h3]
        exact mem_highRows.mp hai
      have hlt : a.2.val < k / 2 := mem_lowPos.mp hap
      omega
  have h1 : (relSet z).card = ((highRows z) ×ˢ (lowPos k)).card := by
    unfold relSet
    exact card_image_of_injOn hinj
  rw [h1, card_product, lowPos_card]

theorem relSet_card_odd {d k : ℕ} (hd : d % 2 = 1) (z : ZeroMat d k)
    (hz : (lowRows z).card = d / 2) :
    (relSet z).card = (d / 2 + 1) * (k / 2) := by
  rw [relSet_card, highRows_card_eq, hz]
  have h : d - d / 2 = d / 2 + 1 := by omega
  rw [h]

theorem adversary_ratio_ge {d k N : ℕ} (hN : N = d * k) (hd : 0 < d) :
    Real.sqrt ((d : ℝ) * (N : ℝ)) / (2 * Real.sqrt 2) ≤
      ((d : ℝ) / 2 + 1) * Real.sqrt ((k : ℝ) / 2) := by
  have hN' : (N : ℝ) = (d : ℝ) * (k : ℝ) := by exact_mod_cast hN
  have hnonneg : 0 ≤ Real.sqrt ((k : ℝ) / 2) := Real.sqrt_nonneg _
  have hid : Real.sqrt ((d : ℝ) * (N : ℝ)) =
      2 * Real.sqrt 2 * ((d : ℝ) / 2 * Real.sqrt ((k : ℝ) / 2)) := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
    have step1 : Real.sqrt ((d : ℝ) * (N : ℝ)) = (d : ℝ) * Real.sqrt (k : ℝ) := by
      rw [hN', show (d : ℝ) * ((d : ℝ) * (k : ℝ)) = (d : ℝ) ^ 2 * (k : ℝ) by ring]
      rw [Real.sqrt_mul (sq_nonneg (d : ℝ)) (k : ℝ), Real.sqrt_sq hd0]
    rw [step1]
    conv_lhs => rw [show (k : ℝ) = 2 * ((k : ℝ) / 2) by ring]
    have hsq2 : Real.sqrt (2 * ((k : ℝ) / 2)) =
        Real.sqrt 2 * Real.sqrt ((k : ℝ) / 2) :=
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) ((k : ℝ) / 2)
    rw [hsq2]
    ring
  have hpos2 : (0 : ℝ) < 2 * Real.sqrt 2 := by positivity
  rw [div_le_iff₀ hpos2, hid]
  have h1 : (d : ℝ) / 2 * Real.sqrt ((k : ℝ) / 2) ≤
      ((d : ℝ) / 2 + 1) * Real.sqrt ((k : ℝ) / 2) := by
    have := mul_le_mul_of_nonneg_right (by linarith : (d : ℝ) / 2 ≤ (d : ℝ) / 2 + 1) hnonneg
    simpa using this
  calc 2 * Real.sqrt 2 * ((d : ℝ) / 2 * Real.sqrt ((k : ℝ) / 2))
      ≤ 2 * Real.sqrt 2 * (((d : ℝ) / 2 + 1) * Real.sqrt ((k : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt hpos2)
    _ = ((d : ℝ) / 2 + 1) * Real.sqrt ((k : ℝ) / 2) * (2 * Real.sqrt 2) := by ring

end Qatlib.Papers.QQueryGraph04.MainResults.LowerBounds
