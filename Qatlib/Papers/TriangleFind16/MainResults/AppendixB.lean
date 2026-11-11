/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Appendix B: expectations over uniformly random subsets

Carette--Laurière--Magniez, fixed arXiv:1609.07786v2, Appendix B. The sparse analyses use three
elementary expectations over the uniform `x`-subset of a finite set:

* `expect_card_inter`: Lemma B.1, `Exp_{X⊆V1, |X|=x} |N ∩ X| = x |N| / |V1|`.
* `expect_edges`: Lemma B.2, `Exp_{X,Y} |E(X,Y)| = 2 x y m / n²`.
* `sum_sq_card_inter`: the second-moment counting identity used by Lemma B.3.
  The final inequality `Exp |N ∩ X|² ≤ 2 (x |N| / |V1|)²` of Lemma B.3 is not formalised here.

The expectations `𝔼 X ∈ s, f X` are the uniform averages `(∑ X ∈ s, f X) / s.card`.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.TriangleFind16.MainResults

variable {α : Type} [Fintype α] [DecidableEq α]

omit [Fintype α] in
/-- Counting identity behind Lemma B.1: the number of `x`-subsets of `V1` that contain a fixed
element `u ∈ V1` is `C(|V1| - 1, x - 1)`. -/
theorem card_powersetCard_mem {V1 : Finset α} {u : α} (hu : u ∈ V1) {x : ℕ} (hx : 1 ≤ x) :
    ((V1.powersetCard x).filter fun X => u ∈ X).card
      = Nat.choose (V1.card - 1) (x - 1) := by
  have hset : (V1.powersetCard x).filter (fun X => u ∈ X)
      = (V1.powersetCard x).filter ({u} ⊆ ·) := by
    refine Finset.filter_congr fun X _ => ?_
    simp
  rw [hset]
  have hsub : ({u} : Finset α) ⊆ V1 := by simpa using hu
  have hc := Finset.card_filter_powersetCard_subset ({u} : Finset α) V1 x hsub (by simpa using hx)
  simpa using hc

omit [Fintype α] in
/-- Double counting step of Lemma B.1: the expected size of `N ∩ X` is the average over the
elements of `N` of the probability that a uniform `x`-subset contains it. -/
theorem sum_card_inter (N V1 : Finset α) (hN : N ⊆ V1) {x : ℕ} (hx : 1 ≤ x) :
    ∑ X ∈ V1.powersetCard x, ((N ∩ X).card : ℝ)
      = (N.card : ℝ) * (Nat.choose (V1.card - 1) (x - 1) : ℝ) := by
  have hpt : ∀ X : Finset α, ((N ∩ X).card : ℝ)
      = ∑ u ∈ N, (if u ∈ X then (1 : ℝ) else 0) := by
    intro X
    have h1 : (N ∩ X).card = ∑ u ∈ N, if u ∈ X then 1 else 0 := by
      rw [← Finset.filter_mem_eq_inter, Finset.card_filter]
    rw [h1]
    push_cast
    rfl
  calc ∑ X ∈ V1.powersetCard x, ((N ∩ X).card : ℝ)
      = ∑ X ∈ V1.powersetCard x, ∑ u ∈ N, (if u ∈ X then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl fun X _ => hpt X
    _ = ∑ u ∈ N, ∑ X ∈ V1.powersetCard x, (if u ∈ X then (1 : ℝ) else 0) := Finset.sum_comm
    _ = ∑ u ∈ N, (((V1.powersetCard x).filter fun X => u ∈ X).card : ℝ) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.card_filter]
        push_cast
        rfl
    _ = ∑ _u ∈ N, ((Nat.choose (V1.card - 1) (x - 1) : ℕ) : ℝ) := by
        refine Finset.sum_congr rfl fun u hu => ?_
        rw [card_powersetCard_mem (hN hu) hx]
    _ = (N.card : ℝ) * (Nat.choose (V1.card - 1) (x - 1) : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]

omit [Fintype α] in
/-- Lemma B.1: for `N ⊆ V1 ⊆ V` and `1 ≤ x ≤ |V1|`, the expected number of elements of `N` in a
uniform `x`-subset of `V1` is `x |N| / |V1|`. -/
theorem expect_card_inter (N V1 : Finset α) (hN : N ⊆ V1) {x : ℕ} (hx : 1 ≤ x)
    (hxV : x ≤ V1.card) :
    (𝔼 X ∈ V1.powersetCard x, ((N ∩ X).card : ℝ))
      = (x : ℝ) * (N.card : ℝ) / (V1.card : ℝ) := by
  rw [Finset.expect_eq_sum_div_card, sum_card_inter N V1 hN hx, Finset.card_powersetCard]
  have hm : 0 < V1.card := lt_of_lt_of_le (by omega) hxV
  have hchoose : 0 < Nat.choose V1.card x := Nat.choose_pos hxV
  have hkey : (V1.card : ℝ) * (Nat.choose (V1.card - 1) (x - 1) : ℝ)
      = (Nat.choose V1.card x : ℝ) * (x : ℝ) := by
    have h := Nat.add_one_mul_choose_eq (V1.card - 1) (x - 1)
    have h1 : V1.card - 1 + 1 = V1.card := Nat.sub_add_cancel (by omega)
    have h2 : x - 1 + 1 = x := Nat.sub_add_cancel hx
    rw [h1, h2] at h
    exact_mod_cast h
  have hmR : (V1.card : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hcR : (Nat.choose V1.card x : ℝ) ≠ 0 := by
    exact_mod_cast hchoose.ne'
  field_simp
  nlinarith [hkey]


omit [Fintype α] in
/-- Counting: a fixed pair `u ≠ v` of elements of `V1` lies in `C(|V1| - 2, x - 2)` many
`x`-subsets of `V1`. -/
theorem card_powersetCard_pair {V1 : Finset α} {u v : α} (hu : u ∈ V1) (hv : v ∈ V1) (huv : u ≠ v)
    {x : ℕ} (hx : 2 ≤ x) :
    ((V1.powersetCard x).filter fun X => u ∈ X ∧ v ∈ X).card
      = Nat.choose (V1.card - 2) (x - 2) := by
  have hpair : ({u, v} : Finset α).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using huv), Finset.card_singleton]
  have hset : (V1.powersetCard x).filter (fun X => u ∈ X ∧ v ∈ X)
      = (V1.powersetCard x).filter ({u, v} ⊆ ·) := by
    refine Finset.filter_congr fun X _ => ?_
    simp [Finset.insert_subset_iff]
  rw [hset]
  have hsub : ({u, v} : Finset α) ⊆ V1 := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hu
    · exact hv
  have hc := Finset.card_filter_powersetCard_subset ({u, v} : Finset α) V1 x hsub
    (by rw [hpair]; omega)
  simpa [hpair] using hc

omit [Fintype α] in
/-- Second-moment counting behind Lemma B.3: the sum of `|N ∩ X|²` over all `x`-subsets of `V1`
splits into a diagonal term and an off-diagonal term. -/
theorem sum_sq_card_inter (N V1 : Finset α) (hN : N ⊆ V1) {x : ℕ} (hx : 2 ≤ x) :
    ∑ X ∈ V1.powersetCard x, (((N ∩ X).card : ℕ) : ℝ) ^ 2
      = (N.card : ℝ) * (Nat.choose (V1.card - 1) (x - 1) : ℝ)
        + ((N.card : ℝ) * ((N.card : ℝ) - 1)) * (Nat.choose (V1.card - 2) (x - 2) : ℝ) := by
  have hpt : ∀ X : Finset α, (((N ∩ X).card : ℕ) : ℝ) ^ 2
      = ∑ u ∈ N, ∑ v ∈ N, (if u ∈ X ∧ v ∈ X then (1 : ℝ) else 0) := by
    intro X
    have hc : ((N ∩ X).card : ℝ) = ∑ u ∈ N, (if u ∈ X then (1 : ℝ) else 0) := by
      rw [← Finset.filter_mem_eq_inter, Finset.card_filter]
      push_cast
      rfl
    rw [hc, sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hux : u ∈ X <;> by_cases hvx : v ∈ X <;> simp [hux, hvx]
  have hinner : ∀ u ∈ N, ∑ v ∈ N,
      ∑ X ∈ V1.powersetCard x, (if u ∈ X ∧ v ∈ X then (1 : ℝ) else 0)
      = (Nat.choose (V1.card - 1) (x - 1) : ℝ)
        + ((N.card : ℝ) - 1) * (Nat.choose (V1.card - 2) (x - 2) : ℝ) := by
    intro u hu
    have hu1 : u ∈ V1 := hN hu
    have hEq : insert u (N.erase u) = N := Finset.insert_erase hu
    conv_lhs => rw [← hEq]
    rw [Finset.sum_insert (Finset.notMem_erase u N)]
    have hdiag : ∑ X ∈ V1.powersetCard x, (if u ∈ X ∧ u ∈ X then (1 : ℝ) else 0)
        = (Nat.choose (V1.card - 1) (x - 1) : ℝ) := by
      have hcnt : ∑ X ∈ V1.powersetCard x, (if u ∈ X ∧ u ∈ X then (1 : ℝ) else 0)
          = (((V1.powersetCard x).filter fun X => u ∈ X).card : ℝ) := by
        rw [Finset.card_filter]
        push_cast
        refine Finset.sum_congr rfl fun X _ => ?_
        by_cases hux : u ∈ X <;> simp [hux]
      rw [hcnt, card_powersetCard_mem hu1 (by omega)]
    rw [hdiag]
    have hoff : ∑ v ∈ N.erase u, ∑ X ∈ V1.powersetCard x,
        (if u ∈ X ∧ v ∈ X then (1 : ℝ) else 0)
        = ((N.erase u).card : ℝ) * (Nat.choose (V1.card - 2) (x - 2) : ℝ) := by
      have hconst : ∀ v ∈ N.erase u, ∑ X ∈ V1.powersetCard x,
          (if u ∈ X ∧ v ∈ X then (1 : ℝ) else 0)
          = (Nat.choose (V1.card - 2) (x - 2) : ℝ) := by
        intro v hv
        have huv : u ≠ v := (Finset.ne_of_mem_erase hv).symm
        have hv1 : v ∈ V1 := hN (Finset.mem_of_mem_erase hv)
        have hcnt : ∑ X ∈ V1.powersetCard x, (if u ∈ X ∧ v ∈ X then (1 : ℝ) else 0)
            = (((V1.powersetCard x).filter fun X => u ∈ X ∧ v ∈ X).card : ℝ) := by
          rw [Finset.card_filter]
          push_cast
          refine Finset.sum_congr rfl fun X _ => ?_
          by_cases h1 : u ∈ X <;> by_cases h2 : v ∈ X <;> simp [h1, h2]
        rw [hcnt, card_powersetCard_pair hu1 hv1 huv hx]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
    rw [hoff, Finset.card_erase_of_mem hu]
    have hNpos : 0 < N.card := Finset.card_pos.mpr ⟨u, hu⟩
    have hcast : ((N.card - 1 : ℕ) : ℝ) = (N.card : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ N.card)]
      norm_num
    try rw [hcast]
    try ring

  calc ∑ X ∈ V1.powersetCard x, (((N ∩ X).card : ℕ) : ℝ) ^ 2
      = ∑ X ∈ V1.powersetCard x, ∑ u ∈ N, ∑ v ∈ N,
          (if u ∈ X ∧ v ∈ X then (1 : ℝ) else 0) := Finset.sum_congr rfl fun X _ => hpt X
    _ = ∑ u ∈ N, ∑ v ∈ N, ∑ X ∈ V1.powersetCard x,
          (if u ∈ X ∧ v ∈ X then (1 : ℝ) else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun u _ => Finset.sum_comm
    _ = ∑ _u ∈ N, ((Nat.choose (V1.card - 1) (x - 1) : ℝ)
          + ((N.card : ℝ) - 1) * (Nat.choose (V1.card - 2) (x - 2) : ℝ)) :=
        Finset.sum_congr rfl hinner
    _ = (N.card : ℝ) * (Nat.choose (V1.card - 1) (x - 1) : ℝ)
          + ((N.card : ℝ) * ((N.card : ℝ) - 1)) * (Nat.choose (V1.card - 2) (x - 2) : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

end Qatlib.Papers.TriangleFind16.MainResults
