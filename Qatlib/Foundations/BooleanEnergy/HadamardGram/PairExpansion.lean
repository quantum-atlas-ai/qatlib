/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.BooleanEnergy.HadamardGram.Carrier

set_option autoImplicit false
open scoped BigOperators
open Finset
namespace Qatlib.Foundations.BooleanEnergy.HadamardGram

theorem product_singleton_filter_lt_left {ι : Type*} [LinearOrder ι] [DecidableEq ι]
    (a : ι) (s : Finset ι) :
    ({a} ×ˢ s).filter (fun p : ι × ι => p.1 < p.2)
      = {a} ×ˢ (s.filter (fun x => a < x)) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hp1, hp2⟩, hlt⟩
    exact ⟨hp1, hp2, hp1 ▸ hlt⟩
  · rintro ⟨hp1, hp2, hlt⟩
    exact ⟨⟨hp1, hp2⟩, hp1 ▸ hlt⟩

theorem product_singleton_filter_lt_right {ι : Type*} [LinearOrder ι] [DecidableEq ι]
    (a : ι) (s : Finset ι) :
    (s ×ˢ {a}).filter (fun p : ι × ι => p.1 < p.2)
      = (s.filter (fun x => x < a)) ×ˢ {a} := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hp1, hp2⟩, hlt⟩
    exact ⟨⟨hp1, hp2 ▸ hlt⟩, hp2⟩
  · rintro ⟨⟨hp1, hlt⟩, hp2⟩
    exact ⟨⟨hp1, hp2⟩, hp2 ▸ hlt⟩

theorem filter_lt_add_filter_gt {ι : Type*} [LinearOrder ι] [DecidableEq ι]
    {a : ι} {s : Finset ι} (ha : a ∉ s) (g : ι → ℝ) :
    ∑ x ∈ s.filter (fun x => a < x), g x + ∑ x ∈ s.filter (fun x => x < a), g x
      = ∑ x ∈ s, g x := by
  classical
  have h : s.filter (fun x => x < a) = s.filter (fun x => ¬ a < x) := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, hlt⟩
      exact ⟨hx, not_lt.mpr hlt.le⟩
    · rintro ⟨hx, hna⟩
      rcases lt_trichotomy x a with hlt | heq | hgt
      · exact ⟨hx, hlt⟩
      · exact absurd (heq ▸ hx) ha
      · exact absurd hgt hna
  rw [h, Finset.sum_filter_add_sum_filter_not]

theorem offDiag_filter_lt_insert {ι : Type*} [LinearOrder ι] [DecidableEq ι]
    {a : ι} {s : Finset ι} (ha : a ∉ s) :
    (insert a s).offDiag.filter (fun p : ι × ι => p.1 < p.2)
      = s.offDiag.filter (fun p : ι × ι => p.1 < p.2)
        ∪ ({a} ×ˢ s).filter (fun p : ι × ι => p.1 < p.2)
        ∪ (s ×ˢ {a}).filter (fun p : ι × ι => p.1 < p.2) := by
  rw [Finset.offDiag_insert ha, Finset.filter_union, Finset.filter_union]

theorem sum_sq_eq_sum_sq_add_two_offDiag_finset {ι : Type*} [LinearOrder ι]
    [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, f i) ^ 2
      = (∑ i ∈ s, f i ^ 2)
        + 2 * ∑ p ∈ s.offDiag.filter (fun p : ι × ι => p.1 < p.2), f p.1 * f p.2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, offDiag_filter_lt_insert ha]
    have h1 : Disjoint (s.offDiag.filter (fun p : ι × ι => p.1 < p.2))
        (({a} ×ˢ s).filter (fun p : ι × ι => p.1 < p.2)) := by
      rw [Finset.disjoint_left]
      intro p hp hq
      simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_product,
        Finset.mem_singleton] at hp hq
      exact ha (hq.1.1 ▸ hp.1.1)
    have h2 : Disjoint (s.offDiag.filter (fun p : ι × ι => p.1 < p.2))
        ((s ×ˢ {a}).filter (fun p : ι × ι => p.1 < p.2)) := by
      rw [Finset.disjoint_left]
      intro p hp hq
      simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_product,
        Finset.mem_singleton] at hp hq
      exact ha (hq.1.2 ▸ hp.1.2.1)
    have h3 : Disjoint (({a} ×ˢ s).filter (fun p : ι × ι => p.1 < p.2))
        ((s ×ˢ {a}).filter (fun p : ι × ι => p.1 < p.2)) := by
      rw [Finset.disjoint_left]
      intro p hp hq
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton] at hp hq
      exact ha (hp.1.1 ▸ hq.1.1)
    rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨h2, h3⟩)]
    rw [Finset.sum_union h1]
    rw [product_singleton_filter_lt_left, product_singleton_filter_lt_right]
    rw [Finset.sum_product, Finset.sum_product]
    simp only [Finset.sum_singleton]
    have h3' : ∑ x ∈ s.filter (fun x => x < a), f x * f a
        = ∑ x ∈ s.filter (fun x => x < a), f a * f x := by
      exact Finset.sum_congr rfl (fun x _ => mul_comm (f x) (f a))
    rw [h3']
    have hpart : ∑ x ∈ s.filter (fun x => a < x), f a * f x
        + ∑ x ∈ s.filter (fun x => x < a), f a * f x = ∑ x ∈ s, f a * f x := by
      simpa only using filter_lt_add_filter_gt ha (fun x => f a * f x)
    have hEq : (∑ p ∈ s.offDiag.filter (fun p : ι × ι => p.1 < p.2), f p.1 * f p.2)
        + (∑ x ∈ s.filter (fun x => a < x), f a * f x)
        + (∑ x ∈ s.filter (fun x => x < a), f a * f x)
        = (∑ p ∈ s.offDiag.filter (fun p : ι × ι => p.1 < p.2), f p.1 * f p.2)
          + ∑ x ∈ s, f a * f x := by
      rw [add_assoc, hpart]
    rw [hEq]
    have hmul : ∑ x ∈ s, f a * f x = f a * ∑ x ∈ s, f x := by
      rw [Finset.mul_sum]
    rw [hmul]
    have hsq : (f a + ∑ x ∈ s, f x) ^ 2
        = f a ^ 2 + 2 * f a * (∑ x ∈ s, f x) + (∑ x ∈ s, f x) ^ 2 := by
      ring
    rw [hsq, ih]
    ring

theorem univ_offDiag_filter_lt {ι : Type*} [LinearOrder ι] [Fintype ι] [DecidableEq ι] :
    (univ : Finset ι).offDiag.filter (fun p : ι × ι => p.1 < p.2)
      = univ.filter (fun p : ι × ι => p.1 < p.2) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨-, hlt⟩
    exact hlt
  · intro hlt
    exact ⟨ne_of_lt hlt, hlt⟩

theorem sum_sq_eq_sum_sq_add_two_offDiag {ι : Type*} [LinearOrder ι] [Fintype ι]
    [DecidableEq ι] (f : ι → ℝ) :
    (∑ i, f i) ^ 2
      = (∑ i, f i ^ 2)
        + 2 * ∑ p ∈ (univ : Finset (ι × ι)).filter (fun p => p.1 < p.2), f p.1 * f p.2 := by
  have h := sum_sq_eq_sum_sq_add_two_offDiag_finset (univ : Finset ι) f
  rwa [univ_offDiag_filter_lt] at h

theorem sum_square_pairs (M : ℕ) (f : Fin M → ℝ) :
    (∑ r, f r)^2 = (∑ r, f r^2) +
      2 * ∑ p : ColumnPair M, f (left p)*f (right p) := by
  have h := sum_sq_eq_sum_sq_add_two_offDiag f
  have hs : (∑ p ∈ (univ : Finset (Fin M × Fin M)).filter (fun p => p.1<p.2),
      f p.1*f p.2) = ∑ p : ColumnPair M, f (left p)*f (right p) := by
    exact Finset.sum_subtype _ (fun _ => by simp) _
  rw [hs] at h
  exact h

end Qatlib.Foundations.BooleanEnergy.HadamardGram
