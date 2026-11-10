/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SProd
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Disjoint
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

namespace Qatlib.Papers.HadamardAnn19.MainResults.GeneralEnergy

set_option autoImplicit false

open Finset

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

def d2 (M : ℕ) (b : Fin M → Fin M → ℝ) (i j : Fin M) : ℝ :=
  (M : ℝ) + 2 * ∑ p ∈ (univ : Finset (Fin M × Fin M)).filter (fun p => p.1 < p.2),
    b p.1 i * b p.1 j * b p.2 i * b p.2 j

def pairEnergy (M : ℕ) (b : Fin M → Fin M → ℝ) (i j : Fin M) : ℝ :=
  (∑ m, b m i * b m j) ^ 2

def Es (M : ℕ) (b : Fin M → Fin M → ℝ) : ℝ :=
  ∑ p ∈ (univ : Finset (Fin M × Fin M)).filter (fun p => p.1 < p.2), d2 M b p.1 p.2

theorem d2_eq_pairEnergy {M : ℕ} {b : Fin M → Fin M → ℝ}
    (hb : ∀ m k, b m k = -1 ∨ b m k = 1) (i j : Fin M) :
    d2 M b i j = pairEnergy M b i j := by
  have hx2 : ∀ m, (b m i * b m j) ^ 2 = 1 := by
    intro m
    rcases hb m i with h | h <;> rcases hb m j with h' | h' <;>
      rw [h, h'] <;> norm_num
  have h := sum_sq_eq_sum_sq_add_two_offDiag (fun m => b m i * b m j)
  unfold pairEnergy
  rw [h]
  unfold d2
  have hsum : (∑ p ∈ (univ : Finset (Fin M × Fin M)).filter (fun p => p.1 < p.2),
        b p.1 i * b p.1 j * b p.2 i * b p.2 j)
      = ∑ p ∈ (univ : Finset (Fin M × Fin M)).filter (fun p => p.1 < p.2),
        (b p.1 i * b p.1 j) * (b p.2 i * b p.2 j) :=
    Finset.sum_congr rfl (fun p _ => by ring)
  rw [hsum]
  have hsq : (∑ m, (b m i * b m j) ^ 2) = (M : ℝ) := by
    rw [Finset.sum_congr rfl (fun m _ => hx2 m)]
    simp
  rw [hsq]

theorem Es_eq_sum_pairEnergy {M : ℕ} {b : Fin M → Fin M → ℝ}
    (hb : ∀ m k, b m k = -1 ∨ b m k = 1) :
    Es M b = ∑ p ∈ (univ : Finset (Fin M × Fin M)).filter (fun p => p.1 < p.2),
      pairEnergy M b p.1 p.2 := by
  unfold Es
  exact Finset.sum_congr rfl (fun p _ => d2_eq_pairEnergy hb p.1 p.2)

def spinOfQ (q : ℝ) : ℝ := 1 - 2 * q

noncomputable def qOfSpin (s : ℝ) : ℝ := (1 - s) / 2

theorem spinOfQ_qOfSpin (s : ℝ) : spinOfQ (qOfSpin s) = s := by
  unfold spinOfQ qOfSpin
  ring

theorem qOfSpin_spinOfQ (q : ℝ) : qOfSpin (spinOfQ q) = q := by
  unfold spinOfQ qOfSpin
  ring

theorem spinOfQ_mem {q : ℝ} (hq : q = 0 ∨ q = 1) :
    spinOfQ q = -1 ∨ spinOfQ q = 1 := by
  unfold spinOfQ
  rcases hq with rfl | rfl <;> norm_num

theorem qOfSpin_mem {s : ℝ} (hs : s = -1 ∨ s = 1) :
    qOfSpin s = 0 ∨ qOfSpin s = 1 := by
  unfold qOfSpin
  rcases hs with rfl | rfl <;> norm_num

def quadTuples (M : ℕ) :
    Finset (Fin (M * M) × Fin (M * M) × Fin (M * M) × Fin (M * M)) :=
  univ.filter (fun p =>
    p.1 < p.2.1 ∧ p.2.1 < p.2.2.1 ∧ p.2.2.1 < p.2.2.2)

noncomputable def ekS (M : ℕ) (s : Fin (M * M) → ℝ) : ℝ :=
  (M ^ 2 * (M - 1) : ℝ) / 2
    + 2 * ∑ p ∈ quadTuples M, s p.1 * s p.2.1 * s p.2.2.1 * s p.2.2.2

theorem ekS_two (s : Fin 4 → ℝ) :
    ekS 2 s = 2 + 2 * (s 0 * s 1 * s 2 * s 3) := by
  have h : quadTuples 2 =
      {((0 : Fin 4), (1 : Fin 4), (2 : Fin 4), (3 : Fin 4))} := by
    decide
  simp [ekS, h]
  norm_num

def hAnd (qi qj qk δ : ℝ) : ℝ :=
  δ * (3 * qk + qi * qj - 2 * qi * qk - 2 * qj * qk)

theorem hAnd_and {qi qj δ : ℝ} (hi : qi = 0 ∨ qi = 1) (hj : qj = 0 ∨ qj = 1) :
    hAnd qi qj (qi * qj) δ = 0 := by
  unfold hAnd
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> norm_num

theorem sum_spin_mul_eq (M : ℕ) (q : Fin M → Fin M → ℝ) (i j : Fin M) :
    ∑ r, (1 - 2 * q r i) * (1 - 2 * q r j)
      = (M : ℝ) - 2 * ∑ r, q r i - 2 * ∑ r, q r j
        + 4 * ∑ r, q r i * q r j := by
  calc ∑ r, (1 - 2 * q r i) * (1 - 2 * q r j)
      = ∑ r, (1 - 2 * q r i - 2 * q r j + 4 * (q r i * q r j)) := by
        exact Finset.sum_congr rfl (fun r _ => by ring)
    _ = ∑ r, (1 : ℝ) - ∑ r, 2 * q r i - ∑ r, 2 * q r j
          + ∑ r, 4 * (q r i * q r j) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    _ = (M : ℝ) - 2 * ∑ r, q r i - 2 * ∑ r, q r j
          + 4 * ∑ r, q r i * q r j := by
        simp [Finset.mul_sum]

def pairReduced (M : ℕ) (q : Fin M → Fin M → ℝ) (a : Fin M → ℝ) (i j : Fin M) : ℝ :=
  ((M : ℝ) - 2 * ∑ r, q r i - 2 * ∑ r, q r j + 4 * ∑ r, a r) ^ 2

theorem pairEnergy_eq_pairReduced_add_penalty (M : ℕ) (q : Fin M → Fin M → ℝ)
    (a : Fin M → ℝ) (i j : Fin M) (δ : ℝ)
    (hqi : ∀ r, q r i = 0 ∨ q r i = 1)
    (hqj : ∀ r, q r j = 0 ∨ q r j = 1)
    (ha : ∀ r, a r = q r i * q r j) :
    pairEnergy M (fun r k => 1 - 2 * q r k) i j
      = pairReduced M q a i j + δ * ∑ r, hAnd (q r i) (q r j) (a r) 1 := by
  have hsum : ∑ r, a r = ∑ r, q r i * q r j :=
    Finset.sum_congr rfl (fun r _ => ha r)
  have hpen : ∑ r, hAnd (q r i) (q r j) (a r) 1 = 0 := by
    refine Finset.sum_eq_zero (fun r _ => ?_)
    rw [ha r, hAnd_and (hqi r) (hqj r)]
  unfold pairEnergy pairReduced
  rw [sum_spin_mul_eq, hsum, hpen, mul_zero, add_zero]

def reducedEs (M : ℕ) (δ : ℝ) (q : Fin M → Fin M → ℝ)
    (a : Fin M → Fin M → Fin M → ℝ) : ℝ :=
  ∑ p ∈ (univ : Finset (Fin M × Fin M)).filter (fun p => p.1 < p.2),
    (pairReduced M q (fun r => a r p.1 p.2) p.1 p.2
      + δ * ∑ r, hAnd (q r p.1) (q r p.2) (a r p.1 p.2) 1)

theorem Es_eq_reducedEs (M : ℕ) (q : Fin M → Fin M → ℝ)
    (a : Fin M → Fin M → Fin M → ℝ) (δ : ℝ)
    (hq : ∀ r k, q r k = 0 ∨ q r k = 1)
    (ha : ∀ r i j, a r i j = q r i * q r j) :
    Es M (fun r k => 1 - 2 * q r k) = reducedEs M δ q a := by
  have hsign : ∀ r k, (1 - 2 * q r k : ℝ) = -1 ∨ (1 - 2 * q r k : ℝ) = 1 := by
    intro r k
    rcases hq r k with h | h <;> rw [h] <;> norm_num
  rw [Es_eq_sum_pairEnergy hsign]
  unfold reducedEs
  refine Finset.sum_congr rfl (fun p _ => ?_)
  exact pairEnergy_eq_pairReduced_add_penalty M q (fun r => a r p.1 p.2) p.1 p.2 δ
    (fun r => hq r p.1) (fun r => hq r p.2) (fun r => ha r p.1 p.2)

theorem Es_eq_reducedEs_spin (M : ℕ) (s : Fin M → Fin M → ℝ)
    (a : Fin M → Fin M → Fin M → ℝ) (δ : ℝ)
    (hs : ∀ r k, s r k = -1 ∨ s r k = 1)
    (ha : ∀ r i j, a r i j = qOfSpin (s r i) * qOfSpin (s r j)) :
    Es M s = reducedEs M δ (fun r k => qOfSpin (s r k)) a := by
  have hmain := Es_eq_reducedEs M (fun r k => qOfSpin (s r k)) a δ
    (fun r k => qOfSpin_mem (hs r k)) ha
  convert hmain using 2
  funext r k
  exact (spinOfQ_qOfSpin (s r k)).symm

end Qatlib.Papers.HadamardAnn19.MainResults.GeneralEnergy
