/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Copyright: paper-layer formalization for SparseCIMat13.
Source: B. Toloui and P. J. Love, "Quantum Algorithms for Quantum Chemistry based on the
sparsity of the CI-matrix", arXiv:1312.2579 (2013), Section II p.4, Eqs. (9)-(10).
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# CI-matrix sparsity (arXiv:1312.2579, Eq. (9)-(10))

A configuration of `ne` electrons in `no` spin-orbitals is a `ne`-element subset of
`Fin no` (paper Eq. (17), `orb(x)`).  The Slater rules (Eqs. (5)-(8)) make the CI matrix
entry `⟨x|H|y⟩` nonzero only when `x` and `y` differ in at most two orbitals.  Hence the
number of nonzero entries in a row indexed by `x` is

  `d = C(ne,2) * C(no-ne,2) + C(ne,1) * C(no-ne,1) + 1`,   (Eq. (9))

the `+1` being the diagonal entry.  This file proves the counting statement and the
polynomial identities/bounds of Eq. (10).
-/

namespace Qatlib.Papers.SparseCIMat13.MainResults.CIMatrix

open Finset

/-- Paper Eq. (9): the total number of nonzero entries in each row of the CI matrix,
for a fixed configuration with `ne` occupied orbitals among `no` spin-orbitals. -/
def ciRowDegree (no ne : ℕ) : ℕ :=
  Nat.choose ne 2 * Nat.choose (no - ne) 2 + ne * (no - ne) + 1

/-- The complementary set of empty orbitals for a configuration `x`. -/
def emptyOrbitals {no : ℕ} (x : Finset (Fin no)) : Finset (Fin no) :=
  Finset.univ \ x

/-- Replace the deleted set `A ⊆ x` by the inserted set `B` of the complement:
`(x \ A) ∪ B`. This is the configuration reached from `x` by an orbital excitation
replacing the orbitals in `A` with those in `B`. -/
def orbitalReplacement {no : ℕ} (x : Finset (Fin no))
    (p : Finset (Fin no) × Finset (Fin no)) : Finset (Fin no) :=
  (x \ p.1) ∪ p.2

/-- Deleting `A` and inserting `B` recovers `x \ A` (used for the injection). -/
private lemma sdiff_union_left {α : Type*} [DecidableEq α] {x A B : Finset α}
    (hA : A ⊆ x) (hB : Disjoint B x) : x \ ((x \ A) ∪ B) = A := by
  ext a
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hax, hnot⟩
    by_contra haA
    exact hnot (Or.inl ⟨hax, haA⟩)
  · intro ha
    refine ⟨hA ha, ?_⟩
    rintro (⟨_, hna⟩ | hb)
    · exact hna ha
    · exact (Finset.disjoint_left.mp hB) hb (hA ha)

/-- Deleting `A` and inserting `B` recovers `B` after removing `x` (used for the injection). -/
private lemma sdiff_union_right {α : Type*} [DecidableEq α] {x A B : Finset α}
    (_hA : A ⊆ x) (hB : Disjoint B x) : ((x \ A) ∪ B) \ x = B := by
  ext a
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨h | h, hax⟩
    · exact absurd h.1 hax
    · exact h
  · intro ha
    exact ⟨Or.inr ha, fun hx => (Finset.disjoint_left.mp hB) ha hx⟩

/-- Undoing a replacement in both directions recovers `y` (used for the surjection). -/
private lemma replacement_self {α : Type*} [DecidableEq α] (x y : Finset α) :
    (x \ (x \ y)) ∪ (y \ x) = y := by
  ext a
  simp only [Finset.mem_sdiff, Finset.mem_union, not_and, not_not]
  tauto

/-- The number of configurations obtained from `x` (of size `ne`) by replacing exactly
`k` orbitals equals `C(ne,k) * C(no-ne,k)`: choose the `k` deleted occupied orbitals and
the `k` inserted empty orbitals.  This is the fibre count underlying Eq. (9)-(10). -/
theorem card_replacements (no ne k : ℕ) (x : Finset (Fin no)) (hx : x.card = ne) :
    ((Finset.univ : Finset (Finset (Fin no))).filter
        (fun y => y.card = ne ∧ (x \ y).card = k)).card
      = Nat.choose ne k * Nat.choose (no - ne) k := by
  classical
  set comp : Finset (Fin no) := Finset.univ \ x with hcompdef
  have hmemcomp : ∀ a, a ∈ comp ↔ a ∉ x := by
    intro a; simp [hcompdef]
  have hcomp : comp.card = no - ne := by
    rw [hcompdef, Finset.card_sdiff]
    simp [hx]
  set S : Finset (Finset (Fin no) × Finset (Fin no)) :=
    x.powersetCard k ×ˢ comp.powersetCard k with hSdef
  have hmemS : ∀ p ∈ S, p.1 ⊆ x ∧ p.1.card = k ∧ p.2 ⊆ comp ∧ p.2.card = k := by
    intro p hp
    rw [hSdef, Finset.mem_product] at hp
    exact ⟨(Finset.mem_powersetCard.mp hp.1).1, (Finset.mem_powersetCard.mp hp.1).2,
      (Finset.mem_powersetCard.mp hp.2).1, (Finset.mem_powersetCard.mp hp.2).2⟩
  have hinj : Set.InjOn (orbitalReplacement x) ↑S := by
    intro p hp q hq hpq
    have hp' := hmemS p hp
    have hq' := hmemS q hq
    have hpB : Disjoint p.2 x := by
      rw [Finset.disjoint_left]
      intro a ha hxa
      exact (hmemcomp a).mp (hp'.2.2.1 ha) hxa
    have hqB : Disjoint q.2 x := by
      rw [Finset.disjoint_left]
      intro a ha hxa
      exact (hmemcomp a).mp (hq'.2.2.1 ha) hxa
    have hpq' : (x \ p.1) ∪ p.2 = (x \ q.1) ∪ q.2 := by
      simpa only [orbitalReplacement] using hpq
    have h1 : p.1 = q.1 := by
      calc p.1 = x \ ((x \ p.1) ∪ p.2) := (sdiff_union_left hp'.1 hpB).symm
        _ = x \ ((x \ q.1) ∪ q.2) := by rw [hpq']
        _ = q.1 := sdiff_union_left hq'.1 hqB
    have h2 : p.2 = q.2 := by
      calc p.2 = ((x \ p.1) ∪ p.2) \ x := (sdiff_union_right hp'.1 hpB).symm
        _ = ((x \ q.1) ∪ q.2) \ x := by rw [hpq']
        _ = q.2 := sdiff_union_right hq'.1 hqB
    exact Prod.ext h1 h2
  have himage : S.image (orbitalReplacement x) =
      (Finset.univ.filter (fun y : Finset (Fin no) => y.card = ne ∧ (x \ y).card = k)) := by
    ext y
    constructor
    · intro hy
      obtain ⟨p, hpS, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨hpx, hpcard, -, hp2card⟩ := hmemS p hpS
      have hB : Disjoint p.2 x := by
        rw [Finset.disjoint_left]
        intro a ha hxa
        exact (hmemcomp a).mp ((hmemS p hpS).2.2.1 ha) hxa
      have hleft : x \ ((x \ p.1) ∪ p.2) = p.1 := sdiff_union_left hpx hB
      have hdisj : Disjoint (x \ p.1) p.2 := by
        rw [Finset.disjoint_left]
        intro a ha hb
        exact (hmemcomp a).mp ((hmemS p hpS).2.2.1 hb) (Finset.mem_sdiff.mp ha).1
      have hcard1 : (x \ p.1).card = ne - k := by
        rw [Finset.card_sdiff_of_subset hpx, hx, hpcard]
      have hk : k ≤ ne := by
        rw [← hx, ← hpcard]; exact Finset.card_le_card hpx
      have hycard : ((x \ p.1) ∪ p.2).card = ne := by
        rw [Finset.card_union_of_disjoint hdisj, hcard1, hp2card]
        omega
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · simpa only [orbitalReplacement] using hycard
      · simp only [orbitalReplacement]
        rw [hleft]
        exact hpcard
    · intro hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      obtain ⟨hycard, hyk⟩ := hy
      refine Finset.mem_image.mpr ⟨(x \ y, y \ x), ?_, ?_⟩
      · rw [hSdef, Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard]
        refine ⟨⟨Finset.sdiff_subset, hyk⟩, ?_, ?_⟩
        · intro a ha
          exact (hmemcomp a).mpr (Finset.mem_sdiff.mp ha).2
        · calc (y \ x).card = y.card - (x ∩ y).card := Finset.card_sdiff
            _ = x.card - (y ∩ x).card := by rw [hycard, hx, Finset.inter_comm]
            _ = (x \ y).card := (Finset.card_sdiff (s := y) (t := x)).symm
            _ = k := hyk
      · exact replacement_self x y
  calc (Finset.univ.filter (fun y : Finset (Fin no) => y.card = ne ∧ (x \ y).card = k)).card
      = (S.image (orbitalReplacement x)).card := by rw [himage]
    _ = S.card := Finset.card_image_of_injOn hinj
    _ = (x.powersetCard k).card * (comp.powersetCard k).card := by
        rw [hSdef, Finset.card_product]
    _ = Nat.choose ne k * Nat.choose (no - ne) k := by
        rw [Finset.card_powersetCard, Finset.card_powersetCard, hx, hcomp]

/-- Paper Eq. (9): the number of configurations connected to `x` by a Slater-rule
one- or two-orbital difference, i.e. the number of nonzero entries in the row of the
CI matrix indexed by `x`, equals `d`. -/
theorem ciRowDegree_eq_card_neighbours (no ne : ℕ) (x : Finset (Fin no)) (hx : x.card = ne) :
    ((Finset.univ : Finset (Finset (Fin no))).filter
        (fun y => y.card = ne ∧ (x \ y).card ≤ 2)).card = ciRowDegree no ne := by
  classical
  set s : Finset (Finset (Fin no)) :=
    Finset.univ.filter (fun y => y.card = ne ∧ (x \ y).card ≤ 2) with hsdef
  have hfiber : ∀ k, k ≤ 2 → (s.filter (fun y => (x \ y).card = k)).card =
      ((Finset.univ : Finset (Finset (Fin no))).filter
        (fun y => y.card = ne ∧ (x \ y).card = k)).card := by
    intro k hk
    congr 1
    ext y
    rw [hsdef]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩
  have hpart := Finset.card_eq_sum_card_fiberwise
    (s := s) (t := Finset.range 3) (f := fun y : Finset (Fin no) => (x \ y).card)
    (fun y hy => by
      rw [hsdef] at hy
      have hylt : (x \ y).card ≤ 2 := (Finset.mem_filter.mp hy).2.2
      exact Finset.mem_range.mpr (by show (x \ y).card < 3; omega))
  rw [hpart]
  have hsum : ∑ k ∈ Finset.range 3, (s.filter (fun y => (x \ y).card = k)).card
      = ∑ k ∈ Finset.range 3, Nat.choose ne k * Nat.choose (no - ne) k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hfiber k (by have := Finset.mem_range.mp hk; omega), card_replacements no ne k x hx]
  rw [hsum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp [Nat.choose_one_right]
  unfold ciRowDegree
  ring

/-- Paper Eq. (10), rational form: the row degree equals the quartic polynomial
`1/4 ne(ne-1)(no-ne)(no-ne-1) + ne(no-ne) + 1`. -/
theorem ciRowDegree_eq_expanded (no ne : ℕ) (h : ne ≤ no) :
    (ciRowDegree no ne : ℚ) =
      (ne : ℚ) * (ne - 1) * (no - ne) * (no - ne - 1) / 4 + (ne : ℚ) * (no - ne) + 1 := by
  unfold ciRowDegree
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  rw [Nat.cast_choose_two (K := ℚ), Nat.cast_choose_two (K := ℚ)]
  push_cast [Nat.cast_sub h]
  ring

/-- `d` is at most quadratic in `no` and quartic in `ne`; concretely
`d ≤ (no * ne + 1)^2` (both binomial factors are bounded by the corresponding square). -/
theorem ciRowDegree_le_sq (no ne : ℕ) : ciRowDegree no ne ≤ (no * ne + 1) ^ 2 := by
  unfold ciRowDegree
  have h1 : Nat.choose ne 2 ≤ ne ^ 2 := by
    rw [Nat.choose_two_right]
    calc ne * (ne - 1) / 2 ≤ ne * (ne - 1) := Nat.div_le_self _ _
      _ ≤ ne * ne := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = ne ^ 2 := (pow_two ne).symm
  have h2 : Nat.choose (no - ne) 2 ≤ (no - ne) ^ 2 := by
    rw [Nat.choose_two_right]
    calc (no - ne) * (no - ne - 1) / 2 ≤ (no - ne) * (no - ne - 1) := Nat.div_le_self _ _
      _ ≤ (no - ne) * (no - ne) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = (no - ne) ^ 2 := (pow_two (no - ne)).symm
  have h3 : (no - ne) ^ 2 ≤ no ^ 2 := Nat.pow_le_pow_left (Nat.sub_le _ _) 2
  have h4 : Nat.choose ne 2 * Nat.choose (no - ne) 2 ≤ ne ^ 2 * no ^ 2 :=
    Nat.mul_le_mul h1 (le_trans h2 h3)
  have h5 : ne * (no - ne) ≤ ne * no := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h6 : ne ^ 2 * no ^ 2 = (no * ne) ^ 2 := by ring
  nlinarith [h4, h5, h6, Nat.zero_le (no * ne)]

end Qatlib.Papers.SparseCIMat13.MainResults.CIMatrix
