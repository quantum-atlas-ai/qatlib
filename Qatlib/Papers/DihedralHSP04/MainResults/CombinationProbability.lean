/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DihedralHSP04.MainResults.CombinationCounting

/-!
# Joint distribution of mask labels

`pairForm` records the labels of two masks simultaneously. Distinct nonzero masks give a
surjective pair map with uniform fibers, yielding the product formula `uniformProb_pair_match`
for joint label events.

This development follows [Regev2004a].

## Main statements

* `pairForm_surjective`: distinct nonzero masks realize every pair of labels.
* `pairForm_fiber_card`: each joint label fiber has cardinality `(2 ^ l) ^ (l + 2)`.
* `uniformProb_pair_match`: joint matching has probability `2⁻ˡ · 2⁻ˡ`.

## References

* [Regev, 2004][Regev2004a]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.DihedralHSP04.MainResults

open scoped BigOperators

/-- The additive homomorphism recording the modular dot products with two masks. -/
def pairForm (l : ℕ) (b₁ b₂ : Mask l) :
    SampleSpace l →+ ZMod (2 ^ l) × ZMod (2 ^ l) :=
  (linForm l b₁).prod (linForm l b₂)

/-- Evaluating `pairForm` gives the pair of modular dot products. -/
theorem pairForm_apply (l : ℕ) (b₁ b₂ : Mask l) (y : SampleSpace l) :
    pairForm l b₁ b₂ y = (dotMod l b₁ y, dotMod l b₂ y) := rfl

/-- The sample supported at coordinate `j` with value `a` there. -/
def unitLabel (l : ℕ) (j : Fin (l + 4)) (a : ZMod (2 ^ l)) : SampleSpace l :=
  Function.update (0 : SampleSpace l) j a

/-- The dot product with a single-coordinate sample is `a` when the mask selects that coordinate
and zero otherwise. -/
theorem dotMod_unitLabel (l : ℕ) (b : Mask l) (j : Fin (l + 4))
    (a : ZMod (2 ^ l)) :
    dotMod l b (unitLabel l j a) = if b j then a else 0 := by
  unfold dotMod unitLabel
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hjne
    simp [Function.update_of_ne hjne, hjne]
  · intro hjnot
    exact absurd (Finset.mem_univ j) hjnot

/-- Evaluating the pair map on two distinct single-coordinate samples gives the two
corresponding sums of selected values. -/
theorem pairForm_unitLabels (l : ℕ) (b₁ b₂ : Mask l) {j k : Fin (l + 4)}
    (hjk : j ≠ k) (a c : ZMod (2 ^ l)) :
    pairForm l b₁ b₂ (unitLabel l j a + unitLabel l k c) =
      ((if b₁ j then a else 0) + (if b₁ k then c else 0),
        (if b₂ j then a else 0) + (if b₂ k then c else 0)) := by
  rw [pairForm_apply]
  have h₁ := map_add (linForm l b₁) (unitLabel l j a) (unitLabel l k c)
  have h₂ := map_add (linForm l b₂) (unitLabel l j a) (unitLabel l k c)
  simp only [linForm_apply] at h₁ h₂
  rw [h₁, h₂, dotMod_unitLabel, dotMod_unitLabel, dotMod_unitLabel,
    dotMod_unitLabel]

/-- The pair label map of two distinct nonzero masks is surjective. -/
theorem pairForm_surjective {l : ℕ} {b₁ b₂ : Mask l}
    (h₁ : b₁ ≠ zeroMask l) (h₂ : b₂ ≠ zeroMask l) (hne : b₁ ≠ b₂) :
    Function.Surjective (pairForm l b₁ b₂) := by
  rintro ⟨z₁, z₂⟩
  by_cases hP : ∃ j, b₁ j = true ∧ b₂ j = false
  · by_cases hQ : ∃ k, b₂ k = true ∧ b₁ k = false
    · obtain ⟨j, hj1, hj2⟩ := hP
      obtain ⟨k, hk2, hk1⟩ := hQ
      have hjk : j ≠ k := by
        rintro rfl
        rw [hj2] at hk2
        simp at hk2
      refine ⟨unitLabel l j z₁ + unitLabel l k z₂, ?_⟩
      rw [pairForm_unitLabels l b₁ b₂ hjk z₁ z₂]
      simp [hj1, hj2, hk1, hk2]
    · obtain ⟨j, hj1, hj2⟩ := hP
      obtain ⟨k, hk2⟩ := exists_true_of_ne_zero h₂
      have hk1 : b₁ k = true := by
        cases hbk : b₁ k
        · exact absurd ⟨k, hk2, hbk⟩ hQ
        · rfl
      have hjk : j ≠ k := by
        rintro rfl
        rw [hj2] at hk2
        simp at hk2
      refine ⟨unitLabel l j (z₁ - z₂) + unitLabel l k z₂, ?_⟩
      rw [pairForm_unitLabels l b₁ b₂ hjk (z₁ - z₂) z₂]
      simp [hj1, hj2, hk1, hk2]
  · by_cases hQ : ∃ k, b₂ k = true ∧ b₁ k = false
    · obtain ⟨k, hk2, hk1⟩ := hQ
      obtain ⟨j, hj1⟩ := exists_true_of_ne_zero h₁
      have hj2 : b₂ j = true := by
        cases hbj : b₂ j
        · exact absurd ⟨j, hj1, hbj⟩ hP
        · rfl
      have hjk : j ≠ k := by
        rintro rfl
        rw [hj1] at hk1
        simp at hk1
      refine ⟨unitLabel l j z₁ + unitLabel l k (z₂ - z₁), ?_⟩
      rw [pairForm_unitLabels l b₁ b₂ hjk z₁ (z₂ - z₁)]
      simp [hj1, hj2, hk1, hk2]
    · exfalso
      apply hne
      funext j
      cases hb1 : b₁ j <;> cases hb2 : b₂ j
      · rfl
      · exact absurd ⟨j, hb2, hb1⟩ hQ
      · exact absurd ⟨j, hb1, hb2⟩ hP
      · rfl

/-- The space of pairs of modular labels has cardinality `(2 ^ l) * (2 ^ l)`. -/
theorem natCard_outcome_pair (l : ℕ) :
    Nat.card (ZMod (2 ^ l) × ZMod (2 ^ l)) = (2 ^ l) * (2 ^ l) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_prod, ZMod.card]

/-- Each joint label fiber for distinct nonzero masks has cardinality `(2 ^ l) ^ (l + 2)`. See
[Regev2004a]. -/
theorem pairForm_fiber_card {l : ℕ} {b₁ b₂ : Mask l}
    (h₁ : b₁ ≠ zeroMask l) (h₂ : b₂ ≠ zeroMask l) (hne : b₁ ≠ b₂)
    (z₁ z₂ : ZMod (2 ^ l)) :
    (Finset.univ.filter
        (fun y : SampleSpace l => dotMod l b₁ y = z₁ ∧ dotMod l b₂ y = z₂)).card =
      (2 ^ l) ^ (l + 2) := by
  have hsurj := pairForm_surjective h₁ h₂ hne
  have hz : (z₁, z₂) ∈ Set.range (pairForm l b₁ b₂) := hsurj (z₁, z₂)
  have h0 : ((0 : ZMod (2 ^ l)), (0 : ZMod (2 ^ l))) ∈
      Set.range (pairForm l b₁ b₂) := ⟨0, map_zero _⟩
  have hsame := AddMonoidHom.card_fiber_eq_of_mem_range (pairForm l b₁ b₂) hz h0

  have hleft :
      (Finset.univ.filter
          (fun y : SampleSpace l => dotMod l b₁ y = z₁ ∧ dotMod l b₂ y = z₂)).card =
        (Finset.univ.filter
          (fun y : SampleSpace l => pairForm l b₁ b₂ y = (z₁, z₂))).card := by
    congr 1
  have hright :
      (Finset.univ.filter
          (fun y : SampleSpace l =>
            pairForm l b₁ b₂ y = ((0 : ZMod (2 ^ l)), (0 : ZMod (2 ^ l))))).card =
        Nat.card (pairForm l b₁ b₂).ker := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
  have hker : Nat.card (pairForm l b₁ b₂).ker = (2 ^ l) ^ (l + 2) := by
    have hmul := (pairForm l b₁ b₂).ker.card_mul_index
    rw [AddSubgroup.index_ker] at hmul
    have hrange : Nat.card (pairForm l b₁ b₂).range = (2 ^ l) * (2 ^ l) := by
      have htop : (pairForm l b₁ b₂).range = ⊤ :=
        AddMonoidHom.range_eq_top.mpr hsurj
      rw [htop]
      rw [show Nat.card (⊤ : AddSubgroup (ZMod (2 ^ l) × ZMod (2 ^ l))) =
          Nat.card (ZMod (2 ^ l) × ZMod (2 ^ l)) from
        Nat.card_congr (AddSubgroup.topEquiv).toEquiv]
      exact natCard_outcome_pair l
    rw [hrange, natCard_sampleSpace] at hmul
    have hfac : (2 ^ l) ^ (l + 4) = ((2 ^ l) * (2 ^ l)) * (2 ^ l) ^ (l + 2) := by
      have h2 : (2 ^ l) * (2 ^ l) = (2 ^ l) ^ 2 := by ring
      rw [h2, ← pow_add]
      congr 1
      omega
    rw [hfac] at hmul
    rw [mul_comm (Nat.card (pairForm l b₁ b₂).ker) ((2 ^ l) * (2 ^ l))] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hmul
  rw [hleft, hsame, hright, hker]

/-- The probability of a predicate under the uniform distribution on a finite type, expressed as
a real cardinality ratio. -/
noncomputable def uniformProb {Ω : Type*} [Fintype Ω] (p : Ω → Prop) : ℝ :=
  (Nat.card {x : Ω // p x} : ℝ) / (Nat.card Ω : ℝ)

/-- Uniform probability equals the cardinality of the filtered universe divided by the
cardinality of the ambient type. -/
theorem uniformProb_eq_filter {Ω : Type*} [Fintype Ω] (p : Ω → Prop) [DecidablePred p] :
    uniformProb p = ((Finset.univ.filter p).card : ℝ) / (Nat.card Ω : ℝ) := by
  unfold uniformProb
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- For distinct nonzero masks, the probability of any specified pair of labels is the product
of two factors `((2 : ℝ) ^ l)⁻¹`. See [Regev2004a]. -/
theorem uniformProb_pair_match {l : ℕ} {b₁ b₂ : Mask l}
    (h₁ : b₁ ≠ zeroMask l) (h₂ : b₂ ≠ zeroMask l) (hne : b₁ ≠ b₂)
    (z₁ z₂ : ZMod (2 ^ l)) :
    uniformProb (fun y : SampleSpace l =>
        dotMod l b₁ y = z₁ ∧ dotMod l b₂ y = z₂) =
      (((2 : ℝ) ^ l)⁻¹) * (((2 : ℝ) ^ l)⁻¹) := by
  rw [uniformProb_eq_filter]
  rw [pairForm_fiber_card h₁ h₂ hne z₁ z₂, natCard_sampleSpace]
  have hA : (((2 ^ l) ^ (l + 2) : ℕ) : ℝ) = ((2 : ℝ) ^ l) ^ (l + 2) := by
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  have hB : (((2 ^ l) ^ (l + 4) : ℕ) : ℝ) = ((2 : ℝ) ^ l) ^ (l + 4) := by
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [hA, hB]
  have hexp : ((2 : ℝ) ^ l) ^ (l + 4) = ((2 : ℝ) ^ l) ^ (l + 2) * (((2 : ℝ) ^ l) ^ 2) := by
    rw [show (l : ℕ) + 4 = (l + 2) + 2 by omega, pow_add]
  rw [hexp, pow_two]
  have hq : ((2 : ℝ) ^ l) ≠ 0 := by positivity
  have hq2 : (((2 : ℝ) ^ l) ^ (l + 2)) ≠ 0 := by positivity
  field_simp

end Qatlib.Papers.DihedralHSP04.MainResults
