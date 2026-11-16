/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdiabLearn11.PairVoting.Coverage
public import Mathlib.Algebra.Order.Field.Basic
public import Lean.Elab.Tactic.Omega

@[expose] public section


/-! # Complete old closed classifier mathematics

The genuine old probability, sign-vote and perfect-classifier results are
preserved. Stronger helpers remove only unused Condition1 and advantage-set
arguments. Binary pair-weight bookkeeping stays explicit; it is not inferred
from the printed cover conditions.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.AdiabLearn11.PairVoting.Claims
open Models Finset
open scoped BigOperators
variable {V ι : Type*}

/-- The entire old Pr_univ mathematical conclusion, with its actual remaining hypotheses. -/
@[simp] theorem massAll [Fintype V] [Nonempty V] : Pr (univ : Finset V) = 1 := by
  unfold Pr
  rw [Finset.card_univ, div_self]
  exact_mod_cast Fintype.card_ne_zero

/-- The entire old Pr_eq_one_iff mathematical conclusion, with its actual remaining hypotheses. -/
theorem massOne [Fintype V] [Nonempty V] (s : Finset V) : Pr s = 1 ↔ s = univ := by
  unfold Pr
  rw [div_eq_one_iff_eq (by exact_mod_cast Fintype.card_ne_zero)]
  constructor
  · intro h
    have hc : s.card = Fintype.card V := by exact_mod_cast h
    exact Finset.eq_of_subset_of_card_le (Finset.subset_univ s)
      (le_of_eq (by rw [Finset.card_univ]; exact hc.symm))
  · intro h
    rw [h, Finset.card_univ]

/-- The entire old Pr_union_add_inter mathematical conclusion, with its actual remaining hypotheses. -/
theorem massUnion [Fintype V] [DecidableEq V] (s t : Finset V) :
    Pr (s ∪ t) + Pr (s ∩ t) = Pr s + Pr t := by
  unfold Pr
  have h : ((s ∪ t).card : ℚ) + ((s ∩ t).card : ℚ) = (s.card : ℚ) + (t.card : ℚ) := by
    rw [← Nat.cast_add, ← Nat.cast_add, Finset.card_union_add_card_inter]
  rw [← add_div, ← add_div, h]

/-- The entire old Pr_le_one mathematical conclusion, with its actual remaining hypotheses. -/
theorem massLeOne [Fintype V] [Nonempty V] (s : Finset V) : Pr s ≤ 1 := by
  unfold Pr
  rw [div_le_one (by exact_mod_cast Fintype.card_pos)]
  exact_mod_cast Finset.card_le_univ s

/-- The entire old Pr_nonneg mathematical conclusion, with its actual remaining hypotheses. -/
theorem massNonneg [Fintype V] (s : Finset V) : 0 ≤ Pr s := by
  unfold Pr
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- The entire old sgn_pos mathematical conclusion, with its actual remaining hypotheses. -/
theorem signPos  {t : ℤ} (h : 0 < t) : sgn t = 1 := by simp [sgn, h]

/-- The entire old sgn_neg mathematical conclusion, with its actual remaining hypotheses. -/
theorem signNeg  {t : ℤ} (h : t < 0) : sgn t = -1 := by
  simp [sgn, h, show ¬ (0 < t) by omega]

/-- The entire old perfect_of_corrsum_pos mathematical conclusion, with its actual remaining hypotheses. -/
theorem voteFromCorr [Fintype ι]
    (h : ι → V → ℤ) (y : V → ℤ) (c : ι → V → ℤ) (w : ι → ℤ)
    (hy : ∀ x, y x = 1 ∨ y x = -1)
    (hc : ∀ i x, c i x = h i x * y x)
    (hpos : ∀ x, 0 < ∑ i, w i * c i x) :
    Perfect h y w := by
  intro x
  show sgn (∑ i, w i * h i x) = y x
  have hfac : (∑ i, w i * c i x) = (∑ i, w i * h i x) * y x := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => by rw [hc i x]; ring)
  have hp := hpos x
  rw [hfac] at hp
  rcases hy x with hyx | hyx
  · rw [hyx] at hp ⊢
    rw [mul_one] at hp
    rw [signPos hp]
  · rw [hyx] at hp ⊢
    rw [mul_neg_one] at hp
    have hlt : (∑ i, w i * h i x) < 0 := by linarith
    rw [signNeg hlt]

/-- The entire old filter_corr_nonneg_eq_union mathematical conclusion, with its actual remaining hypotheses. -/
theorem pairFilter [Fintype V] [DecidableEq V] (c : ι → V → ℤ)
    (hrange : ∀ i x, c i x = 1 ∨ c i x = -1) (j j' : ι) :
    univ.filter (fun x => 0 ≤ c j x + c j' x) = CorrectSet c j ∪ CorrectSet c j' := by
  ext x
  simp only [CorrectSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · intro h
    rcases hrange j x with h1 | h1 <;> rcases hrange j' x with h2 | h2 <;> omega
  · rintro (h | h)
    · rw [h]; have := hrange j' x; omega
    · rw [h]; have := hrange j x; omega

/-- The entire old pair_sum_nonneg_of_cond2 mathematical conclusion, with its actual remaining hypotheses. -/
theorem pairNoFail [Fintype V] [DecidableEq V] [Nonempty V]
    (c : ι → V → ℤ) (hrange : ∀ i x, c i x = 1 ∨ c i x = -1)
    (j j' : ι)
    (h2 : Pr (CorrectSet c j ∩ CorrectSet c j') = Pr (CorrectSet c j) + Pr (CorrectSet c j') - 1) :
    ∀ x, 0 ≤ c j x + c j' x := by
  have hun : Pr (CorrectSet c j ∪ CorrectSet c j') = 1 := by
    have h := massUnion (CorrectSet c j) (CorrectSet c j')
    linarith
  have huniv : CorrectSet c j ∪ CorrectSet c j' = univ := (massOne _).mp hun
  intro x
  have hx : x ∈ CorrectSet c j ∪ CorrectSet c j' := by rw [huniv]; exact mem_univ x
  rcases Finset.mem_union.mp hx with hmem | hmem
  · have hcj : c j x = 1 := by simpa [CorrectSet] using hmem
    have := hrange j' x
    omega
  · have hcj : c j' x = 1 := by simpa [CorrectSet] using hmem
    have := hrange j x
    omega

/-- The entire old lemma1 mathematical conclusion, with its actual remaining hypotheses. -/
theorem lemmaOne [Fintype V] [DecidableEq V] (c : ι → V → ℤ) (hrange : ∀ i x, c i x = 1 ∨ c i x = -1)  (j j' : ι)
    (h2 : Pr (CorrectSet c j ∩ CorrectSet c j') = Pr (CorrectSet c j) + Pr (CorrectSet c j') - 1) :
    Pr (univ.filter (fun x => 0 ≤ c j x + c j' x)) = 1 := by
  rw [pairFilter c hrange j j']
  have hu := massUnion (CorrectSet c j) (CorrectSet c j')
  linarith

/-- The entire old lemma1a mathematical conclusion, with its actual remaining hypotheses. -/
theorem lemmaOneA [Fintype V] [DecidableEq V] (c : ι → V → ℤ) (hrange : ∀ i x, c i x = 1 ∨ c i x = -1)  (j j' : ι) (ε : ℚ)
    (h2a : Pr (CorrectSet c j ∩ CorrectSet c j')
        = Pr (CorrectSet c j) + Pr (CorrectSet c j') - 1 + ε) :
    Pr (univ.filter (fun x => 0 ≤ c j x + c j' x)) = 1 - ε := by
  rw [pairFilter c hrange j j']
  have hu := massUnion (CorrectSet c j) (CorrectSet c j')
  linarith

/-- The entire old theorem1_perfect mathematical conclusion, with its actual remaining hypotheses. -/
theorem perfectPairs [Fintype V] [DecidableEq V] [Nonempty V] [Fintype ι] [DecidableEq ι]
    (h : ι → V → ℤ) (y : V → ℤ) (c : ι → V → ℤ)
    (hy : ∀ x, y x = 1 ∨ y x = -1)
    (hrange : ∀ i x, c i x = 1 ∨ c i x = -1)
    (hc : ∀ i x, c i x = h i x * y x)  (J : Finset (ι × ι))  (hcond2 : Condition2 c J) (hcond3 : Condition3 c J)
    (hbook : ∀ x, ∑ i, pairWeight J i * c i x = ∑ p ∈ J, (c p.1 x + c p.2 x)) :
    Perfect h y (pairWeight J) := by
  apply voteFromCorr h y c (pairWeight J) hy hc
  intro x
  rw [hbook x]
  obtain ⟨p, hpJ, hpx⟩ := Coverage.covers c J hcond3 x
  have hp2 : c p.1 x + c p.2 x = 2 := by
    simp only [pairMeet, CorrectSet, Finset.mem_inter, Finset.mem_filter,
      Finset.mem_univ, true_and] at hpx
    omega
  have hnonneg : ∀ q ∈ J, 0 ≤ c q.1 x + c q.2 x := by
    intro q hq
    have h2q : Pr (CorrectSet c q.1 ∩ CorrectSet c q.2)
        = Pr (CorrectSet c q.1) + Pr (CorrectSet c q.2) - 1 := by
      simpa [pairMeet] using hcond2 q hq
    exact pairNoFail c hrange q.1 q.2 h2q x
  have hsplit : ∑ q ∈ J, (c q.1 x + c q.2 x)
      = (c p.1 x + c p.2 x) + ∑ q ∈ J.erase p, (c q.1 x + c q.2 x) := by
    have h := Finset.sum_erase_add (s := J)
      (f := fun q : ι × ι => c q.1 x + c q.2 x) hpJ
    calc ∑ q ∈ J, (c q.1 x + c q.2 x)
        = ∑ q ∈ J.erase p, (c q.1 x + c q.2 x) + (c p.1 x + c p.2 x) := h.symm
      _ = (c p.1 x + c p.2 x) + ∑ q ∈ J.erase p, (c q.1 x + c q.2 x) := add_comm _ _
  rw [hsplit, hp2]
  have hrest : 0 ≤ ∑ q ∈ J.erase p, (c q.1 x + c q.2 x) :=
    Finset.sum_nonneg (fun q hq => hnonneg q (Finset.mem_of_mem_erase hq))
  linarith

/-- The entire old theorem2_perfect mathematical conclusion, with its actual remaining hypotheses. -/
theorem perfectExtra [Fintype V] [DecidableEq V] [Nonempty V] [Fintype ι] [DecidableEq ι]
    (h : ι → V → ℤ) (y : V → ℤ) (c : ι → V → ℤ)
    (hy : ∀ x, y x = 1 ∨ y x = -1)
    (hrange : ∀ i x, c i x = 1 ∨ c i x = -1)
    (hc : ∀ i x, c i x = h i x * y x)  (J : Finset (ι × ι)) (a : ι)  (hcond2 : Condition2 c J) (hcond3a : Condition3a c J a)
    (hbook : ∀ x, ∑ i, pairWeightA J a i * c i x
        = ∑ p ∈ J, (c p.1 x + c p.2 x) + c a x) :
    Perfect h y (pairWeightA J a) := by
  apply voteFromCorr h y c (pairWeightA J a) hy hc
  intro x
  rw [hbook x]
  have hnonneg : ∀ q ∈ J, 0 ≤ c q.1 x + c q.2 x := by
    intro q hq
    have h2q : Pr (CorrectSet c q.1 ∩ CorrectSet c q.2)
        = Pr (CorrectSet c q.1) + Pr (CorrectSet c q.2) - 1 := by
      simpa [pairMeet] using hcond2 q hq
    exact pairNoFail c hrange q.1 q.2 h2q x
  rcases Coverage.coversExtra c J a hcond3a x with ⟨p, hpJ, hpx⟩ | ha
  · have hp2 : c p.1 x + c p.2 x = 2 := by
      simp only [pairMeet, CorrectSet, Finset.mem_inter, Finset.mem_filter,
        Finset.mem_univ, true_and] at hpx
      omega
    have hca : -1 ≤ c a x := by have := hrange a x; omega
    have hsplit : ∑ q ∈ J, (c q.1 x + c q.2 x)
        = (c p.1 x + c p.2 x) + ∑ q ∈ J.erase p, (c q.1 x + c q.2 x) := by
      have h := Finset.sum_erase_add (s := J)
        (f := fun q : ι × ι => c q.1 x + c q.2 x) hpJ
      calc ∑ q ∈ J, (c q.1 x + c q.2 x)
          = ∑ q ∈ J.erase p, (c q.1 x + c q.2 x) + (c p.1 x + c p.2 x) := h.symm
        _ = (c p.1 x + c p.2 x) + ∑ q ∈ J.erase p, (c q.1 x + c q.2 x) := add_comm _ _
    rw [hsplit, hp2]
    have hrest : 0 ≤ ∑ q ∈ J.erase p, (c q.1 x + c q.2 x) :=
      Finset.sum_nonneg (fun q hq => hnonneg q (Finset.mem_of_mem_erase hq))
    linarith
  · have hca1 : c a x = 1 := by simpa [CorrectSet] using ha
    have hpair : 0 ≤ ∑ p ∈ J, (c p.1 x + c p.2 x) :=
      Finset.sum_nonneg (fun q hq => hnonneg q hq)
    linarith

end Qatlib.Papers.AdiabLearn11.PairVoting.Claims
