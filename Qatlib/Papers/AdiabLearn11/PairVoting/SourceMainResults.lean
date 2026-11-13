/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Achievable Strong-Classifier Accuracy via Pair Voting

This module formalizes the finite-sample strong-classifier accuracy guarantees
of Section IV ("Achievable strong classifier accuracy") of Pudenz and Lidar on
quantum adiabatic machine learning over a finite input-output space `V` sampled
uniformly, with binary labels `y x ∈ {-1, 1}`, weak classifiers `h i x ∈ {-1, 1}`,
pointwise correctness indicators `c i x = h i x * y x ∈ {-1, 1}`, and weighted
majority vote `Vote h w x = sgn (∑ i, w i * h i x)`.

## Main statements

* `lemma1`: under the minimum-overlap identity for a pair `(j, j')`, the pair
  correctness sum `c j x + c j' x` is nonnegative with probability `1`.
* `lemma1a`: under the relaxed overlap identity with error `ε`, the pair
  correctness sum `c j x + c j' x` is nonnegative with probability `1 - ε`.
* `coverage_of_condition3` and `coverage_of_condition3a`: order-2 Bonferroni
  coverage of `V` from Conditions 3 and 3a.
* `theorem1_perfect` and `theorem2_perfect`: strong classifiers built from weak
  classifier pairs satisfying Conditions 1, 2, and 3 (or 3a) are perfect.
* `theorem3_epsperfect`: strong classifiers built from weak classifier pairs
  satisfying Conditions 1, 2a, and 3 are `ε`-perfect with `ε = ∑ p ∈ J, ε p`.

## References

* [Pudenz and Lidar, 2013][PudenzLidar2013], Section IV, Lemmas 1 and 1a,
  Theorems 1-3.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.AdiabLearn11.PairVoting

open Finset

/-! ## Uniform finite probability layer -/

/-- Uniform probability of a finite event over the input-output space `V`. -/
def Pr {V : Type*} [Fintype V] (s : Finset V) : ℚ :=
  (s.card : ℚ) / (Fintype.card V : ℚ)

/-- The full sample space has probability `1`. -/
@[simp] theorem Pr_univ {V : Type*} [Fintype V] [Nonempty V] :
    Pr (univ : Finset V) = 1 := by
  unfold Pr
  rw [Finset.card_univ, div_self]
  exact_mod_cast Fintype.card_ne_zero

/-- `Pr s = 1` if and only if the event `s` covers the entire finite space `V`. -/
theorem Pr_eq_one_iff {V : Type*} [Fintype V] [Nonempty V] (s : Finset V) :
    Pr s = 1 ↔ s = univ := by
  unfold Pr
  rw [div_eq_one_iff_eq (by exact_mod_cast Fintype.card_ne_zero)]
  constructor
  · intro h
    have hc : s.card = Fintype.card V := by exact_mod_cast h
    exact Finset.eq_of_subset_of_card_le (Finset.subset_univ s)
      (le_of_eq (by rw [Finset.card_univ]; exact hc.symm))
  · intro h
    rw [h, Finset.card_univ]

/-- Inclusion-exclusion for two finite events under uniform probability. -/
theorem Pr_union_add_inter {V : Type*} [Fintype V] [DecidableEq V] (s t : Finset V) :
    Pr (s ∪ t) + Pr (s ∩ t) = Pr s + Pr t := by
  unfold Pr
  have h : ((s ∪ t).card : ℚ) + ((s ∩ t).card : ℚ) = (s.card : ℚ) + (t.card : ℚ) := by
    rw [← Nat.cast_add, ← Nat.cast_add, Finset.card_union_add_card_inter]
  rw [← add_div, ← add_div, h]

/-- Uniform event probabilities are bounded above by `1`. -/
theorem Pr_le_one {V : Type*} [Fintype V] [Nonempty V] (s : Finset V) : Pr s ≤ 1 := by
  unfold Pr
  rw [div_le_one (by exact_mod_cast Fintype.card_pos)]
  exact_mod_cast Finset.card_le_univ s

/-- Uniform event probabilities are nonnegative. -/
theorem Pr_nonneg {V : Type*} [Fintype V] (s : Finset V) : 0 ≤ Pr s := by
  unfold Pr
  positivity

/-! ## Source objects and Conditions -/

/-- Correctness set `A_i = {x : c_i(x) = 1}` where classifier `i` is correct on `x`. -/
def CorrectSet {V ι : Type*} [Fintype V] (c : ι → V → ℤ) (i : ι) : Finset V :=
  univ.filter (fun x => c i x = 1)

/-- Joint correctness event `(c_j = 1) ∩ (c_{j'} = 1)` of a pair `p = (j, j')`. -/
def pairMeet {V ι : Type*} [Fintype V] [DecidableEq V] (c : ι → V → ℤ) (p : ι × ι) : Finset V :=
  CorrectSet c p.1 ∩ CorrectSet c p.2

/-- Condition 1 (Eq. (36)): weak classifiers in `A` exceed accuracy `1 / 2`. -/
def Condition1 {V ι : Type*} [Fintype V] (c : ι → V → ℤ) (A : Finset ι) : Prop :=
  ∀ i ∈ A, (1 / 2 : ℚ) < Pr (CorrectSet c i)

/-- Condition 2 (Eq. (38)): minimum-overlap joint-correctness identity. -/
def Condition2 {V ι : Type*} [Fintype V] [DecidableEq V]
    (c : ι → V → ℤ) (J : Finset (ι × ι)) : Prop :=
  ∀ p ∈ J, Pr (pairMeet c p) = Pr (CorrectSet c p.1) + Pr (CorrectSet c p.2) - 1

/-- Condition 2a (Eq. (51)): relaxed joint-correctness identity with overlap error `ε`. -/
def Condition2a {V ι : Type*} [Fintype V] [DecidableEq V]
    (c : ι → V → ℤ) (J : Finset (ι × ι)) (ε : ι × ι → ℚ) : Prop :=
  ∀ p ∈ J, Pr (pairMeet c p) = Pr (CorrectSet c p.1) + Pr (CorrectSet c p.2) - 1 + ε p

/-- Condition 3 (Eq. (39)): the pairs' joint-correctness regions cover `V` with
minimal pairwise overlap. -/
def Condition3 {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (c : ι → V → ℤ) (J : Finset (ι × ι)) : Prop :=
  (∑ p ∈ J, Pr (pairMeet c p))
      - (∑ p ∈ J, ∑ q ∈ J.filter (fun q => q ≠ p), Pr (pairMeet c p ∩ pairMeet c q)) = 1

/-- Condition 3a (Eq. (40)): the Condition-3 cover augmented by a stand-alone
classifier `a`. -/
def Condition3a {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (c : ι → V → ℤ) (J : Finset (ι × ι)) (a : ι) : Prop :=
  (∑ p ∈ J, Pr (pairMeet c p)) + Pr (CorrectSet c a)
      - (∑ p ∈ J, ∑ q ∈ J.filter (fun q => q ≠ p), Pr (pairMeet c p ∩ pairMeet c q))
      - (∑ p ∈ J, Pr (CorrectSet c a ∩ pairMeet c p)) = 1

/-! ## Sign vote, perfectness, and weights -/

/-- Three-valued integer sign with `sgn 0 = 0` for an inconclusive tie. -/
def sgn (t : ℤ) : ℤ := if 0 < t then 1 else if t < 0 then -1 else 0

/-- Positive integers have sign `1`. -/
theorem sgn_pos {t : ℤ} (h : 0 < t) : sgn t = 1 := by simp [sgn, h]

/-- Negative integers have sign `-1`. -/
theorem sgn_neg {t : ℤ} (h : t < 0) : sgn t = -1 := by
  simp [sgn, h, show ¬ (0 < t) by omega]

/-- Strong-classifier vote (Eq. (14)): `Q_w(x) = sgn (∑ i, w i * h i x)`. -/
def Vote {V ι : Type*} [Fintype ι] (h : ι → V → ℤ) (w : ι → ℤ) (x : V) : ℤ :=
  sgn (∑ i, w i * h i x)

/-- A strong classifier is perfect (Eq. (31)) if `Vote h w x = y x` everywhere. -/
def Perfect {V ι : Type*} [Fintype ι] (h : ι → V → ℤ) (y : V → ℤ) (w : ι → ℤ) : Prop :=
  ∀ x, Vote h w x = y x

/-- Binary weights of the pair-built strong classifier (Eq. (41)): `1` on every
index occurring in a pair of `J`, and `0` elsewhere. -/
def pairWeight {ι : Type*} [DecidableEq ι] (J : Finset (ι × ι)) : ι → ℤ :=
  fun i => if i ∈ (J.image Prod.fst ∪ J.image Prod.snd) then 1 else 0

/-- Binary weights for Theorem 2 (Condition 3a): the pair indices together with
the stand-alone classifier `a`. -/
def pairWeightA {ι : Type*} [DecidableEq ι] (J : Finset (ι × ι)) (a : ι) : ι → ℤ :=
  fun i => if i ∈ (J.image Prod.fst ∪ J.image Prod.snd ∪ {a}) then 1 else 0

/-- `ε`-perfectness (Definition 7): the weighted correctness sum is positive
with probability at least `1 - ε`. -/
def EpsPerfect {V ι : Type*} [Fintype V] [Fintype ι]
    (c : ι → V → ℤ) (w : ι → ℤ) (ε : ℚ) : Prop :=
  1 - ε ≤ Pr (univ.filter (fun x => 0 < ∑ i, w i * c i x))

/-- Positive weighted correctness sum everywhere implies perfect classification. -/
theorem perfect_of_corrsum_pos {V ι : Type*} [Fintype ι]
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
    rw [sgn_pos hp]
  · rw [hyx] at hp ⊢
    rw [mul_neg_one] at hp
    have hlt : (∑ i, w i * h i x) < 0 := by linarith
    rw [sgn_neg hlt]

/-! ## Correct-sum pointwise facts -/

/-- For `±1`-valued correctness indicators, `{x : 0 ≤ c_j(x) + c_{j'}(x)}` equals
the union of the two single-classifier correctness sets. -/
theorem filter_corr_nonneg_eq_union {V ι : Type*} [Fintype V] [DecidableEq V]
    (c : ι → V → ℤ) (hrange : ∀ i x, c i x = 1 ∨ c i x = -1) (j j' : ι) :
    univ.filter (fun x => 0 ≤ c j x + c j' x) = CorrectSet c j ∪ CorrectSet c j' := by
  ext x
  simp only [CorrectSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · intro h
    rcases hrange j x with h1 | h1 <;> rcases hrange j' x with h2 | h2 <;> omega
  · rintro (h | h)
    · rw [h]; have := hrange j' x; omega
    · rw [h]; have := hrange j x; omega

/-- Condition 2 for a pair `(j, j')` makes the pair correctness sum nonnegative
everywhere on `V`. -/
theorem pair_sum_nonneg_of_cond2 {V ι : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (c : ι → V → ℤ) (hrange : ∀ i x, c i x = 1 ∨ c i x = -1)
    (j j' : ι)
    (h2 : Pr (CorrectSet c j ∩ CorrectSet c j') = Pr (CorrectSet c j) + Pr (CorrectSet c j') - 1) :
    ∀ x, 0 ≤ c j x + c j' x := by
  have hun : Pr (CorrectSet c j ∪ CorrectSet c j') = 1 := by
    have h := Pr_union_add_inter (CorrectSet c j) (CorrectSet c j')
    linarith
  have huniv : CorrectSet c j ∪ CorrectSet c j' = univ := (Pr_eq_one_iff _).mp hun
  intro x
  have hx : x ∈ CorrectSet c j ∪ CorrectSet c j' := by rw [huniv]; exact mem_univ x
  rcases Finset.mem_union.mp hx with hmem | hmem
  · have hcj : c j x = 1 := by simpa [CorrectSet] using hmem
    have := hrange j' x
    omega
  · have hcj : c j' x = 1 := by simpa [CorrectSet] using hmem
    have := hrange j x
    omega

/-! ## Coverage lemmas -/

private lemma card_eq_sum_indicator {V : Type*} [Fintype V] [DecidableEq V]
    (s : Finset V) : (s.card : ℤ) = ∑ x : V, if x ∈ s then 1 else 0 := by
  simp

private lemma sum_card_eq_sum_multiplicity {V α : Type*} [Fintype V] [DecidableEq V]
    (J : Finset α) (S : α → Finset V) :
    (∑ p ∈ J, ((S p).card : ℤ)) =
      ∑ x : V, ((J.filter (fun p => x ∈ S p)).card : ℤ) := by
  simp_rw [card_eq_sum_indicator]
  rw [Finset.sum_comm]
  simp

private lemma sum_inter_card_eq_sum_multiplicity {V α : Type*}
    [Fintype V] [DecidableEq V] [DecidableEq α]
    (J : Finset α) (S : α → Finset V) :
    (∑ p ∈ J, ∑ q ∈ J.filter (fun q => q ≠ p), ((S p ∩ S q).card : ℤ)) =
      ∑ x : V, ((J.filter (fun p => x ∈ S p)).card : ℤ) *
        (((J.filter (fun p => x ∈ S p)).card : ℤ) - 1) := by
  simp_rw [card_eq_sum_indicator]
  simp_rw [Finset.sum_comm (s := J.filter _) (t := (univ : Finset V))]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  let T := J.filter (fun p => x ∈ S p)
  have hfilter (p : α) :
      (J.filter (fun q => q ≠ p)).filter (fun q => x ∈ S q) = T.erase p := by
    ext q
    simp [T, and_left_comm, and_comm]
  have hinner (p : α) :
      (∑ q ∈ J.filter (fun q => q ≠ p), if x ∈ S p ∩ S q then (1 : ℤ) else 0) =
        if x ∈ S p then ((T.erase p).card : ℤ) else 0 := by
    by_cases hp : x ∈ S p
    · simp [Finset.mem_inter, hp, hfilter]
    · simp [Finset.mem_inter, hp]
  simp_rw [hinner]
  rw [← Finset.sum_filter]
  change (∑ p ∈ T, ((T.erase p).card : ℤ)) = (T.card : ℤ) * ((T.card : ℤ) - 1)
  calc
    _ = ∑ _p ∈ T, ((T.card : ℤ) - 1) := by
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.card_erase_of_mem hp, Nat.cast_sub (Finset.card_pos.mpr ⟨p, hp⟩)]
      rfl
    _ = _ := by simp [mul_sub]

private lemma eq_one_of_sum_eq_card {V : Type*} [Fintype V]
    (f : V → ℤ) (hle : ∀ x, f x ≤ 1)
    (hsum : ∑ x, f x = (Fintype.card V : ℤ)) (x : V) : f x = 1 := by
  have hdef : ∑ y, (1 - f y) = 0 := by
    rw [Finset.sum_sub_distrib, hsum]
    simp
  have hx : 1 - f x ≤ ∑ y, (1 - f y) :=
    Finset.single_le_sum (fun y _ => sub_nonneg.mpr (hle y)) (Finset.mem_univ x)
  rw [hdef] at hx
  have := hle x
  omega

private lemma sum_inter_card_eq_sum_indicator_mul {V α : Type*}
    [Fintype V] [DecidableEq V] (J : Finset α) (S : α → Finset V) (T : Finset V) :
    (∑ p ∈ J, ((T ∩ S p).card : ℤ)) =
      ∑ x : V, (if x ∈ T then (1 : ℤ) else 0) *
        ((J.filter (fun p => x ∈ S p)).card : ℤ) := by
  rw [sum_card_eq_sum_multiplicity]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x ∈ T <;> simp [Finset.mem_inter, hx]

/-- Condition 3 implies that the pair-correctness events cover `V`
(Eqs. (46a)-(47)). -/
theorem coverage_of_condition3 {V ι : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    [DecidableEq ι] (c : ι → V → ℤ) (J : Finset (ι × ι))
    (h3 : Condition3 c J) : ∀ x, ∃ p ∈ J, x ∈ pairMeet c p := by
  have hn : (Fintype.card V : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hrat :
      ((∑ p ∈ J, ((pairMeet c p).card : ℚ)) -
        ∑ p ∈ J, ∑ q ∈ J.filter (fun q => q ≠ p),
          ((pairMeet c p ∩ pairMeet c q).card : ℚ)) / (Fintype.card V : ℚ) = 1 := by
    simpa only [Condition3, Pr, ← Finset.sum_div, ← sub_div] using h3
  have hcount :
      (∑ p ∈ J, ((pairMeet c p).card : ℤ)) -
        (∑ p ∈ J, ∑ q ∈ J.filter (fun q => q ≠ p),
          ((pairMeet c p ∩ pairMeet c q).card : ℤ)) = (Fintype.card V : ℤ) := by
    exact_mod_cast (div_eq_one_iff_eq hn).mp hrat
  rw [sum_card_eq_sum_multiplicity, sum_inter_card_eq_sum_multiplicity,
    ← Finset.sum_sub_distrib] at hcount
  intro x
  have hx := eq_one_of_sum_eq_card _ (fun y => by
    nlinarith [sq_nonneg (((J.filter (fun p => y ∈ pairMeet c p)).card : ℤ) - 1)])
    hcount x
  by_contra hmiss
  have hempty : J.filter (fun p => x ∈ pairMeet c p) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro p hp hpx
    exact hmiss ⟨p, hp, hpx⟩
  simp [hempty] at hx

/-- Condition 3a implies that the pair-correctness events together with the
stand-alone classifier `a` cover `V` (Eqs. (49)-(50)). -/
theorem coverage_of_condition3a {V ι : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    [DecidableEq ι] (c : ι → V → ℤ) (J : Finset (ι × ι)) (a : ι)
    (h3a : Condition3a c J a) :
    ∀ x, (∃ p ∈ J, x ∈ pairMeet c p) ∨ x ∈ CorrectSet c a := by
  have hn : (Fintype.card V : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hrat :
      ((∑ p ∈ J, ((pairMeet c p).card : ℚ)) + ((CorrectSet c a).card : ℚ) -
        (∑ p ∈ J, ∑ q ∈ J.filter (fun q => q ≠ p),
          ((pairMeet c p ∩ pairMeet c q).card : ℚ)) -
        (∑ p ∈ J, ((CorrectSet c a ∩ pairMeet c p).card : ℚ))) /
          (Fintype.card V : ℚ) = 1 := by
    simpa only [Condition3a, Pr, ← Finset.sum_div, ← add_div, ← sub_div] using h3a
  have hcount :
      (∑ p ∈ J, ((pairMeet c p).card : ℤ)) + ((CorrectSet c a).card : ℤ) -
        (∑ p ∈ J, ∑ q ∈ J.filter (fun q => q ≠ p),
          ((pairMeet c p ∩ pairMeet c q).card : ℤ)) -
        (∑ p ∈ J, ((CorrectSet c a ∩ pairMeet c p).card : ℤ)) =
          (Fintype.card V : ℤ) := by
    exact_mod_cast (div_eq_one_iff_eq hn).mp hrat
  rw [sum_card_eq_sum_multiplicity, card_eq_sum_indicator,
    sum_inter_card_eq_sum_multiplicity, sum_inter_card_eq_sum_indicator_mul,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib] at hcount
  intro x
  have hx := eq_one_of_sum_eq_card _ (fun y => by
    by_cases hy : y ∈ CorrectSet c a
    · simp only [ite_eq_left hy]
      by_cases hz : (J.filter (fun p => y ∈ pairMeet c p)).card = 0
      · simp [hz]
      · have hm : (1 : ℤ) ≤ ((J.filter (fun p => y ∈ pairMeet c p)).card : ℤ) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
        nlinarith
    · simp only [ite_eq_right hy]
      nlinarith [sq_nonneg (((J.filter (fun p => y ∈ pairMeet c p)).card : ℤ) - 1)])
    hcount x
  by_contra hmiss
  have ha : x ∉ CorrectSet c a := fun h => hmiss (Or.inr h)
  have hempty : J.filter (fun p => x ∈ pairMeet c p) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro p hp hpx
    exact hmiss (Or.inl ⟨p, hp, hpx⟩)
  simp [ha, hempty] at hx

/-! ## Lemma 1, Lemma 1a, and Theorems 1-3 -/

/-- **Lemma 1** (Eq. (42)): under Condition 1 and the Condition-2 overlap
identity for `(j, j')`, the pair correctness sum is nonnegative with
probability `1`. -/
theorem lemma1 {V ι : Type*} [Fintype V] [DecidableEq V]
    (c : ι → V → ℤ) (hrange : ∀ i x, c i x = 1 ∨ c i x = -1)
    (A : Finset ι) (j j' : ι)
    (_hcond1 : Condition1 c A)
    (h2 : Pr (CorrectSet c j ∩ CorrectSet c j') = Pr (CorrectSet c j) + Pr (CorrectSet c j') - 1) :
    Pr (univ.filter (fun x => 0 ≤ c j x + c j' x)) = 1 := by
  rw [filter_corr_nonneg_eq_union c hrange j j']
  have hu := Pr_union_add_inter (CorrectSet c j) (CorrectSet c j')
  linarith

/-- **Lemma 1a** (Eq. (52)): under Condition 1 and the relaxed Condition-2a
identity for `(j, j')`, the pair correctness sum is nonnegative with
probability `1 - ε`. -/
theorem lemma1a {V ι : Type*} [Fintype V] [DecidableEq V]
    (c : ι → V → ℤ) (hrange : ∀ i x, c i x = 1 ∨ c i x = -1)
    (A : Finset ι) (j j' : ι) (ε : ℚ)
    (_hcond1 : Condition1 c A)
    (h2a : Pr (CorrectSet c j ∩ CorrectSet c j')
        = Pr (CorrectSet c j) + Pr (CorrectSet c j') - 1 + ε) :
    Pr (univ.filter (fun x => 0 ≤ c j x + c j' x)) = 1 - ε := by
  rw [filter_corr_nonneg_eq_union c hrange j j']
  have hu := Pr_union_add_inter (CorrectSet c j) (CorrectSet c j')
  linarith

/-- **Theorem 1**: a strong classifier built from weak-classifier pairs
satisfying Conditions 1-3 with disjoint constituent indices is perfect. -/
theorem theorem1_perfect {V ι : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype ι] [DecidableEq ι]
    (h : ι → V → ℤ) (y : V → ℤ) (c : ι → V → ℤ)
    (hy : ∀ x, y x = 1 ∨ y x = -1)
    (hrange : ∀ i x, c i x = 1 ∨ c i x = -1)
    (hc : ∀ i x, c i x = h i x * y x)
    (A : Finset ι) (J : Finset (ι × ι))
    (_hcond1 : Condition1 c A) (hcond2 : Condition2 c J) (hcond3 : Condition3 c J)
    (hbook : ∀ x, ∑ i, pairWeight J i * c i x = ∑ p ∈ J, (c p.1 x + c p.2 x)) :
    Perfect h y (pairWeight J) := by
  apply perfect_of_corrsum_pos h y c (pairWeight J) hy hc
  intro x
  rw [hbook x]
  obtain ⟨p, hpJ, hpx⟩ := coverage_of_condition3 c J hcond3 x
  have hp2 : c p.1 x + c p.2 x = 2 := by
    simp only [pairMeet, CorrectSet, Finset.mem_inter, Finset.mem_filter,
      Finset.mem_univ, true_and] at hpx
    omega
  have hnonneg : ∀ q ∈ J, 0 ≤ c q.1 x + c q.2 x := by
    intro q hq
    have h2q : Pr (CorrectSet c q.1 ∩ CorrectSet c q.2)
        = Pr (CorrectSet c q.1) + Pr (CorrectSet c q.2) - 1 := by
      simpa [pairMeet] using hcond2 q hq
    exact pair_sum_nonneg_of_cond2 c hrange q.1 q.2 h2q x
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

/-- **Theorem 2**: a strong classifier built from weak-classifier pairs and a
stand-alone classifier `a` satisfying Conditions 1, 2, and 3a is perfect. -/
theorem theorem2_perfect {V ι : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype ι] [DecidableEq ι]
    (h : ι → V → ℤ) (y : V → ℤ) (c : ι → V → ℤ)
    (hy : ∀ x, y x = 1 ∨ y x = -1)
    (hrange : ∀ i x, c i x = 1 ∨ c i x = -1)
    (hc : ∀ i x, c i x = h i x * y x)
    (A : Finset ι) (J : Finset (ι × ι)) (a : ι)
    (_hcond1 : Condition1 c A) (hcond2 : Condition2 c J) (hcond3a : Condition3a c J a)
    (hbook : ∀ x, ∑ i, pairWeightA J a i * c i x
        = ∑ p ∈ J, (c p.1 x + c p.2 x) + c a x) :
    Perfect h y (pairWeightA J a) := by
  apply perfect_of_corrsum_pos h y c (pairWeightA J a) hy hc
  intro x
  rw [hbook x]
  have hnonneg : ∀ q ∈ J, 0 ≤ c q.1 x + c q.2 x := by
    intro q hq
    have h2q : Pr (CorrectSet c q.1 ∩ CorrectSet c q.2)
        = Pr (CorrectSet c q.1) + Pr (CorrectSet c q.2) - 1 := by
      simpa [pairMeet] using hcond2 q hq
    exact pair_sum_nonneg_of_cond2 c hrange q.1 q.2 h2q x
  rcases coverage_of_condition3a c J a hcond3a x with ⟨p, hpJ, hpx⟩ | ha
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

private lemma Pr_filter_add_filter_not {V : Type*} [Fintype V] [Nonempty V]
    (P : V → Prop) [DecidablePred P] :
    Pr (univ.filter P) + Pr (univ.filter (fun x => ¬ P x)) = 1 := by
  unfold Pr
  rw [← add_div, ← Nat.cast_add, Finset.card_filter_add_card_filter_not,
    Finset.card_univ, div_self]
  exact_mod_cast Fintype.card_ne_zero

private lemma Pr_mono {V : Type*} [Fintype V] {s t : Finset V} (hst : s ⊆ t) :
    Pr s ≤ Pr t := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card hst

private lemma Pr_biUnion_le {V α : Type*} [Fintype V] [DecidableEq V]
    (J : Finset α) (S : α → Finset V) : Pr (J.biUnion S) ≤ ∑ p ∈ J, Pr (S p) := by
  unfold Pr
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_biUnion_le (s := J) (t := S)

/-- **Theorem 3** (Eq. (55)): a strong classifier built from weak-classifier
pairs satisfying Conditions 1, 2a, and 3 is `ε`-perfect with
`ε = ∑ p ∈ J, ε p`. -/
theorem theorem3_epsperfect {V ι : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype ι] [DecidableEq ι]
    (c : ι → V → ℤ) (hrange : ∀ i x, c i x = 1 ∨ c i x = -1)
    (A : Finset ι) (J : Finset (ι × ι)) (ε : ι × ι → ℚ)
    (_hcond1 : Condition1 c A) (hcond2a : Condition2a c J ε) (hcond3 : Condition3 c J)
    (_hε : ∀ p ∈ J, 0 ≤ ε p)
    (hbook : ∀ x, ∑ i, pairWeight J i * c i x = ∑ p ∈ J, (c p.1 x + c p.2 x)) :
    EpsPerfect c (pairWeight J) (∑ p ∈ J, ε p) := by
  let B := univ.filter (fun x => (∑ p ∈ J, (c p.1 x + c p.2 x)) ≤ 0)
  let E := fun p : ι × ι => univ.filter (fun x => c p.1 x + c p.2 x < 0)
  have hsub : B ⊆ J.biUnion E := by
    intro x hx
    have hsum : (∑ p ∈ J, (c p.1 x + c p.2 x)) ≤ 0 := (Finset.mem_filter.mp hx).2
    obtain ⟨p, hp, hpx⟩ := coverage_of_condition3 c J hcond3 x
    have hp2 : c p.1 x + c p.2 x = 2 := by
      simp only [pairMeet, CorrectSet, Finset.mem_inter, Finset.mem_filter,
        Finset.mem_univ, true_and] at hpx
      omega
    by_contra hmiss
    have hnonneg : ∀ q ∈ J, 0 ≤ c q.1 x + c q.2 x := by
      intro q hq
      by_contra hneg
      apply hmiss
      exact Finset.mem_biUnion.mpr ⟨q, hq,
        Finset.mem_filter.mpr ⟨Finset.mem_univ x, lt_of_not_ge hneg⟩⟩
    have hle : c p.1 x + c p.2 x ≤ ∑ q ∈ J, (c q.1 x + c q.2 x) :=
      Finset.single_le_sum hnonneg hp
    omega
  have herror (p : ι × ι) (hp : p ∈ J) : Pr (E p) = ε p := by
    have hpair := lemma1a c hrange A p.1 p.2 (ε p) _hcond1
      (by simpa [pairMeet] using hcond2a p hp)
    have hcomp := Pr_filter_add_filter_not (fun x => 0 ≤ c p.1 x + c p.2 x)
    have he : univ.filter (fun x => ¬ 0 ≤ c p.1 x + c p.2 x) = E p := by
      ext x
      simp [E]
    rw [he] at hcomp
    linarith
  have hbound : Pr B ≤ ∑ p ∈ J, ε p := calc
    Pr B ≤ Pr (J.biUnion E) := Pr_mono hsub
    _ ≤ ∑ p ∈ J, Pr (E p) := Pr_biUnion_le J E
    _ = ∑ p ∈ J, ε p := Finset.sum_congr rfl herror
  have hcomp := Pr_filter_add_filter_not (fun x => 0 < ∑ p ∈ J, (c p.1 x + c p.2 x))
  have hB : univ.filter (fun x => ¬ 0 < ∑ p ∈ J, (c p.1 x + c p.2 x)) = B := by
    ext x
    simp [B]
  rw [hB] at hcomp
  unfold EpsPerfect
  simp_rw [hbook]
  linarith

end Qatlib.Papers.AdiabLearn11.PairVoting
