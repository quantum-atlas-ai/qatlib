/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BoolHidShift11.InputModel.BHSPModel.SourceBHSP
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery
import Mathlib.Logic.Equiv.Fintype

set_option backward.isDefEq.respectTransparency false

/-!
# Classical Query Lower Bound for Random Boolean Hidden Shift Instances

This module formalizes the randomized classical query lower bound for the Boolean
hidden shift problem over uniformly random Boolean functions `f : Z_2^n → Bool`
and hidden shifts `s ∈ Z_2^n`.

## Main statements

* `card_pairwiseDiff_le`: the set of pairwise XOR differences of `k` queried points
  has cardinality at most `k ^ 2`.
* `classical_success_forces_queries`: arithmetic deduction `2 ^ n ≤ 3 * t ^ 2 + 2`
  from the transcript success-probability bound `(t ^ 2 + 1) / (2 ^ n - t ^ 2) ≥ 1 / 2`.
* `source_lemma2_classical_lower_bound`: any `t`-query randomized classical decision
  tree achieving average success probability at least `1 / 2` over uniform `(f, s)`
  satisfies `2 ^ n ≤ 3 * t ^ 2 + 2`.

## References

* [Gavinsky, Roetteler, and Roland, 2011][GavinskyRoettelerRoland2011], Lemma 2, pp. 4--5.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open scoped BigOperators ENNReal Classical

namespace Qatlib.Papers.BoolHidShift11.RandomFunctions.ClassicalLowerBound

open Qatlib.Papers.BoolHidShift11.InputModel.BHSPModel

/-- The set `S_k = {X_i ⊕ X_j | i, j ∈ Fin k}` of pairwise XOR differences of `k`
queried points. -/
def pairwiseDiff {n k : ℕ} (X : Fin k → Reg n) : Finset (Reg n) :=
  (Finset.univ : Finset (Fin k × Fin k)).image (fun p => regXor (X p.1) (X p.2))

/-- There are at most `k ^ 2` distinct pairwise XOR differences among `k` points. -/
theorem card_pairwiseDiff_le {n k : ℕ} (X : Fin k → Reg n) :
    (pairwiseDiff X).card ≤ k ^ 2 := by
  calc
    (pairwiseDiff X).card ≤ (Finset.univ : Finset (Fin k × Fin k)).card :=
      Finset.card_image_le
    _ = k ^ 2 := by
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
      ring

/-- If `(t ^ 2 + 1) / (2 ^ n - t ^ 2) ≥ 1 / 2` with `t ^ 2 < 2 ^ n`, then
`2 ^ n ≤ 3 * t ^ 2 + 2`. -/
theorem classical_success_forces_queries {n t : ℕ}
    (hden : (t : ℝ) ^ 2 < (2 : ℝ) ^ n)
    (hsucc : (1 / 2 : ℝ) ≤
      ((t : ℝ) ^ 2 + 1) / ((2 : ℝ) ^ n - (t : ℝ) ^ 2)) :
    (2 : ℝ) ^ n ≤ 3 * (t : ℝ) ^ 2 + 2 := by
  have hden_pos : (0 : ℝ) < (2 : ℝ) ^ n - (t : ℝ) ^ 2 := by linarith
  have h1 : (1 / 2 : ℝ) * ((2 : ℝ) ^ n - (t : ℝ) ^ 2)
      ≤ (t : ℝ) ^ 2 + 1 :=
    (le_div_iff₀ hden_pos).mp hsucc
  linarith

/-- The combined two-function oracle `(b, x) ↦ if b then f(x ⊕ s) else f(x)`. -/
def oracleOf {n : ℕ} (f : Reg n → Bool) (s : Reg n) : Bool × Reg n → Bool :=
  fun q => if q.1 then f (regXor q.2 s) else f q.2

/-- Average success probability of a randomized Boolean decision-tree program over
uniformly random `(f, s)`. -/
noncomputable def avgSuccess {n : ℕ}
    (prog : PMF (BoolQueryTree (Bool × Reg n) (Reg n))) : ℝ :=
  (∑ f : Reg n → Bool, ∑ s : Reg n,
      (BoolQueryTree.SuccessProb prog (oracleOf f s) (fun out => out = s)).toReal)
    / ((Fintype.card (Reg n → Bool) : ℝ) * (Fintype.card (Reg n) : ℝ))

private abbrev Transcript (n : ℕ) := List ((Bool × Reg n) × Bool)

private def consistent {n : ℕ} (C : Transcript n) (f : Reg n → Bool) (s : Reg n) :
    Prop := ∀ e ∈ C, oracleOf f s e.1 = e.2

private def points {n : ℕ} (C : Transcript n) (b : Bool) : Finset (Reg n) :=
  ((C.filter (fun e => e.1.1 = b)).map (fun e => e.1.2)).toFinset

private def bad {n : ℕ} (C : Transcript n) : Finset (Reg n) :=
  ((points C false) ×ˢ (points C true)).image (fun p => regXor p.1 p.2)

private def good {n : ℕ} (C : Transcript n) : Finset ((Reg n → Bool) × Reg n) := by
  classical
  exact Finset.univ.filter (fun p => consistent C p.1 p.2 ∧ p.2 ∉ bad C)

private def wins {n : ℕ} (C : Transcript n)
    (tr : BoolQueryTree (Bool × Reg n) (Reg n)) : Finset ((Reg n → Bool) × Reg n) :=
  (good C).filter (fun p => (BoolQueryTree.Run (oracleOf p.1 p.2) tr).1 = p.2)

private lemma xor_cancel_right {n : ℕ} (x s : Reg n) : regXor (regXor x s) s = x := by
  rw [regXor_assoc, regXor_self, regXor_zero_right]

private lemma mem_points {n : ℕ} (C : Transcript n) (b : Bool) (x : Reg n) :
    x ∈ points C b ↔ ∃ a, ((b, x), a) ∈ C := by
  simp only [points, List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨b', x'⟩, a⟩, ⟨he, hb⟩, hx⟩
    change b' = b at hb
    change x' = x at hx
    subst b'; subst x'
    exact ⟨a, he⟩
  · rintro ⟨a, ha⟩
    exact ⟨((b, x), a), ⟨ha, rfl⟩, rfl⟩

private lemma points_cons {n : ℕ} (C : Transcript n) (q : Bool × Reg n)
    (a b : Bool) : points ((q, a) :: C) b =
      if q.1 = b then insert q.2 (points C b) else points C b := by
  rcases q with ⟨c, x⟩
  cases c <;> cases b <;> simp [points]

private lemma points_card_le {n : ℕ} (C : Transcript n) :
    (points C false).card + (points C true).card ≤ C.length := by
  induction C with
  | nil => simp [points]
  | cons e C ih =>
    rcases e with ⟨⟨b, x⟩, a⟩
    cases b <;> simp only [points_cons, Bool.false_eq_true, Bool.true_eq_false,
      ↓reduceIte, List.length_cons] <;>
      have := Finset.card_insert_le x (points C false) <;>
      have := Finset.card_insert_le x (points C true) <;> omega

private lemma bad_card_le {n : ℕ} (C : Transcript n) : (bad C).card ≤ C.length ^ 2 := by
  have hp := points_card_le C
  calc
    (bad C).card ≤ ((points C false) ×ˢ (points C true)).card := Finset.card_image_le
    _ = (points C false).card * (points C true).card := Finset.card_product _ _
    _ ≤ C.length ^ 2 := by nlinarith

private lemma bad_mono {n : ℕ} (C : Transcript n) (q : Bool × Reg n) (a : Bool) :
    bad C ⊆ bad ((q, a) :: C) := by
  apply Finset.image_subset_image
  apply Finset.product_subset_product <;>
    intro x hx <;> rw [mem_points] at hx ⊢ <;>
    obtain ⟨v, hv⟩ := hx <;> exact ⟨v, List.mem_cons_of_mem _ hv⟩

private lemma bad_answer {n : ℕ} (C : Transcript n) (q : Bool × Reg n) (a : Bool) :
    bad ((q, a) :: C) = bad ((q, false) :: C) := by
  simp only [bad, points_cons]

private lemma new_bad_card_le {n : ℕ} (C : Transcript n) (q : Bool × Reg n) :
    (bad ((q, false) :: C) \ bad C).card ≤ C.length := by
  have hp := points_card_le C
  rcases q with ⟨b, x⟩
  cases b
  · have hsub : bad (((false, x), false) :: C) \ bad C ⊆
        (points C true).image (fun y => regXor x y) := by
      intro s hs
      obtain ⟨hs, hn⟩ := Finset.mem_sdiff.mp hs
      obtain ⟨⟨y, z⟩, hyz, rfl⟩ := Finset.mem_image.mp hs
      simp only [Finset.mem_product, points_cons, ↓reduceIte, Finset.mem_insert] at hyz
      rcases hyz.1 with rfl | hy
      · exact Finset.mem_image.mpr ⟨z, hyz.2, rfl⟩
      · exact False.elim (hn (Finset.mem_image.mpr
          ⟨(y, z), Finset.mem_product.mpr ⟨hy, hyz.2⟩, rfl⟩))
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by omega))
  · have hsub : bad (((true, x), false) :: C) \ bad C ⊆
        (points C false).image (fun y => regXor y x) := by
      intro s hs
      obtain ⟨hs, hn⟩ := Finset.mem_sdiff.mp hs
      obtain ⟨⟨y, z⟩, hyz, rfl⟩ := Finset.mem_image.mp hs
      simp only [Finset.mem_product, points_cons, ↓reduceIte, Finset.mem_insert] at hyz
      rcases hyz.2 with rfl | hz
      · exact Finset.mem_image.mpr ⟨y, hyz.1, rfl⟩
      · exact False.elim (hn (Finset.mem_image.mpr
          ⟨(y, z), Finset.mem_product.mpr ⟨hyz.1, hz⟩, rfl⟩))
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by omega))

private def queryLocation {n : ℕ} (s : Reg n) (q : Bool × Reg n) : Reg n :=
  if q.1 then regXor q.2 s else q.2

private lemma queryLocation_injective {n : ℕ} (C : Transcript n) (s : Reg n)
    (hs : s ∉ bad C) :
    Function.Injective (fun q : {q : Bool × Reg n // q.2 ∈ points C q.1} =>
      queryLocation s q.1) := by
  rintro ⟨⟨b, x⟩, hx⟩ ⟨⟨c, y⟩, hy⟩ h
  apply Subtype.ext
  cases b <;> cases c
  · simpa [queryLocation] using h
  · exfalso
    apply hs
    apply Finset.mem_image.mpr
    refine ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, ?_⟩
    have hxy : x = regXor y s := by simpa [queryLocation] using h
    rw [hxy, regXor_comm y s, xor_cancel_right]
  · exfalso
    apply hs
    apply Finset.mem_image.mpr
    refine ⟨(y, x), Finset.mem_product.mpr ⟨hy, hx⟩, ?_⟩
    have hxy : regXor x s = y := by simpa [queryLocation] using h
    rw [← hxy, regXor_comm x s, xor_cancel_right]
  · have hh := congrArg (fun z => regXor z s) h
    simpa [queryLocation, xor_cancel_right] using hh

private lemma count_consistent_eq {n : ℕ} (C : Transcript n) (s₁ s₂ : Reg n)
    (hs₁ : s₁ ∉ bad C) (hs₂ : s₂ ∉ bad C) :
    (Finset.univ.filter (fun f : Reg n → Bool => consistent C f s₁)).card =
      (Finset.univ.filter (fun f : Reg n → Bool => consistent C f s₂)).card := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun q : {q : Bool × Reg n // q.2 ∈ points C q.1} => queryLocation s₁ q.1)
    (fun q : {q : Bool × Reg n // q.2 ∈ points C q.1} => queryLocation s₂ q.1)
    (queryLocation_injective C s₁ hs₁) (queryLocation_injective C s₂ hs₂)
  have hrun (f : Reg n → Bool) (e : (Bool × Reg n) × Bool) (he : e ∈ C) :
      oracleOf (f ∘ σ) s₁ e.1 = oracleOf f s₂ e.1 := by
    have hm : e.1.2 ∈ points C e.1.1 :=
      (mem_points C e.1.1 e.1.2).mpr ⟨e.2, he⟩
    have hh := congrArg f (hσ ⟨e.1, hm⟩)
    cases hb : e.1.1 <;> simpa [oracleOf, queryLocation, Function.comp_apply, hb] using hh
  have hcons (f : Reg n → Bool) :
      consistent C (f ∘ σ) s₁ ↔ consistent C f s₂ := by
    constructor
    · intro h e he
      rw [← hrun f e he]
      exact h e he
    · intro h e he
      rw [hrun f e he]
      exact h e he
  let e := σ.symm.arrowCongr (Equiv.refl Bool)
  symm
  apply Finset.card_bijective e e.bijective
  intro f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (hcons f).symm

private lemma uniform_fiber_count_le {A B : Type*} [Fintype B] [DecidableEq B]
    (G : Finset (A × B)) (E S : Finset B) (c D : ℕ)
    (hgood : ∀ p ∈ G, p.2 ∉ E)
    (hcount : ∀ s ∉ E, (G.filter (fun p => p.2 = s)).card = c)
    (hD : D ≤ Fintype.card B - E.card) :
    (G.filter (fun p => p.2 ∈ S)).card * D ≤ S.card * G.card := by
  classical
  have hfull : G.card = (Fintype.card B - E.card) * c := by
    calc
      G.card = ∑ s ∈ Eᶜ, (G.filter (fun p => p.2 = s)).card :=
        Finset.card_eq_sum_card_fiberwise
          (fun p hp => Finset.mem_compl.mpr (hgood p hp))
      _ = Eᶜ.card * c := Finset.sum_const_nat
        (fun s hs => hcount s (Finset.mem_compl.mp hs))
      _ = (Fintype.card B - E.card) * c := by rw [Finset.card_compl]
  have hfiber (s : B) : (G.filter (fun p => p.2 = s)).card ≤ c := by
    by_cases hs : s ∈ E
    · have hempty : G.filter (fun p => p.2 = s) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        obtain ⟨hpG, hpEq⟩ := Finset.mem_filter.mp hp
        apply hgood p hpG
        simpa only [hpEq] using hs
      rw [hempty, Finset.card_empty]
      exact Nat.zero_le c
    · exact (hcount s hs).le
  have hselected : (G.filter (fun p => p.2 ∈ S)).card ≤ S.card * c := by
    rw [← Finset.sum_card_fiberwise_eq_card_filter G S Prod.snd]
    calc
      ∑ s ∈ S, (G.filter (fun p => p.2 = s)).card ≤ ∑ _s ∈ S, c :=
        Finset.sum_le_sum (fun s _hs => hfiber s)
      _ = S.card * c := by simp
  calc
    (G.filter (fun p => p.2 ∈ S)).card * D ≤ (S.card * c) * D :=
      Nat.mul_le_mul_right D hselected
    _ = S.card * (D * c) := by ring
    _ ≤ S.card * ((Fintype.card B - E.card) * c) :=
      Nat.mul_le_mul_left S.card (Nat.mul_le_mul_right c hD)
    _ = S.card * G.card := by rw [hfull]

private lemma good_fiber {n : ℕ} (C : Transcript n) (s : Reg n) (hs : s ∉ bad C) :
    ((good C).filter (fun p => p.2 = s)).card =
      (Finset.univ.filter (fun f : Reg n → Bool => consistent C f s)).card := by
  apply Finset.card_nbij' Prod.fst (fun f => (f, s))
  · intro p hp
    obtain ⟨hg, he⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      he ▸ (Finset.mem_filter.mp hg).2.1⟩
  · intro f hf
    have hc := (Finset.mem_filter.mp hf).2
    change (f, s) ∈ (good C).filter (fun p => p.2 = s)
    simp [good, hc, hs]
  · intro p hp
    exact Prod.ext rfl (Finset.mem_filter.mp hp).2.symm
  · intro f _
    rfl

private lemma good_count_le {n t : ℕ} (C : Transcript n) (S : Finset (Reg n))
    (hlen : C.length ≤ t) (ht : t ^ 2 < 2 ^ n) :
    ((good C).filter (fun p => p.2 ∈ S)).card * (2 ^ n - t ^ 2) ≤
      S.card * (good C).card := by
  have hsq : C.length ^ 2 ≤ t ^ 2 := Nat.pow_le_pow_left hlen 2
  have hcard : (bad C).card < Fintype.card (Reg n) := by
    rw [card_reg]
    exact (bad_card_le C).trans_lt (hsq.trans_lt ht)
  obtain ⟨s₀, hs₀⟩ : ∃ s : Reg n, s ∉ bad C := by
    by_contra h
    have hall : bad C = Finset.univ := by ext s; simp_all
    simp [hall] at hcard
  apply uniform_fiber_count_le (good C) (bad C) S
    (Finset.univ.filter (fun f : Reg n → Bool => consistent C f s₀)).card
    (2 ^ n - t ^ 2)
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.2
  · intro s hs
    rw [good_fiber C s hs]
    exact count_consistent_eq C s s₀ hs hs₀
  · rw [card_reg]
    exact Nat.sub_le_sub_left ((bad_card_le C).trans hsq) _

private lemma mem_good_cons {n : ℕ} (C : Transcript n) (q : Bool × Reg n)
    (a : Bool) (p : (Reg n → Bool) × Reg n) :
    p ∈ good ((q, a) :: C) ↔ p ∈ good C ∧
      oracleOf p.1 p.2 q = a ∧ p.2 ∉ bad ((q, false) :: C) := by
  simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [bad_answer C q a]
  have hm := bad_mono C q false
  simp only [consistent, List.forall_mem_cons]
  constructor
  · rintro ⟨⟨ha, hc⟩, hb⟩
    exact ⟨⟨hc, fun h => hb (hm h)⟩, ha, hb⟩
  · rintro ⟨⟨hc, _⟩, ha, hb⟩
    exact ⟨⟨ha, hc⟩, hb⟩

private lemma good_children_card {n : ℕ} (C : Transcript n) (q : Bool × Reg n) :
    (good ((q, false) :: C)).card + (good ((q, true) :: C)).card ≤
      (good C).card := by
  rw [← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact ((mem_good_cons C q false p).mp hp).1
    · exact ((mem_good_cons C q true p).mp hp).1
  · apply Finset.disjoint_left.mpr
    intro p hf ht
    have hf := ((mem_good_cons C q false p).mp hf).2.1
    have ht := ((mem_good_cons C q true p).mp ht).2.1
    exact Bool.false_ne_true (hf.symm.trans ht)

private lemma wins_ask_card {n : ℕ} (C : Transcript n) (q : Bool × Reg n)
    (trF trT : BoolQueryTree (Bool × Reg n) (Reg n)) :
    (wins C (.ask q trF trT)).card ≤
      ((good C).filter (fun p => p.2 ∈ bad ((q, false) :: C) \ bad C)).card +
        (wins ((q, false) :: C) trF).card + (wins ((q, true) :: C) trT).card := by
  apply (Finset.card_le_card (show wins C (.ask q trF trT) ⊆
      ((good C).filter (fun p => p.2 ∈ bad ((q, false) :: C) \ bad C)) ∪
        wins ((q, false) :: C) trF ∪ wins ((q, true) :: C) trT from ?_)).trans
    ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  intro p hp
  obtain ⟨hg, hw⟩ := Finset.mem_filter.mp hp
  by_cases hb : p.2 ∈ bad ((q, false) :: C)
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨hg, Finset.mem_sdiff.mpr
      ⟨hb, (Finset.mem_filter.mp hg).2.2⟩⟩
  · cases ha : oracleOf p.1 p.2 q
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      exact ⟨(mem_good_cons C q false p).mpr ⟨hg, ha, hb⟩,
        by simpa [BoolQueryTree.Run, ha] using hw⟩
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      exact ⟨(mem_good_cons C q true p).mpr ⟨hg, ha, hb⟩,
        by simpa [BoolQueryTree.Run, ha] using hw⟩

private def budgetWeight (k m : ℕ) : ℕ := m * (2 * k + m) + 1

private lemma budgetWeight_mono (k : ℕ) {m M : ℕ} (h : m ≤ M) :
    budgetWeight k m ≤ budgetWeight k M := by
  exact Nat.add_le_add_right (Nat.mul_le_mul h (by omega)) 1

private lemma subtree_bound {n t : ℕ} (ht : t ^ 2 < 2 ^ n)
    (tr : BoolQueryTree (Bool × Reg n) (Reg n)) :
    ∀ C : Transcript n, C.length + BoolQueryTree.MaxQueries tr ≤ t →
      (wins C tr).card * (2 ^ n - t ^ 2) ≤
        budgetWeight C.length (BoolQueryTree.MaxQueries tr) * (good C).card := by
  induction tr with
  | halt s =>
    intro C hbudget
    have h := good_count_le C {s} (by simpa [BoolQueryTree.MaxQueries] using hbudget) ht
    have hw : wins C (.halt s) = (good C).filter (fun p => p.2 ∈ ({s} : Finset _)) := by
      ext p
      simp [wins, BoolQueryTree.Run, eq_comm]
    simpa [hw, BoolQueryTree.MaxQueries, budgetWeight] using h
  | ask q trF trT ihF ihT =>
    intro C hbudget
    let M := max (BoolQueryTree.MaxQueries trF) (BoolQueryTree.MaxQueries trT)
    have hM : C.length + (1 + M) ≤ t := hbudget
    have hF : C.length + 1 + BoolQueryTree.MaxQueries trF ≤ t :=
      by have := Nat.le_max_left (BoolQueryTree.MaxQueries trF)
          (BoolQueryTree.MaxQueries trT); omega
    have hT : C.length + 1 + BoolQueryTree.MaxQueries trT ≤ t :=
      by have := Nat.le_max_right (BoolQueryTree.MaxQueries trF)
          (BoolQueryTree.MaxQueries trT); omega
    have hcF := ihF ((q, false) :: C) (by simpa using hF)
    have hcT := ihT ((q, true) :: C) (by simpa using hT)
    have hwF : budgetWeight (C.length + 1) (BoolQueryTree.MaxQueries trF) ≤
        budgetWeight (C.length + 1) M := budgetWeight_mono _ (Nat.le_max_left _ _)
    have hwT : budgetWeight (C.length + 1) (BoolQueryTree.MaxQueries trT) ≤
        budgetWeight (C.length + 1) M := budgetWeight_mono _ (Nat.le_max_right _ _)
    have hnew := good_count_le C (bad ((q, false) :: C) \ bad C) (by omega) ht
    have hn : ((good C).filter
        (fun p => p.2 ∈ bad ((q, false) :: C) \ bad C)).card * (2 ^ n - t ^ 2) ≤
        (2 * C.length + 1) * (good C).card :=
      hnew.trans (Nat.mul_le_mul_right _ ((new_bad_card_le C q).trans (by omega)))
    have hc := good_children_card C q
    calc
      (wins C (.ask q trF trT)).card * (2 ^ n - t ^ 2) ≤
          (((good C).filter (fun p => p.2 ∈ bad ((q, false) :: C) \ bad C)).card +
            (wins ((q, false) :: C) trF).card +
            (wins ((q, true) :: C) trT).card) * (2 ^ n - t ^ 2) :=
        Nat.mul_le_mul_right _ (wins_ask_card C q trF trT)
      _ ≤ (2 * C.length + 1) * (good C).card +
          budgetWeight (C.length + 1) M * (good ((q, false) :: C)).card +
          budgetWeight (C.length + 1) M * (good ((q, true) :: C)).card := by
        rw [Nat.add_mul, Nat.add_mul]
        exact Nat.add_le_add (Nat.add_le_add hn
          (hcF.trans (Nat.mul_le_mul_right _ hwF)))
          (hcT.trans (Nat.mul_le_mul_right _ hwT))
      _ = (2 * C.length + 1) * (good C).card +
          budgetWeight (C.length + 1) M *
            ((good ((q, false) :: C)).card + (good ((q, true) :: C)).card) := by ring
      _ ≤ (2 * C.length + 1) * (good C).card +
          budgetWeight (C.length + 1) M * (good C).card :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ hc) _
      _ = budgetWeight C.length (BoolQueryTree.MaxQueries (.ask q trF trT)) *
          (good C).card := by
        change _ = budgetWeight C.length (1 + M) * (good C).card
        simp only [budgetWeight]
        ring

private lemma deterministic_count_bound {n t : ℕ} (ht : t ^ 2 < 2 ^ n)
    (tr : BoolQueryTree (Bool × Reg n) (Reg n)) (htr : tr.MaxQueries ≤ t) :
    (Finset.univ.filter (fun p : (Reg n → Bool) × Reg n =>
      (BoolQueryTree.Run (oracleOf p.1 p.2) tr).1 = p.2)).card * (2 ^ n - t ^ 2) ≤
        (t ^ 2 + 1) * (Fintype.card (Reg n → Bool) * Fintype.card (Reg n)) := by
  have h := subtree_bound ht tr [] (by simpa using htr)
  have hw := budgetWeight_mono 0 htr
  have hg : good ([] : Transcript n) = Finset.univ := by
    ext p
    simp [good, consistent, bad, points]
  simp only [List.length_nil, wins, hg, Finset.card_univ, Fintype.card_prod] at h
  apply h.trans
  apply Nat.mul_le_mul_right
  simpa [budgetWeight, pow_two] using hw

private lemma randomized_count_bound {n t : ℕ}
    (prog : PMF (BoolQueryTree (Bool × Reg n) (Reg n)))
    (hbound : BoolQueryTree.BoundedQueries prog t)
    (B : ℝ) (hB : 0 ≤ B)
    (hdet : ∀ tree, BoolQueryTree.MaxQueries tree ≤ t →
      ((Finset.univ.filter
        (fun p : (Reg n → Bool) × Reg n =>
          (BoolQueryTree.Run (oracleOf p.1 p.2) tree).1 = p.2)).card : ℝ) ≤ B) :
    (∑ f : Reg n → Bool, ∑ s : Reg n,
      (BoolQueryTree.SuccessProb prog (oracleOf f s)
        (fun out => out = s)).toReal) ≤ B := by
  have hfinite (f : Reg n → Bool) (s : Reg n) :
      BoolQueryTree.SuccessProb prog (oracleOf f s)
        (fun out => out = s) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    calc
      _ ≤ ∑' tree, prog tree := by
        unfold BoolQueryTree.SuccessProb
        apply ENNReal.tsum_le_tsum
        intro tree
        split <;> simp
      _ = 1 := prog.tsum_coe
  have htotal :
      (∑ f : Reg n → Bool, ∑ s : Reg n,
        BoolQueryTree.SuccessProb prog (oracleOf f s)
          (fun out => out = s)) ≤ ENNReal.ofReal B := by
    calc
      _ = ∑ p : (Reg n → Bool) × Reg n,
          ∑' tree, prog tree *
            if (BoolQueryTree.Run (oracleOf p.1 p.2) tree).1 = p.2
              then 1 else 0 := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro f _
        apply Finset.sum_congr rfl
        intro s _
        unfold BoolQueryTree.SuccessProb
        apply tsum_congr
        intro tree
        by_cases hw : (BoolQueryTree.Run (oracleOf f s) tree).1 = s <;> simp [hw]
      _ = ∑' tree, ∑ p : (Reg n → Bool) × Reg n,
          prog tree *
            if (BoolQueryTree.Run (oracleOf p.1 p.2) tree).1 = p.2
              then 1 else 0 := by
        calc
          _ = ∑' p : (Reg n → Bool) × Reg n, ∑' tree, prog tree *
              if (BoolQueryTree.Run (oracleOf p.1 p.2) tree).1 = p.2
                then 1 else 0 := (tsum_fintype _).symm
          _ = ∑' tree, ∑' p : (Reg n → Bool) × Reg n, prog tree *
              if (BoolQueryTree.Run (oracleOf p.1 p.2) tree).1 = p.2
                then 1 else 0 := ENNReal.tsum_comm
          _ = _ := by simp only [tsum_fintype]
      _ = ∑' tree, prog tree *
          ((Finset.univ.filter
            (fun p : (Reg n → Bool) × Reg n =>
              (BoolQueryTree.Run (oracleOf p.1 p.2) tree).1 = p.2)).card :
            ℝ≥0∞) := by
        apply tsum_congr
        intro tree
        rw [← Finset.mul_sum, Finset.sum_boole]
      _ ≤ ∑' tree, prog tree * ENNReal.ofReal B := by
        apply ENNReal.tsum_le_tsum
        intro tree
        by_cases htree : prog tree = 0
        · simp [htree]
        · apply mul_le_mul_right
          simpa only [ENNReal.ofReal_natCast] using
            ENNReal.ofReal_le_ofReal (hdet tree (hbound tree htree))
      _ = ENNReal.ofReal B := by
        rw [ENNReal.tsum_mul_right, prog.tsum_coe, one_mul]
  have htoReal :
      (∑ f : Reg n → Bool, ∑ s : Reg n,
        BoolQueryTree.SuccessProb prog (oracleOf f s)
          (fun out => out = s)).toReal =
      ∑ f : Reg n → Bool, ∑ s : Reg n,
        (BoolQueryTree.SuccessProb prog (oracleOf f s)
          (fun out => out = s)).toReal := by
    rw [ENNReal.toReal_sum (fun f _ =>
      ENNReal.sum_ne_top.mpr (fun s _ => hfinite f s))]
    apply Finset.sum_congr rfl
    intro f _
    exact ENNReal.toReal_sum (fun s _ => hfinite f s)
  simpa only [htoReal, ENNReal.toReal_ofReal hB] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top htotal

/-- **Lemma 2**: any `t`-query bounded randomized classical decision-tree program
whose average success probability on a uniformly random BHSP instance is at least
`1 / 2` satisfies `2 ^ n ≤ 3 * t ^ 2 + 2`. -/
theorem source_lemma2_classical_lower_bound {n t : ℕ}
    (prog : PMF (BoolQueryTree (Bool × Reg n) (Reg n)))
    (hbound : BoolQueryTree.BoundedQueries prog t)
    (hsucc : (1 / 2 : ℝ) ≤ avgSuccess prog) :
    (2 : ℝ) ^ n ≤ 3 * (t : ℝ) ^ 2 + 2 := by
  by_cases hlarge : (2 : ℝ) ^ n ≤ (t : ℝ) ^ 2
  · nlinarith [sq_nonneg (t : ℝ)]
  have hden : (t : ℝ) ^ 2 < (2 : ℝ) ^ n := lt_of_not_ge hlarge
  have ht : t ^ 2 < 2 ^ n := by exact_mod_cast hden
  have hcast : ((2 ^ n - t ^ 2 : ℕ) : ℝ) = (2 : ℝ) ^ n - (t : ℝ) ^ 2 := by
    rw [Nat.cast_sub (Nat.le_of_lt ht)]
    norm_cast
  let B : ℝ := ((t : ℝ) ^ 2 + 1) / ((2 : ℝ) ^ n - (t : ℝ) ^ 2)
  have hB : 0 ≤ B := div_nonneg (by positivity) (sub_pos.mpr hden).le
  have hcard : (0 : ℝ) <
      (Fintype.card (Reg n → Bool) : ℝ) * (Fintype.card (Reg n) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Fintype.card_pos) (Fintype.card_pos)
  apply classical_success_forces_queries hden
  apply hsucc.trans
  apply (div_le_iff₀ hcard).mpr
  apply randomized_count_bound prog hbound
    (B * ((Fintype.card (Reg n → Bool) : ℝ) * (Fintype.card (Reg n) : ℝ)))
    (mul_nonneg hB hcard.le)
  intro tree htree
  have hnat := deterministic_count_bound ht tree htree
  have hr : ((Finset.univ.filter (fun p : (Reg n → Bool) × Reg n =>
      (BoolQueryTree.Run (oracleOf p.1 p.2) tree).1 = p.2)).card : ℝ) *
        ((2 ^ n - t ^ 2 : ℕ) : ℝ) ≤
      ((t : ℝ) ^ 2 + 1) *
        ((Fintype.card (Reg n → Bool) : ℝ) * (Fintype.card (Reg n) : ℝ)) := by
    exact_mod_cast hnat
  rw [hcast] at hr
  dsimp [B]
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (sub_pos.mpr hden)).mpr hr


end Qatlib.Papers.BoolHidShift11.RandomFunctions.ClassicalLowerBound
