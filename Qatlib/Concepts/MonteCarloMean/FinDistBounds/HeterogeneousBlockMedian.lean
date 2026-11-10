/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.IndependentWeightedEstimator

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Matrix
open scoped Classical BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

def blockRecordLaw {X : Type} [Fintype X] [DecidableEq X] (r B : ℕ)
    (p : Fin (2*r+1) → Fin B → FinDist X) : FinDist (Fin (2*r+1) → Fin B → X) where
  prob ω := ∏ j, ∏ b, (p j b).prob (ω j b)
  nonneg ω := Finset.prod_nonneg fun j _ => Finset.prod_nonneg fun b _ => (p j b).nonneg _
  sum_one := by
    exact (independentSampleLaw (fun j => independentSampleLaw (p j))).sum_one

def weightedBlock {X : Type} [Fintype X] [DecidableEq X] (r B : ℕ)
    (w : Fin (2*r+1) → Fin B → ℝ) (f : Fin (2*r+1) → Fin B → X → ℝ)
    (ω : Fin (2*r+1) → Fin B → X) : Fin (2*r+1) → ℝ :=
  fun j => ∑ b, w j b * f j b (ω j b)

theorem heterogeneous_blocks_actual_product_and_estimator {X : Type} [Fintype X] [DecidableEq X]
    (r B : ℕ) (p : Fin (2*r+1) → Fin B → FinDist X)
    (w : Fin (2*r+1) → Fin B → ℝ) (f : Fin (2*r+1) → Fin B → X → ℝ)
    (ω : Fin (2*r+1) → Fin B → X) :
    (blockRecordLaw r B p).prob ω = ∏ j, ∏ b, (p j b).prob (ω j b) ∧
      ∀ j, weightedBlock r B w f ω j = ∑ b, w j b * f j b (ω j b) :=
  ⟨rfl, fun _ => rfl⟩

theorem blockRecordLaw_expect_prod {X : Type} [Fintype X] [DecidableEq X] (r B : ℕ)
    (p : Fin (2*r+1) → Fin B → FinDist X) (g : Fin (2*r+1) → (Fin B → X) → ℝ) :
    (blockRecordLaw r B p).expect (fun ω => ∏ j, g j (ω j))
      = ∏ j, (∑ u : Fin B → X, (∏ b, (p j b).prob (u b)) * g j u) := by
  exact independentSampleLaw_expect_prod (fun j => independentSampleLaw (p j)) g

theorem blockRecordLaw_expect_prod_mem {X : Type} [Fintype X] [DecidableEq X] (r B : ℕ)
    (p : Fin (2*r+1) → Fin B → FinDist X) (J : Finset (Fin (2*r+1)))
    (g : Fin (2*r+1) → (Fin B → X) → ℝ) :
    (blockRecordLaw r B p).expect (fun ω => ∏ j ∈ J, g j (ω j))
      = ∏ j ∈ J, (∑ u : Fin B → X, (∏ b, (p j b).prob (u b)) * g j u) := by
  have hfull := blockRecordLaw_expect_prod r B p (fun j u => if j ∈ J then g j u else 1)
  have hfun : (fun ω : Fin (2*r+1) → Fin B → X => ∏ j ∈ J, g j (ω j))
      = fun ω => ∏ j, (if j ∈ J then g j (ω j) else 1) := by
    funext ω
    have e1 : ∏ j ∈ J, (if j ∈ J then g j (ω j) else 1)
        = ∏ j, (if j ∈ J then g j (ω j) else 1) :=
      Finset.prod_subset (Finset.subset_univ J) (fun j _ hj => if_neg hj)
    have e2 : (∏ j ∈ J, g j (ω j))
        = ∏ j ∈ J, (if j ∈ J then g j (ω j) else 1) :=
      Finset.prod_congr rfl fun j hj => (if_pos hj).symm
    rw [← e1, e2]
  rw [hfun, hfull]
  have hb : ∏ j ∈ J, (∑ u : Fin B → X, (∏ b, (p j b).prob (u b)) * (if j ∈ J then g j u else 1))
      = ∏ j, (∑ u : Fin B → X, (∏ b, (p j b).prob (u b)) * (if j ∈ J then g j u else 1)) :=
    Finset.prod_subset (Finset.subset_univ J) (fun j _ hj => by
      rw [Finset.sum_congr rfl fun u (_ : u ∈ Finset.univ) => by rw [if_neg hj, mul_one]]
      exact (independentSampleLaw (p j)).sum_one)
  have ha : ∏ j ∈ J, (∑ u : Fin B → X, (∏ b, (p j b).prob (u b)) * (if j ∈ J then g j u else 1))
      = ∏ j ∈ J, (∑ u : Fin B → X, (∏ b, (p j b).prob (u b)) * g j u) :=
    Finset.prod_congr rfl fun j hj => Finset.sum_congr rfl fun u _ => by rw [if_pos hj]
  exact hb.symm.trans ha

theorem blockRecordLaw_marginal {X : Type} [Fintype X] [DecidableEq X] (r B : ℕ)
    (p : Fin (2*r+1) → Fin B → FinDist X) (j : Fin (2*r+1)) (h : (Fin B → X) → ℝ) :
    (blockRecordLaw r B p).expect (fun ω => h (ω j)) = (independentSampleLaw (p j)).expect h := by
  exact independentSampleLaw_expect_coord (fun k => independentSampleLaw (p k)) j h

theorem expect_indicator_eq_filter_sum {Ω : Type} [Fintype Ω] (q : FinDist Ω) (P : Ω → Prop)
    [DecidablePred P] :
    q.expect (fun ω => if P ω then (1:ℝ) else 0) = ∑ ω ∈ Finset.univ.filter P, q.prob ω := by
  show ∑ ω, q.prob ω * (if P ω then (1:ℝ) else 0) = _
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun ω _ => by
    by_cases hP : P ω <;> simp [hP]

theorem heterogeneous_block_exact_centered_moment {X : Type} [Fintype X] [DecidableEq X]
    (r B : ℕ) (p : Fin (2*r+1) → Fin B → FinDist X) (w : Fin (2*r+1) → Fin B → ℝ)
    (f : Fin (2*r+1) → Fin B → X → ℝ) (j : Fin (2*r+1)) :
    let μ := ∑ b, w j b * (p j b).expect (f j b)
    (blockRecordLaw r B p).expect (fun ω => weightedBlock r B w f ω j) = μ ∧
      (blockRecordLaw r B p).expect (fun ω => (weightedBlock r B w f ω j - μ)^2) =
        ∑ b, (w j b)^2 * (p j b).expect (fun x => (f j b x-(p j b).expect (f j b))^2) := by
  show (blockRecordLaw r B p).expect (fun ω => weightedBlock r B w f ω j) =
      ∑ b, w j b * (p j b).expect (f j b) ∧
    (blockRecordLaw r B p).expect
        (fun ω => (weightedBlock r B w f ω j - ∑ b, w j b * (p j b).expect (f j b))^2) =
      ∑ b, (w j b)^2 * (p j b).expect (fun x => (f j b x-(p j b).expect (f j b))^2)
  refine ⟨?_, ?_⟩
  · calc (blockRecordLaw r B p).expect (fun ω => weightedBlock r B w f ω j)
        = (blockRecordLaw r B p).expect (fun ω => weightedSampleSum (w j) (f j) (ω j)) := rfl
      _ = (independentSampleLaw (p j)).expect (weightedSampleSum (w j) (f j)) :=
          blockRecordLaw_marginal r B p j _
      _ = ∑ b, w j b * (p j b).expect (f j b) := independent_weighted_expectation _ _ _
  · calc (blockRecordLaw r B p).expect
          (fun ω => (weightedBlock r B w f ω j - ∑ b, w j b * (p j b).expect (f j b))^2)
        = (blockRecordLaw r B p).expect
            (fun ω => (weightedSampleSum (w j) (f j) (ω j)
              - ∑ b, w j b * (p j b).expect (f j b))^2) := rfl
      _ = (independentSampleLaw (p j)).expect
            (fun u => (weightedSampleSum (w j) (f j) u
              - ∑ b, w j b * (p j b).expect (f j b))^2) :=
          blockRecordLaw_marginal r B p j
            (fun u => (weightedSampleSum (w j) (f j) u
              - ∑ b, w j b * (p j b).expect (f j b))^2)
      _ = (independentSampleLaw (p j)).variance (weightedSampleSum (w j) (f j)) := by
          have hdef : (independentSampleLaw (p j)).variance (weightedSampleSum (w j) (f j))
              = (independentSampleLaw (p j)).expect
                (fun u => (weightedSampleSum (w j) (f j) u -
                  (independentSampleLaw (p j)).expect (weightedSampleSum (w j) (f j)))^2) :=
            rfl
          rw [hdef, independent_weighted_expectation]
      _ = ∑ b, (w j b)^2 * (p j b).expect (fun x => (f j b x-(p j b).expect (f j b))^2) :=
          independent_weighted_variance _ _ _

theorem heterogeneous_block_bad_subset_product {X : Type} [Fintype X] [DecidableEq X]
    (r B : ℕ) (p : Fin (2*r+1) → Fin B → FinDist X) (w : Fin (2*r+1) → Fin B → ℝ)
    (f : Fin (2*r+1) → Fin B → X → ℝ) (θ ε : ℝ) (J : Finset (Fin (2*r+1))) :
    (∑ ω ∈ Finset.univ.filter (fun ω => ∀ j ∈ J, ε < |weightedBlock r B w f ω j-θ|),
        (blockRecordLaw r B p).prob ω) =
      ∏ j ∈ J, (∑ ω ∈ Finset.univ.filter (fun ω => ε < |weightedBlock r B w f ω j-θ|),
        (blockRecordLaw r B p).prob ω) := by
  have hprod := blockRecordLaw_expect_prod_mem r B p J
    (fun j u => if ε < |∑ b, w j b * f j b (u b) - θ| then (1:ℝ) else 0)
  have hL : (∑ ω ∈ Finset.univ.filter (fun ω => ∀ j ∈ J, ε < |weightedBlock r B w f ω j-θ|),
        (blockRecordLaw r B p).prob ω)
      = (blockRecordLaw r B p).expect
          (fun ω => ∏ j ∈ J, (if ε < |∑ b, w j b * f j b (ω j b) - θ| then (1:ℝ) else 0)) := by
    rw [← expect_indicator_eq_filter_sum (blockRecordLaw r B p)
      (fun ω => ∀ j ∈ J, ε < |weightedBlock r B w f ω j - θ|)]
    refine congrArg _ (funext fun ω => ?_)
    show (if ∀ j ∈ J, ε < |weightedBlock r B w f ω j - θ| then (1:ℝ) else 0)
      = ∏ j ∈ J, (if ε < |∑ b, w j b * f j b (ω j b) - θ| then (1:ℝ) else 0)
    by_cases hall : ∀ j ∈ J, ε < |weightedBlock r B w f ω j - θ|
    · have hprod1 : (∏ j' ∈ J,
          (if ε < |∑ b, w j' b * f j' b (ω j' b) - θ| then (1:ℝ) else 0)) = 1 :=
        Finset.prod_eq_one (fun j hj => if_pos (hall j hj))
      rw [if_pos hall, hprod1]
    · push Not at hall
      obtain ⟨j, hjJ, hjbad⟩ := hall
      rw [if_neg (fun hall => not_lt.mpr hjbad (hall j hjJ)),
        Finset.prod_eq_zero hjJ (if_neg (by
          show ¬ (ε < |∑ b, w j b * f j b (ω j b) - θ|)
          exact not_lt.mpr hjbad))]
  have hR : ∀ j : Fin (2*r+1),
      (∑ ω ∈ Finset.univ.filter (fun ω => ε < |weightedBlock r B w f ω j-θ|),
        (blockRecordLaw r B p).prob ω)
        = ∑ u : Fin B → X, (∏ b, (p j b).prob (u b)) *
            (if ε < |∑ b, w j b * f j b (u b) - θ| then (1:ℝ) else 0) := by
    intro j
    calc (∑ ω ∈ Finset.univ.filter (fun ω => ε < |weightedBlock r B w f ω j-θ|),
          (blockRecordLaw r B p).prob ω)
        = (blockRecordLaw r B p).expect
            (fun ω => if ε < |weightedBlock r B w f ω j - θ| then (1:ℝ) else 0) :=
          (expect_indicator_eq_filter_sum _ _).symm
      _ = (independentSampleLaw (p j)).expect
            (fun u => if ε < |∑ b, w j b * f j b (u b) - θ| then (1:ℝ) else 0) :=
          blockRecordLaw_marginal r B p j
            (fun u => if ε < |∑ b, w j b * f j b (u b) - θ| then (1:ℝ) else 0)
      _ = ∑ u : Fin B → X, (∏ b, (p j b).prob (u b)) *
            (if ε < |∑ b, w j b * f j b (u b) - θ| then (1:ℝ) else 0) := rfl
  calc (∑ ω ∈ Finset.univ.filter (fun ω => ∀ j ∈ J, ε < |weightedBlock r B w f ω j-θ|),
        (blockRecordLaw r B p).prob ω)
      = (blockRecordLaw r B p).expect
          (fun ω => ∏ j ∈ J, (if ε < |∑ b, w j b * f j b (ω j b) - θ| then (1:ℝ) else 0)) := hL
    _ = ∏ j ∈ J, (∑ u : Fin B → X, (∏ b, (p j b).prob (u b)) *
          (if ε < |∑ b, w j b * f j b (u b) - θ| then (1:ℝ) else 0)) := hprod
    _ = ∏ j ∈ J, (∑ ω ∈ Finset.univ.filter (fun ω => ε < |weightedBlock r B w f ω j-θ|),
          (blockRecordLaw r B p).prob ω) := Finset.prod_congr rfl fun j _ => (hR j).symm

noncomputable def insertSortedCounted (x : ℝ) : List ℝ → List ℝ × ℕ
  | [] => ([x], 0)
  | y :: ys =>
      if x ≤ y then (x :: y :: ys, 1)
      else let s := insertSortedCounted x ys; (y :: s.1, s.2 + 1)

noncomputable def insertionSortCounted : List ℝ → List ℝ × ℕ
  | [] => ([], 0)
  | x :: xs =>
      let s := insertionSortCounted xs
      let t := insertSortedCounted x s.1
      (t.1, s.2 + t.2)

theorem insertSortedCounted_length (x : ℝ) (l : List ℝ) :
    (insertSortedCounted x l).1.length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
      simp only [insertSortedCounted]
      split
      · rfl
      · show ((insertSortedCounted x ys).1).length + 1 = (y :: ys).length + 1
        rw [ih]
        simp

theorem insertSortedCounted_cost_le (x : ℝ) (l : List ℝ) :
    (insertSortedCounted x l).2 ≤ l.length := by
  induction l with
  | nil => simp [insertSortedCounted]
  | cons y ys ih =>
      simp only [insertSortedCounted]
      split
      · simp
      · show (insertSortedCounted x ys).2 + 1 ≤ (y :: ys).length
        have hlen : (y :: ys).length = ys.length + 1 := rfl
        omega

theorem insertSortedCounted_perm (x : ℝ) (l : List ℝ) :
    (insertSortedCounted x l).1.Perm (x :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
      simp only [insertSortedCounted]
      split
      · exact List.Perm.refl _
      · exact List.Perm.trans (List.Perm.cons y ih) (List.Perm.swap x y ys)

theorem insertSortedCounted_sorted {x : ℝ} {l : List ℝ} (hl : l.SortedLE) :
    (insertSortedCounted x l).1.SortedLE := by
  induction l with
  | nil =>
      exact List.sortedLE_iff_pairwise.mpr
        (List.Pairwise.cons (fun b hb => absurd hb (List.not_mem_nil (a := b))) List.Pairwise.nil)
  | cons y ys ih =>
      simp only [insertSortedCounted]
      rw [List.sortedLE_iff_pairwise] at hl ⊢
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hl
      split
      · next hxy =>
          refine List.Pairwise.cons (fun b hb => ?_) hl
          rcases List.mem_cons.mp hb with rfl | hbys
          · exact hxy
          · exact le_trans hxy (hhead b hbys)
      · next hnxy =>
          have hyx : y ≤ x := le_of_lt (lt_of_not_ge hnxy)
          refine List.Pairwise.cons (fun b hb => ?_)
            (List.sortedLE_iff_pairwise.mp (ih (List.sortedLE_iff_pairwise.mpr htail)))
          have hmem : b ∈ x :: ys := List.Perm.subset (insertSortedCounted_perm x ys) hb
          rcases List.mem_cons.mp hmem with rfl | hbys
          · exact hyx
          · exact hhead b hbys

theorem insertionSortCounted_length (l : List ℝ) :
    (insertionSortCounted l).1.length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      show ((insertSortedCounted x (insertionSortCounted xs).1).1).length = (x :: xs).length
      rw [insertSortedCounted_length, ih]
      simp

theorem insertionSortCounted_perm (l : List ℝ) : (insertionSortCounted l).1.Perm l := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
      show ((insertSortedCounted x (insertionSortCounted xs).1).1).Perm (x :: xs)
      exact List.Perm.trans (insertSortedCounted_perm x _) (List.Perm.cons x ih)

theorem insertionSortCounted_cost_le (l : List ℝ) :
    (insertionSortCounted l).2 ≤ l.length * l.length := by
  induction l with
  | nil => simp [insertionSortCounted]
  | cons x xs ih =>
      show (insertionSortCounted xs).2 + (insertSortedCounted x (insertionSortCounted xs).1).2
        ≤ (x :: xs).length * (x :: xs).length
      have h1 := insertSortedCounted_cost_le x (insertionSortCounted xs).1
      have h2 := insertionSortCounted_length xs
      have h3 : (x :: xs).length = xs.length + 1 := rfl
      have h4 : xs.length * xs.length + xs.length
          ≤ (x :: xs).length * (x :: xs).length := by
        rw [h3, Nat.succ_mul_succ]
        omega
      omega

theorem insertionSortCounted_sorted (l : List ℝ) : (insertionSortCounted l).1.SortedLE := by
  induction l with
  | nil => exact List.sortedLE_iff_pairwise.mpr List.Pairwise.nil
  | cons x xs ih =>
      show ((insertSortedCounted x (insertionSortCounted xs).1).1).SortedLE
      exact insertSortedCounted_sorted ih

noncomputable def sortedBlockMedian (r : ℕ) (v : Fin (2*r+1) → ℝ) : ℝ :=
  (insertionSortCounted (List.ofFn v)).1.getD r 0

theorem heterogeneous_sorted_median_majority_witness (r : ℕ) (v : Fin (2*r+1) → ℝ) (θ ε : ℝ)
    (hε : 0 ≤ ε) (hmed : ε < |sortedBlockMedian r v - θ|) :
    r+1 ≤ (Finset.univ.filter (fun j => ε < |v j - θ|)).card := by
  have hlen : ((insertionSortCounted (List.ofFn v)).1).length = 2*r+1 := by
    rw [insertionSortCounted_length, List.length_ofFn]
  have hsorted := insertionSortCounted_sorted (List.ofFn v)
  have hperm := insertionSortCounted_perm (List.ofFn v)
  have hdiv : (2*r+1)/2 = r := by omega
  have hmed' : ε < |((insertionSortCounted (List.ofFn v)).1).getD ((2*r+1)/2) 0 - θ| := by
    rw [hdiv]
    exact hmed
  have hkey :=
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.sorted_countP_ge_of_median_dev
      (M := 2*r+1) hsorted hlen (by omega) hmed'
  rw [hdiv] at hkey
  have hcp : ((insertionSortCounted (List.ofFn v)).1).countP (fun x => decide (ε < |x - θ|))
      = (List.ofFn v).countP (fun x => decide (ε < |x - θ|)) :=
    List.Perm.countP_eq _ hperm
  have hfin : (List.ofFn v).countP (fun x => decide (ε < |x - θ|))
      = (Finset.univ.filter (fun j => ε < |v j - θ|)).card :=
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.countP_ofFn_eq_card_filter v (fun x => ε < |x - θ|)
  omega

noncomputable def countedBlockMedian {X : Type} [Fintype X] [DecidableEq X] (r B : ℕ)
    (w : Fin (2*r+1) → Fin B → ℝ) (f : Fin (2*r+1) → Fin B → X → ℝ)
    (ω : Fin (2*r+1) → Fin B → X) : ℝ × ℕ × ℕ :=
  let l : List ℝ := List.ofFn (weightedBlock r B w f ω)
  let s := insertionSortCounted l
  (s.1.getD r 0, l.length * B, s.2)

theorem heterogeneous_counted_estimator_reads_and_comparisons {X : Type} [Fintype X]
    [DecidableEq X] (r B : ℕ) (w : Fin (2*r+1) → Fin B → ℝ) (f : Fin (2*r+1) → Fin B → X → ℝ)
    (ω : Fin (2*r+1) → Fin B → X) :
    (countedBlockMedian r B w f ω).1 = sortedBlockMedian r (weightedBlock r B w f ω) ∧
      (countedBlockMedian r B w f ω).2.1 = (2*r+1)*B ∧
      (countedBlockMedian r B w f ω).2.2 ≤ (2*r+1)*(2*r+1) := by
  refine ⟨rfl, ?_, ?_⟩
  · show (List.ofFn (weightedBlock r B w f ω)).length * B = (2*r+1)*B
    rw [List.length_ofFn]
  · show (insertionSortCounted (List.ofFn (weightedBlock r B w f ω))).2 ≤ (2*r+1)*(2*r+1)
    have h1 := insertionSortCounted_cost_le (List.ofFn (weightedBlock r B w f ω))
    rw [List.length_ofFn] at h1
    exact h1

theorem pow_le_one_of_mem_Icc {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : ∀ d : ℕ, a ^ d ≤ 1 := by
  intro d
  induction d with
  | zero => norm_num
  | succ d ih =>
      rw [pow_succ]
      exact le_trans (mul_le_of_le_one_right (pow_nonneg ha0 _) ha1) ih

theorem fintype_union_bound_mass {ι Ω : Type} [Fintype ι] [Fintype Ω] (mass : Ω → ℝ)
    (hnn : ∀ ω, 0 ≤ mass ω) (A : ι → Ω → Prop) [∀ i, DecidablePred (A i)]
    [DecidablePred fun ω => ∃ i, A i ω] :
    ∑ ω ∈ Finset.univ.filter (fun ω => ∃ i, A i ω), mass ω
      ≤ ∑ i, ∑ ω ∈ Finset.univ.filter (A i), mass ω := by
  have hpt : ∀ ω : Ω, (∃ i, A i ω) →
      mass ω ≤ ∑ i, mass ω * (if A i ω then (1:ℝ) else 0) := by
    intro ω ⟨i₀, hA⟩
    have h1 : (1:ℝ) ≤ (if A i₀ ω then 1 else 0) := by rw [if_pos hA]
    have h2 : mass ω * (if A i₀ ω then (1:ℝ) else 0)
        ≤ ∑ i, mass ω * (if A i ω then (1:ℝ) else 0) :=
      Finset.single_le_sum (f := fun i => mass ω * (if A i ω then (1:ℝ) else 0))
        (fun i _ => mul_nonneg (hnn ω) (by split_ifs <;> norm_num)) (Finset.mem_univ i₀)
    calc mass ω = mass ω * 1 := by ring
      _ ≤ mass ω * (if A i₀ ω then (1:ℝ) else 0) := mul_le_mul_of_nonneg_left h1 (hnn ω)
      _ ≤ ∑ i, mass ω * (if A i ω then (1:ℝ) else 0) := h2
  calc ∑ ω ∈ Finset.univ.filter (fun ω => ∃ i, A i ω), mass ω
      ≤ ∑ ω ∈ Finset.univ.filter (fun ω => ∃ i, A i ω),
          ∑ i, mass ω * (if A i ω then (1:ℝ) else 0) :=
        Finset.sum_le_sum fun ω hω => hpt ω ((Finset.mem_filter.mp hω).2)
    _ ≤ ∑ ω ∈ Finset.univ, ∑ i, mass ω * (if A i ω then (1:ℝ) else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun ω _ _ => Finset.sum_nonneg fun i _ =>
            mul_nonneg (hnn ω) (by split_ifs <;> norm_num))
    _ = ∑ i, ∑ ω ∈ Finset.univ, mass ω * (if A i ω then (1:ℝ) else 0) := Finset.sum_comm
    _ = ∑ i, ∑ ω ∈ Finset.univ.filter (A i), mass ω := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun ω _ => by
          by_cases hA : A i ω <;> simp [hA]

theorem heterogeneous_weighted_median_concentration {X : Type} [Fintype X] [DecidableEq X]
    (r B : ℕ) (p : Fin (2*r+1) → Fin B → FinDist X) (w : Fin (2*r+1) → Fin B → ℝ)
    (f : Fin (2*r+1) → Fin B → X → ℝ) (θ ε : ℝ) (hε : 0 < ε)
    (hmean : ∀ j, ∑ b, w j b * (p j b).expect (f j b) = θ)
    (hvar : ∀ j, ∑ b, (w j b)^2 * (p j b).expect (fun x => (f j b x-(p j b).expect (f j b))^2)
      ≤ ε^2/16) :
    (∑ ω ∈ Finset.univ.filter (fun ω => ε < |sortedBlockMedian r (weightedBlock r B w f ω)-θ|),
      (blockRecordLaw r B p).prob ω) ≤ (2:ℝ)^(2*r+1) * (1/16:ℝ)^(r+1) := by
  classical

  have hcheb : ∀ j : Fin (2*r+1),
      (∑ ω ∈ Finset.univ.filter (fun ω => ε < |weightedBlock r B w f ω j - θ|),
        (blockRecordLaw r B p).prob ω) ≤ (1/16:ℝ) := by
    intro j
    have hmarg := blockRecordLaw_marginal r B p j
      (fun u => if ε < |∑ b, w j b * f j b (u b) - θ| then (1:ℝ) else 0)
    have hchebmain := independent_weighted_chebyshev (p j) (w j) (f j) ε hε
    rw [Finset.filter_congr (fun u (_ : u ∈ Finset.univ) => by rw [hmean j])] at hchebmain
    calc (∑ ω ∈ Finset.univ.filter (fun ω => ε < |weightedBlock r B w f ω j - θ|),
          (blockRecordLaw r B p).prob ω)
        = (blockRecordLaw r B p).expect
            (fun ω => if ε < |weightedBlock r B w f ω j - θ| then (1:ℝ) else 0) :=
          (expect_indicator_eq_filter_sum _ _).symm
      _ = (independentSampleLaw (p j)).expect
            (fun u => if ε < |∑ b, w j b * f j b (u b) - θ| then (1:ℝ) else 0) := hmarg
      _ = ∑ u ∈ Finset.univ.filter
            (fun u : Fin B → X => ε < |weightedSampleSum (w j) (f j) u - θ|),
            (independentSampleLaw (p j)).prob u :=
          expect_indicator_eq_filter_sum _ _
      _ ≤ (∑ b, (w j b)^2 * (p j b).variance (f j b)) / ε^2 := hchebmain
      _ ≤ (ε^2/16) / ε^2 := div_le_div_of_nonneg_right (hvar j) (sq_nonneg ε)
      _ = 1/16 := by
          have hε2 : (ε:ℝ)^2 ≠ 0 := pow_ne_zero 2 hε.ne'
          field_simp

  set fam : Finset (Finset (Fin (2*r+1))) := Finset.univ.filter (fun J => r+1 ≤ J.card) with hfam
  have hfamcard : ∀ J ∈ fam, r+1 ≤ J.card := by
    intro J hJ
    rw [hfam] at hJ
    exact (Finset.mem_filter.mp hJ).2
  have hsub : (Finset.univ.filter (fun ω => ε < |sortedBlockMedian r (weightedBlock r B w f ω)-θ|))
      ⊆ Finset.univ.filter (fun ω => ∃ J : Finset (Fin (2*r+1)),
          J ∈ fam ∧ ∀ j ∈ J, ε < |weightedBlock r B w f ω j - θ|) := by
    intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    refine ⟨Finset.mem_univ ω, ?_⟩
    have hG4 := heterogeneous_sorted_median_majority_witness r (weightedBlock r B w f ω) θ ε
      (le_of_lt hε) hω.2
    refine ⟨Finset.univ.filter (fun j => ε < |weightedBlock r B w f ω j - θ|),
      by rw [hfam]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hG4⟩,
      fun j hj => (Finset.mem_filter.mp hj).2⟩
  have hub := fintype_union_bound_mass ((blockRecordLaw r B p).prob)
    (fun ω => (blockRecordLaw r B p).nonneg ω)
    (A := fun (J : Finset (Fin (2*r+1))) ω =>
      J ∈ fam ∧ ∀ j ∈ J, ε < |weightedBlock r B w f ω j - θ|)
  have hdrop : (∑ J : Finset (Fin (2*r+1)), ∑ ω ∈ Finset.univ.filter
          (fun ω => J ∈ fam ∧ ∀ j ∈ J, ε < |weightedBlock r B w f ω j - θ|),
          (blockRecordLaw r B p).prob ω)
      = ∑ J ∈ fam, ∑ ω ∈ Finset.univ.filter (fun ω => ∀ j ∈ J, ε < |weightedBlock r B w f ω j - θ|),
          (blockRecordLaw r B p).prob ω := by
    rw [← Finset.sum_subset (Finset.subset_univ fam) (fun J _ hJ =>
      Finset.sum_eq_zero fun ω hω => absurd ((Finset.mem_filter.mp hω).2).1 hJ)]
    exact Finset.sum_congr rfl fun J hJ => Finset.sum_congr
      (Finset.filter_congr fun ω _ => ⟨fun h => h.2, fun h => ⟨hJ, h⟩⟩) fun _ _ => rfl
  have hperJ : ∀ J ∈ fam,
      (∏ j ∈ J, (∑ ω ∈ Finset.univ.filter (fun ω => ε < |weightedBlock r B w f ω j - θ|),
        (blockRecordLaw r B p).prob ω)) ≤ (1/16:ℝ)^(r+1) := by
    intro J hJ
    refine le_trans (le_trans
      (Finset.prod_le_prod₀ (fun j _ => Finset.sum_nonneg fun _ _ => (blockRecordLaw r B p).nonneg _)
        (fun j _ => hcheb j)) (le_of_eq (Finset.prod_const (1/16:ℝ)))) ?_
    rw [← Nat.sub_add_cancel (hfamcard J hJ), pow_add]
    exact mul_le_of_le_one_left (pow_nonneg (show (0:ℝ) ≤ 1/16 by norm_num) _)
      (pow_le_one_of_mem_Icc (show (0:ℝ) ≤ 1/16 by norm_num)
        (show (1/16:ℝ) ≤ 1 by norm_num) _)
  have hcards : fam.card ≤ 2^(2*r+1) := by
    rw [hfam]
    have h1 : (Finset.univ.filter (fun J : Finset (Fin (2*r+1)) => r+1 ≤ J.card)).card
        ≤ (Finset.univ : Finset (Finset (Fin (2*r+1)))).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin] at h1
    exact h1
  calc (∑ ω ∈ Finset.univ.filter (fun ω => ε < |sortedBlockMedian r (weightedBlock r B w f ω)-θ|),
        (blockRecordLaw r B p).prob ω)
      ≤ ∑ J : Finset (Fin (2*r+1)), ∑ ω ∈ Finset.univ.filter
          (fun ω => J ∈ fam ∧ ∀ j ∈ J, ε < |weightedBlock r B w f ω j - θ|),
          (blockRecordLaw r B p).prob ω :=
        (Finset.sum_le_sum_of_subset_of_nonneg hsub
          fun ω _ _ => (blockRecordLaw r B p).nonneg ω).trans hub
    _ = ∑ J ∈ fam, ∑ ω ∈ Finset.univ.filter (fun ω => ∀ j ∈ J, ε < |weightedBlock r B w f ω j - θ|),
          (blockRecordLaw r B p).prob ω := hdrop
    _ = ∑ J ∈ fam, ∏ j ∈ J, (∑ ω ∈ Finset.univ.filter
          (fun ω => ε < |weightedBlock r B w f ω j - θ|),
          (blockRecordLaw r B p).prob ω) :=
        Finset.sum_congr rfl fun J _ => heterogeneous_block_bad_subset_product r B p w f θ ε J
    _ ≤ ∑ J ∈ fam, (1/16:ℝ)^(r+1) := Finset.sum_le_sum fun J hJ => hperJ J hJ
    _ = (fam.card : ℝ) * (1/16:ℝ)^(r+1) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2:ℝ)^(2*r+1) * (1/16:ℝ)^(r+1) := by
        refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (by norm_num) _)
        exact_mod_cast hcards

theorem heterogeneous_same_records_many_observables {X : Type} [Fintype X] [DecidableEq X]
    {Z : Type} [Fintype Z] [DecidableEq Z] (r B : ℕ) (p : Fin (2*r+1) → Fin B → FinDist X)
    (w : Z → Fin (2*r+1) → Fin B → ℝ) (f : Z → Fin (2*r+1) → Fin B → X → ℝ)
    (θ : Z → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hmean : ∀ z j, ∑ b, w z j b * (p j b).expect (f z j b) = θ z)
    (hvar : ∀ z j, ∑ b, (w z j b)^2 * (p j b).expect
      (fun x => (f z j b x-(p j b).expect (f z j b))^2) ≤ ε^2/16) :
    (∑ ω ∈ Finset.univ.filter
        (fun ω => ∃ z, ε < |sortedBlockMedian r (weightedBlock r B (w z) (f z) ω)-θ z|),
      (blockRecordLaw r B p).prob ω) ≤ (Fintype.card Z:ℝ) * ((2:ℝ)^(2*r+1)*(1/16:ℝ)^(r+1)) := by
  classical
  have hG5 : ∀ z : Z, (∑ ω ∈ Finset.univ.filter
        (fun ω => ε < |sortedBlockMedian r (weightedBlock r B (w z) (f z) ω)-θ z|),
        (blockRecordLaw r B p).prob ω) ≤ (2:ℝ)^(2*r+1)*(1/16:ℝ)^(r+1) :=
    fun z => heterogeneous_weighted_median_concentration r B p (w z) (f z) (θ z) ε hε
      (hmean z) (hvar z)
  calc (∑ ω ∈ Finset.univ.filter
        (fun ω => ∃ z, ε < |sortedBlockMedian r (weightedBlock r B (w z) (f z) ω)-θ z|),
      (blockRecordLaw r B p).prob ω)
      ≤ ∑ z : Z, (∑ ω ∈ Finset.univ.filter
          (fun ω => ε < |sortedBlockMedian r (weightedBlock r B (w z) (f z) ω)-θ z|),
          (blockRecordLaw r B p).prob ω) :=
        fintype_union_bound_mass ((blockRecordLaw r B p).prob)
          (fun ω => (blockRecordLaw r B p).nonneg ω)
          (fun z ω => ε < |sortedBlockMedian r (weightedBlock r B (w z) (f z) ω)-θ z|)
    _ ≤ (Fintype.card Z:ℝ) * ((2:ℝ)^(2*r+1)*(1/16:ℝ)^(r+1)) := by
        calc ∑ z : Z, (∑ ω ∈ Finset.univ.filter
              (fun ω => ε < |sortedBlockMedian r (weightedBlock r B (w z) (f z) ω)-θ z|),
              (blockRecordLaw r B p).prob ω)
            ≤ ∑ z : Z, (2:ℝ)^(2*r+1)*(1/16:ℝ)^(r+1) := Finset.sum_le_sum fun z _ => hG5 z
          _ = (Fintype.card Z:ℝ) * ((2:ℝ)^(2*r+1)*(1/16:ℝ)^(r+1)) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Qatlib.Concepts.MonteCarloMean.FinDistBounds
