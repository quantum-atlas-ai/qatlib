/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.SensitivityCombinatorics
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ParityPolynomialBound
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryComplexity.DegreeMethod.SensitivityCombinatorics

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib
open scoped Classical BigOperators

def sensitiveBlockIndex {n : ℕ} (F : Finset (Finset (Fin n))) (i : Fin n) : Option F :=
  if h : ∃ B : F, i ∈ B.val then some (Classical.choose h) else none

def sensitiveBlockPoint {n : ℕ} (x : Fin n → Bool) (F : Finset (Finset (Fin n)))
    (y : F → Bool) (i : Fin n) : Bool :=
  match sensitiveBlockIndex F i with
  | none => x i
  | some B => Bool.xor (x i) (y B)

def sensitiveBlockCoordinate {n : ℕ} (x : Fin n → Bool) (F : Finset (Finset (Fin n)))
    (i : Fin n) : MvPolynomial F ℝ :=
  match sensitiveBlockIndex F i with
  | none => MvPolynomial.C (if x i then 1 else 0)
  | some B => if x i then 1-MvPolynomial.X B else MvPolynomial.X B

def sensitiveBlockPolynomial {n : ℕ} (x : Fin n → Bool) (F : Finset (Finset (Fin n)))
    (p : MvPolynomial (Fin n) ℝ) : MvPolynomial F ℝ :=
  p.eval₂ MvPolynomial.C (sensitiveBlockCoordinate x F)

lemma sensitiveBlockIndex_mem {n : ℕ} (F : Finset (Finset (Fin n))) (i : Fin n) (B : F)
    (h : sensitiveBlockIndex F i = some B) : i ∈ B.val := by
  unfold sensitiveBlockIndex at h
  split_ifs at h with hi
  · have he : Classical.choose hi = B := Option.some.inj h
    simpa only [he] using Classical.choose_spec hi

lemma sensitiveBlockIndex_eq {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool)
    (F : Finset (Finset (Fin n))) (hF : SensitiveFamily f x F) (i : Fin n) (B : F)
    (hi : i ∈ B.val) : sensitiveBlockIndex F i = some B := by
  have hex : ∃ B : F, i ∈ B.val := ⟨B,hi⟩
  unfold sensitiveBlockIndex
  rw [dif_pos hex]
  congr 1
  apply Subtype.ext
  by_contra hn
  have hd := hF.2 (Classical.choose hex).val (Classical.choose hex).property B.val B.property hn
  have hm : i ∈ (Classical.choose hex).val ∩ B.val :=
    Finset.mem_inter.mpr ⟨Classical.choose_spec hex,hi⟩
  rw [hd] at hm
  simp at hm

theorem sensitiveBlockCoordinate_eval {n : ℕ} (x : Fin n → Bool)
    (F : Finset (Finset (Fin n))) (y : F → Bool) (i : Fin n) :
    MvPolynomial.eval (fun B => if y B then (1 : ℝ) else 0) (sensitiveBlockCoordinate x F i) =
      if sensitiveBlockPoint x F y i then (1 : ℝ) else 0 := by
  unfold sensitiveBlockCoordinate sensitiveBlockPoint
  cases sensitiveBlockIndex F i with
  | none => simp
  | some B => cases x i <;> cases hyB : y B <;> simp [hyB]

theorem sensitiveBlockPolynomial_eval {n : ℕ} (x : Fin n → Bool)
    (F : Finset (Finset (Fin n))) (p : MvPolynomial (Fin n) ℝ) (y : F → Bool) :
    MvPolynomial.eval (fun B => if y B then (1 : ℝ) else 0) (sensitiveBlockPolynomial x F p) =
      MvPolynomial.eval (fun i => if sensitiveBlockPoint x F y i then (1 : ℝ) else 0) p := by
  rw [sensitiveBlockPolynomial,← MvPolynomial.eval_assoc]
  apply congrArg (fun v : Fin n → ℝ => MvPolynomial.eval v p)
  funext i
  exact sensitiveBlockCoordinate_eval x F y i

theorem sensitiveBlockPoint_zero {n : ℕ} (x : Fin n → Bool) (F : Finset (Finset (Fin n))) :
    sensitiveBlockPoint x F (fun _ => false) = x := by
  funext i
  unfold sensitiveBlockPoint
  cases sensitiveBlockIndex F i <;> simp

theorem sensitiveBlockPoint_singleton {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool)
    (F : Finset (Finset (Fin n))) (hF : SensitiveFamily f x F) (B : F) :
    sensitiveBlockPoint x F (fun C => decide (C = B)) = flipBlock x B.val := by
  funext i
  by_cases hi : i ∈ B.val
  · rw [sensitiveBlockPoint,sensitiveBlockIndex_eq f x F hF i B hi]
    simp [flipBlock,hi]
  · cases he : sensitiveBlockIndex F i with
    | none => simp [sensitiveBlockPoint,he,flipBlock,hi]
    | some C =>
      have hC := sensitiveBlockIndex_mem F i C he
      have hne : C ≠ B := by intro hn; subst C; exact hi hC
      simp [sensitiveBlockPoint,he,flipBlock,hi,hne]

theorem affine_substitution_totalDegree {I J : Type} [DecidableEq I] [DecidableEq J]
    (p : MvPolynomial I ℝ) (v : I → MvPolynomial J ℝ) (hv : ∀ i, (v i).totalDegree ≤ 1) :
    (p.eval₂ MvPolynomial.C v).totalDegree ≤ p.totalDegree := by
  rw [MvPolynomial.eval₂_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro d hd
  have hp : (∏ i ∈ d.support, v i ^ d i).totalDegree ≤ ∑ i ∈ d.support, d i := by
    calc
      _ ≤ ∑ i ∈ d.support, (v i ^ d i).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
      _ ≤ _ := Finset.sum_le_sum fun i _ =>
        (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left (d i) (hv i))
  have hm := MvPolynomial.totalDegree_mul (MvPolynomial.C (p.coeff d)) (∏ i ∈ d.support, v i ^ d i)
  simp only [MvPolynomial.totalDegree_C,zero_add] at hm
  exact hm.trans (hp.trans (MvPolynomial.le_totalDegree hd))

lemma block_neg_totalDegree {I : Type} (p : MvPolynomial I ℝ) : (-p).totalDegree ≤ p.totalDegree := by
  rw [← neg_one_smul ℝ p]
  exact MvPolynomial.totalDegree_smul_le _ _

lemma block_complement_totalDegree {I : Type} (p : MvPolynomial I ℝ) :
    (1-p).totalDegree ≤ p.totalDegree := by
  rw [sub_eq_add_neg]
  exact (MvPolynomial.totalDegree_add _ _).trans
    (max_le (by simp only [MvPolynomial.totalDegree_one]; exact Nat.zero_le _) (block_neg_totalDegree p))

theorem sensitiveBlockPolynomial_totalDegree {n : ℕ} (x : Fin n → Bool)
    (F : Finset (Finset (Fin n))) (p : MvPolynomial (Fin n) ℝ) :
    (sensitiveBlockPolynomial x F p).totalDegree ≤ p.totalDegree := by
  apply affine_substitution_totalDegree
  intro i
  unfold sensitiveBlockCoordinate
  cases sensitiveBlockIndex F i with
  | none => simp only [MvPolynomial.totalDegree_C]; exact Nat.zero_le _
  | some B =>
    split_ifs
    · exact (block_complement_totalDegree _).trans (by simp)
    · simp

theorem block_zero_weight {I : Type} [Fintype I] [DecidableEq I] (y : I → Bool)
    (hy : boolWeight y = 0) : y = fun _ => false := by
  have hs : boolSupp y = ∅ := Finset.card_eq_zero.mp hy
  funext i
  cases hi : y i
  · rfl
  · have hm : i ∈ boolSupp y := (boolSupp_mem_iff y i).mpr hi
    rw [hs] at hm
    simp at hm

theorem block_one_weight {I : Type} [Fintype I] [DecidableEq I] (y : I → Bool)
    (hy : boolWeight y = 1) : ∃ j : I, y = fun i => decide (i = j) := by
  obtain ⟨j,hj⟩ := Finset.card_eq_one.mp hy
  refine ⟨j,?_⟩
  funext i
  by_cases hij : i = j
  · have hm : i ∈ boolSupp y := by rw [hj]; simp [hij]
    have htrue := (boolSupp_mem_iff y i).mp hm
    simpa [hij] using htrue
  · cases hi : y i
    · simp [hij]
    · have hm : i ∈ boolSupp y := (boolSupp_mem_iff y i).mpr hi
      rw [hj] at hm
      simp [hij] at hm

theorem block_layerAverage_bounds {I : Type} [Fintype I] [DecidableEq I]
    (p : MvPolynomial I ℝ) (k : ℕ) (hk : k ≤ Fintype.card I) (l u : ℝ)
    (hb : ∀ y : I → Bool, boolWeight y = k →
      l ≤ p.eval (boolPoint y) ∧ p.eval (boolPoint y) ≤ u) :
    l ≤ layerAverage p k ∧ layerAverage p k ≤ u := by
  have hcard : (0 : ℝ) < Nat.choose (Fintype.card I) k := by exact_mod_cast Nat.choose_pos hk
  have hbot : (∑ y : {y : I → Bool // boolWeight y = k}, l) ≤
      ∑ y : {y : I → Bool // boolWeight y = k}, p.eval (boolPoint y.val) :=
    Finset.sum_le_sum fun y _ => (hb y.val y.property).1
  have htop : (∑ y : {y : I → Bool // boolWeight y = k}, p.eval (boolPoint y.val)) ≤
      ∑ y : {y : I → Bool // boolWeight y = k}, u :=
    Finset.sum_le_sum fun y _ => (hb y.val y.property).2
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hbot htop
  rw [card_level_real k] at hbot htop
  unfold layerAverage layerSum
  rw [← div_eq_mul_inv]
  refine ⟨(le_div_iff₀ hcard).mpr ?_,(div_le_iff₀ hcard).mpr ?_⟩
  · simpa only [mul_comm] using hbot
  · simpa only [mul_comm] using htop

end Qatlib.Concepts.QueryComplexity.DegreeMethod
