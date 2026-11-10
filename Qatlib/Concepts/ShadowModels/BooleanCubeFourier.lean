/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds

namespace Qatlib.Concepts.ShadowModels.BooleanCubeFourier

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

def cubeChar {N : ℕ} (S : Finset (Fin N)) (x : Reg N) : ℝ :=
  ∏ i ∈ S, if x i then 1 else -1

def cubeWeight {N : ℕ} (x : Reg N) : ℕ := ∑ i, if x i then 0 else 1

def cubeDist {N : ℕ} (x y : Reg N) : ℕ := cubeWeight fun i => x i == y i

def cubeAlpha {N : ℕ} (p : FinDist (Reg N)) (S : Finset (Fin N)) : ℝ :=
  p.expect (cubeChar S)

def cubeAlphaWeightMass {N : ℕ} (p : FinDist (Reg N)) (k : ℕ) : ℝ :=
  ∑ S ∈ Finset.univ.powerset.filter (fun S => S.card = k), (cubeAlpha p S) ^ 2

def cubeAlphaTotalMass {N : ℕ} (p : FinDist (Reg N)) : ℝ :=
  ∑ S ∈ Finset.univ.powerset.erase ∅, (cubeAlpha p S) ^ 2

def IsCorrelationConcentrated {N : ℕ} (p : FinDist (Reg N)) (Δ : ℝ) (k : ℕ) (β : ℝ) : Prop :=
  β * cubeAlphaTotalMass p ≤ cubeAlphaWeightMass p k ∧
    β * Δ ≤ cubeAlphaWeightMass p k

def krawtchouk (N k t : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    (-1 : ℝ) ^ j * (Nat.choose t j : ℝ) * (Nat.choose (N - t) (k - j) : ℝ)

noncomputable def cubeUniformDist (N : ℕ) : FinDist (Reg N) where
  prob _ := (1 / 2 : ℝ) ^ N
  nonneg _ := by positivity
  sum_one := by
    simp [Fintype.card_pi, Reg]

open scoped Classical symmDiff

theorem cubeChar_mul {N : ℕ} (S T : Finset (Fin N)) (x : Reg N) :
    cubeChar S x * cubeChar T x = cubeChar (S ∆ T) x := by
  classical
  have hcube : ∀ (a : Fin N) (R : Finset (Fin N)), a ∉ R →
      cubeChar (insert a R) x = (if x a then 1 else -1) * cubeChar R x := by
    intro a R hR
    simp only [cubeChar, Finset.prod_insert hR]
  induction S using Finset.induction_on with
  | empty =>
    have hunion : (∅ : Finset (Fin N)) ∆ T = T := by
      ext i
      simp [Finset.mem_symmDiff]
    rw [hunion, cubeChar, Finset.prod_empty, one_mul]
  | insert a S ha ih =>
    by_cases hat : a ∈ T
    · have hmem : a ∈ S ∆ T := by simp [Finset.mem_symmDiff, ha, hat]
      have hunion : insert a S ∆ T = (S ∆ T).erase a := by
        ext i
        by_cases hia : i = a
        · subst hia
          simp [Finset.mem_symmDiff, Finset.mem_erase, ha, hat]
        · simp [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_erase, hia]
      have hcharSD : cubeChar (S ∆ T) x
          = (if x a then 1 else -1) * cubeChar ((S ∆ T).erase a) x := by
        conv_lhs => rw [← Finset.insert_erase hmem]
        exact hcube a _ (Finset.notMem_erase a (S ∆ T))
      rw [hunion, hcube a S ha, mul_assoc, ih, hcharSD]
      by_cases hxa : x a <;> simp [hxa]
    · have hnot : ¬ a ∈ S ∆ T := by simp [Finset.mem_symmDiff, ha, hat]
      have hunion : insert a S ∆ T = insert a (S ∆ T) := by
        ext i
        by_cases hia : i = a
        · subst hia
          simp [Finset.mem_symmDiff, Finset.mem_insert, ha, hat]
        · simp [Finset.mem_symmDiff, Finset.mem_insert, hia]
      rw [hunion, hcube a S ha, hcube a _ hnot, mul_assoc, ih]

theorem cubeChar_pair {N : ℕ} (S : Finset (Fin N)) (a b : Reg N) :
    cubeChar S a * cubeChar S b = cubeChar S (fun i => a i == b i) := by
  classical
  rw [cubeChar, cubeChar, cubeChar, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hxa : a i <;> by_cases hxb : b i <;> simp [hxa, hxb]

theorem krawtchouk_char_sum {N k : ℕ} (x : Reg N) :
    ∑ S ∈ Finset.univ.powerset.filter (fun S => S.card = k), cubeChar S x
      = krawtchouk N k (cubeWeight x) := by
  classical
  set A : Finset (Fin N) := Finset.univ.filter (fun i => ¬ x i) with hAdef
  have hAmem : ∀ i : Fin N, i ∈ A ↔ ¬ x i := fun i => by simp [hAdef]
  set t : ℕ := A.card with htdef
  set B : Finset (Fin N) := Finset.univ \ A with hBdef

  have hwt : cubeWeight x = t := by
    have h1 : (∑ i, if x i then 0 else 1) = ∑ i, if i ∈ A then 1 else 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hx : x i <;> simp [hx, hAmem i]
    have h2 : (∑ i : Fin N, if i ∈ A then 1 else 0) = A.card := by
      rw [← Finset.sum_subset A.subset_univ (fun i _ hi => if_neg hi)]
      simp
    show (∑ i, if x i then 0 else 1) = t
    rw [h1, h2, htdef]

  have hchar : ∀ S : Finset (Fin N), cubeChar S x = ((-1 : ℝ))^(S ∩ A).card := by
    intro S
    have hsplit : S ∩ A ∪ S \ A = S := by
      rw [Finset.union_comm, Finset.sdiff_union_inter]
    have hdisj : Disjoint (S ∩ A) (S \ A) :=
      Disjoint.symm
        (Finset.disjoint_of_subset_right Finset.inter_subset_right Finset.sdiff_disjoint)
    simp only [cubeChar]
    conv_lhs => rw [← hsplit]
    rw [Finset.prod_union hdisj]
    have hleft : (∏ i ∈ S ∩ A, if x i then 1 else -1) = ((-1 : ℝ))^(S ∩ A).card := by
      have hpt : ∀ i ∈ S ∩ A, (if x i then (1 : ℝ) else -1) = (-1 : ℝ) := by
        intro i hi
        have hx : ¬ x i := (hAmem i).mp (Finset.mem_of_mem_inter_right hi)
        simp [hx]
      rw [Finset.prod_congr rfl (fun i hi => hpt i hi), Finset.prod_const]
    have hright : (∏ i ∈ S \ A, (if x i then 1 else -1 : ℝ)) = 1 := by
      refine Finset.prod_eq_one fun i hi => ?_
      have hnx : ¬ (¬ x i) := fun hc => (Finset.mem_sdiff.mp hi).2 ((hAmem i).2 hc)
      simp [not_not.mp hnx]
    have hfinal : (∏ i ∈ S ∩ A, if x i then 1 else -1) * (∏ i ∈ S \ A, if x i then 1 else -1)
        = ((-1 : ℝ))^(S ∩ A).card := by
      rw [hleft, hright, mul_one]
    exact hfinal
  have hcardsplit : ∀ S : Finset (Fin N),
      (S ∩ A).card + (S \ A).card = S.card := fun S => by
    rw [← Finset.card_union_of_disjoint
        (Disjoint.symm
          (Finset.disjoint_of_subset_right Finset.inter_subset_right Finset.sdiff_disjoint)),
      Finset.union_comm, Finset.sdiff_union_inter]
  have hBc : B.card = N - t := by
    rw [hBdef, Finset.card_sdiff_of_subset A.subset_univ, Finset.card_univ,
      Fintype.card_fin, htdef]

  have hregroup :
      ∑ S ∈ Finset.univ.powerset.filter (fun S => S.card = k), cubeChar S x
        = ∑ p ∈ A.powerset ×ˢ B.powerset,
            (if p.1.card + p.2.card = k then ((-1 : ℝ))^p.1.card else 0) := by
    rw [Finset.sum_filter]
    refine Finset.sum_nbij'
      (i := fun S : Finset (Fin N) => (S ∩ A, S \ A))
      (j := fun p : Finset (Fin N) × Finset (Fin N) => p.1 ∪ p.2) ?_ ?_ ?_ ?_ ?_
    · intro S _
      have hsub2 : S \ A ⊆ B := by
        intro u hu
        rw [hBdef]
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, (Finset.mem_sdiff.mp hu).2⟩
      show (S ∩ A, S \ A) ∈ A.powerset ×ˢ B.powerset
      exact Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
        Finset.mem_powerset.mpr hsub2⟩
    · rintro ⟨T, U⟩ -
      show (T ∪ U) ∈ Finset.univ.powerset
      exact Finset.mem_powerset.mpr (Finset.subset_univ _)
    · intro S _
      show (S ∩ A) ∪ (S \ A) = S
      rw [Finset.union_comm, Finset.sdiff_union_inter]
    · rintro ⟨T, U⟩ hp
      obtain ⟨hTA, hUB⟩ := Finset.mem_product.mp hp
      have hsT : T ⊆ A := Finset.mem_powerset.mp hTA
      have hsU : U ⊆ B := Finset.mem_powerset.mp hUB
      have hUnotA : ∀ u ∈ U, u ∉ A := by
        intro u hu
        have huB : u ∈ B := hsU hu
        rw [hBdef] at huB
        exact (Finset.mem_sdiff.mp huB).2
      have hdisj : Disjoint U A := Finset.disjoint_left.mpr hUnotA
      have hintE : U ∩ A = ∅ := by
        ext u
        by_cases hu : u ∈ U
        · simp [hu, hUnotA u hu]
        · simp [hu]
      have hint1 : (T ∪ U) ∩ A = T := by
        rw [Finset.union_inter_distrib_right,
          show T ∩ A = T from by simp [hsT],
          show U ∩ A = ∅ from hintE, Finset.union_empty]
      have hint2 : (T ∪ U) \ A = U := by
        rw [Finset.union_sdiff_distrib,
          show T \ A = ∅ from Finset.sdiff_eq_empty_iff_subset.mpr hsT,
          Finset.empty_union, Finset.sdiff_eq_self_of_disjoint hdisj]
      show ((T ∪ U) ∩ A, (T ∪ U) \ A) = (T, U)
      rw [hint1, hint2]
    · intro S _
      show (if S.card = k then cubeChar S x else 0)
          = (if (S ∩ A).card + (S \ A).card = k then ((-1 : ℝ))^(S ∩ A).card else 0)
      rw [hchar S, ← hcardsplit S]

  rw [hregroup, Finset.sum_product]
  simp only []
  have hinner : ∀ T : Finset (Fin N), (∑ U ∈ B.powerset,
      (if T.card + U.card = k then ((-1 : ℝ))^T.card else 0))
      = (if T.card ≤ k then ((-1 : ℝ))^T.card * ((B.card.choose (k - T.card) : ℕ) : ℝ)
        else 0) := by
    intro T
    by_cases hTk : T.card ≤ k
    · rw [if_pos hTk]
      have hcond : ∀ U ∈ B.powerset,
          (if T.card + U.card = k then ((-1 : ℝ))^T.card else 0)
            = (if U.card = k - T.card then ((-1 : ℝ))^T.card else 0) := by
        intro U _
        by_cases hc : T.card + U.card = k
        · rw [if_pos hc, if_pos (by omega)]
        · rw [if_neg hc, if_neg (by omega)]
      rw [Finset.sum_congr rfl (fun U hU => hcond U hU),
        ← Finset.sum_filter (s := B.powerset) (p := fun U => U.card = k - T.card)
          (f := fun _ => ((-1 : ℝ))^T.card),
        Finset.sum_const, ← Finset.powersetCard_eq_filter, Finset.card_powersetCard,
        nsmul_eq_mul']
    · rw [if_neg hTk]
      exact Finset.sum_eq_zero fun U _ => if_neg (by omega)
  rw [Finset.sum_congr rfl (fun T _hT => hinner T)]

  rw [Finset.sum_powerset_apply_card
    (f := fun m => (if m ≤ k then ((-1 : ℝ))^m * ((B.card.choose (k - m) : ℕ) : ℝ)
      else 0)) (x := A), hBc, hwt, ← htdef]
  simp only [nsmul_eq_mul']
  have hkraw : krawtchouk N k t = ∑ j ∈ Finset.range (k + 1),
      (-1 : ℝ)^j * ((Nat.choose t j : ℕ) : ℝ)
        * ((Nat.choose (N - t) (k - j) : ℕ) : ℝ) := rfl
  by_cases htk : t ≤ k
  · have hconv : ∀ m ∈ Finset.range (t + 1),
        (if m ≤ k then ((-1 : ℝ))^m * ((Nat.choose (N - t) (k - m) : ℕ) : ℝ) else 0)
          * ((Nat.choose t m : ℕ) : ℝ)
        = (-1 : ℝ)^m * ((Nat.choose t m : ℕ) : ℝ)
          * ((Nat.choose (N - t) (k - m) : ℕ) : ℝ) := by
      intro m hm
      have hmk : m ≤ k := Nat.le_trans (Nat.le_of_lt_succ (Finset.mem_range.mp hm)) htk
      rw [if_pos hmk]
      ring
    have hsub : Finset.range (t + 1) ⊆ Finset.range (k + 1) :=
      Finset.range_subset_range.mpr (Nat.succ_le_succ htk)
    have hzero : ∀ m ∈ Finset.range (k + 1), m ∉ Finset.range (t + 1) →
        (-1 : ℝ)^m * ((Nat.choose t m : ℕ) : ℝ)
          * ((Nat.choose (N - t) (k - m) : ℕ) : ℝ) = 0 := by
      intro m hm hnm
      have hmt : t < m := by
        have h' : ¬ m < t + 1 := fun hc => hnm (Finset.mem_range.mpr hc)
        omega
      have hz : ((Nat.choose t m : ℕ) : ℝ) = 0 := by
        rw [Nat.choose_eq_zero_of_lt hmt, Nat.cast_zero]
      rw [hz, mul_zero, zero_mul]
    rw [Finset.sum_congr rfl hconv, Finset.sum_subset hsub hzero, ← hkraw]
  · have hkt : k < t := by omega
    have hkey : ∀ m ∈ Finset.range (k + 1),
        (if m ≤ k then ((-1 : ℝ))^m * ((Nat.choose (N - t) (k - m) : ℕ) : ℝ) else 0)
          * ((Nat.choose t m : ℕ) : ℝ)
        = (-1 : ℝ)^m * ((Nat.choose t m : ℕ) : ℝ)
          * ((Nat.choose (N - t) (k - m) : ℕ) : ℝ) := by
      intro m hm
      have hmk : m ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
      rw [if_pos hmk]
      ring
    have hsub : Finset.range (k + 1) ⊆ Finset.range (t + 1) :=
      Finset.range_subset_range.mpr (Nat.succ_le_succ (Nat.le_of_lt hkt))
    have hzero : ∀ m ∈ Finset.range (t + 1), m ∉ Finset.range (k + 1) →
        (if m ≤ k then ((-1 : ℝ))^m * ((Nat.choose (N - t) (k - m) : ℕ) : ℝ) else 0)
          * ((Nat.choose t m : ℕ) : ℝ) = 0 := by
      intro m hm hnm
      have hmk : k < m := by
        have h' : ¬ m < k + 1 := fun hc => hnm (Finset.mem_range.mpr hc)
        omega
      rw [if_neg (Nat.not_le.mpr hmk), zero_mul]
    rw [hkraw, ← Finset.sum_subset hsub hzero, Finset.sum_congr rfl hkey]

end Qatlib.Concepts.ShadowModels.BooleanCubeFourier
