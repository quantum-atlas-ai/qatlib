/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.CommutatorGrowth
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.CommutatorProducts

open scoped BigOperators Classical Matrix.Norms.L2Operator
open CommutatorGrowth BCHCommMass
open Qatlib.Concepts.TrotterFormula.GeneralOrder

def doubleSuccessor (l : ℕ) : (Fin l → ℕ) ↪ (Fin l → ℕ) where
  toFun v i := 2 * (v i + 1)
  inj' := by intro v w h; funext i; have hi := congrFun h i; dsimp at hi; omega

def positiveFiber (l j : ℕ) : Finset (Fin l → ℕ) :=
  (Finset.finAntidiagonal l j).filter (fun v => ∀ i, Even (v i) ∧ 2 ≤ v i)

theorem sum_doubleSuccessor (l : ℕ) (v : Fin l → ℕ) :
    (∑ i, doubleSuccessor l v i) = 2 * ((∑ i, v i) + l) := by
  change (∑ i, 2 * (v i + 1)) = _
  rw [← Finset.mul_sum]
  congr 1
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]

theorem positiveFiber_eq (l n : ℕ) :
    positiveFiber l (2 * (n + l)) = (Finset.finAntidiagonal l n).map (doubleSuccessor l) := by
  ext w
  constructor
  · intro hw
    obtain ⟨hwSum, hwPos⟩ := Finset.mem_filter.mp hw
    have hs : ∑ i, w i = 2 * (n + l) := Finset.mem_finAntidiagonal.mp hwSum
    let v : Fin l → ℕ := fun i => w i / 2 - 1
    have he : doubleSuccessor l v = w := by
      funext i
      obtain ⟨a, ha⟩ := (hwPos i).1
      have hp := (hwPos i).2
      dsimp only [doubleSuccessor, Function.Embedding.coeFn_mk, v]
      omega
    have hv : ∑ i, v i = n := by
      have h := sum_doubleSuccessor l v
      rw [he, hs] at h
      omega
    exact Finset.mem_map.mpr ⟨v, Finset.mem_finAntidiagonal.mpr hv, he⟩
  · intro hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_finAntidiagonal.mpr
      rw [sum_doubleSuccessor, Finset.mem_finAntidiagonal.mp hv]
    · intro i
      constructor
      · exact ⟨v i + 1, by dsimp [doubleSuccessor]; omega⟩
      · dsimp [doubleSuccessor]
        omega

variable {I : Type} [Fintype I]

def rawProduct (xs : List (Matrix I I ℂ)) (l n : ℕ) : ℝ :=
  ∑ v ∈ Finset.finAntidiagonal l n, ∏ i, pfCommAlphaSelf xs (2 * v i + 3)

def positiveProduct (xs : List (Matrix I I ℂ)) (j l : ℕ) : ℝ :=
  ∑ v ∈ positiveFiber l j, ∏ i, pfCommAlphaSelf xs (v i + 1)

theorem positiveProduct_nonneg (xs : List (Matrix I I ℂ)) (j l : ℕ) :
    0 ≤ positiveProduct xs j l :=
  Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => profile_nonneg xs _

theorem rawProduct_nonneg (xs : List (Matrix I I ℂ)) (l n : ℕ) : 0 ≤ rawProduct xs l n :=
  Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => profile_nonneg xs _

theorem positiveProduct_eq_raw (xs : List (Matrix I I ℂ)) (l n : ℕ) :
    positiveProduct xs (2 * (n + l)) l = rawProduct xs l n := by
  rw [positiveProduct, positiveFiber_eq, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.prod_congr rfl
  intro i _
  congr 1

variable [DecidableEq I]

theorem normalized_fiber (xs : List (Matrix I I ℂ)) (l n : ℕ) :
    (∑ v ∈ Finset.finAntidiagonal l n,
      ∏ i, (pfCommAlphaSelf xs (2 * v i + 3) / boundingScale xs ^ (2 * v i + 3))) =
        rawProduct xs l n / boundingScale xs ^ (2 * n + 3 * l) := by
  rw [rawProduct, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v hv
  have he : ∑ i, (2 * v i + 3) = 2 * n + 3 * l := by
    have hn : ∑ i, v i = n := Finset.mem_finAntidiagonal.mp hv
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hn, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, he]

theorem rawProduct_le_scale (xs : List (Matrix I I ℂ)) (l n : ℕ) :
    rawProduct xs l n ≤ boundingScale xs ^ (2 * n + 3 * l) := by
  let f : ℕ → ℝ := fun j => pfCommAlphaSelf xs (2 * j + 3) / boundingScale xs ^ (2 * j + 3)
  have hs := BCHMassProducts.tuple_hasSum f (normalized_summable xs) (normalized_nonneg xs) l
  have hfin : (∑ v ∈ Finset.finAntidiagonal l n, ∏ i, f (v i)) ≤ (∑' j, f j) ^ l := by
    rw [← hs.tsum_eq]
    exact hs.summable.sum_le_tsum _
        (fun v _ => Finset.prod_nonneg fun i _ => normalized_nonneg xs (v i))
  have hbase : (∑' j, f j) ≤ 1 := (normalized_sum_le xs).trans (by norm_num)
  have hpow : (∑' j, f j) ^ l ≤ 1 :=
    pow_le_one₀ (tsum_nonneg (normalized_nonneg xs)) hbase
  have h := hfin.trans hpow
  change (∑ v ∈ Finset.finAntidiagonal l n,
    ∏ i, (pfCommAlphaSelf xs (2 * v i + 3) / boundingScale xs ^ (2 * v i + 3))) ≤ 1 at h
  rw [normalized_fiber] at h
  exact (div_le_iff₀ (pow_pos (boundingScale_pos xs) _)).mp h |>.trans_eq (one_mul _)

end Qatlib.Papers.CommutLCHS26.MainResults.CommutatorProducts
