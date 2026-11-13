/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GraphEnergy.ZeroEnergy.LazyGraphDefs

/-!
# Stationarity and reversibility of the lazy graph walk

This module verifies nonnegative normalized transition rows and stationary weights for the lazy
graph kernel. It proves detailed balance and global balance, including the zero-volume
convention. These classical reversible-chain properties underlie the quantum-walk construction
of [Szegedy2004].

## Main statements

* `kernel_sum` and `stationary_sum`: normalization of transition and stationary weights.
* `detailed_balance` and `global_balance`: reversibility and stationarity.
* `g1`: the combined stochastic and stationary laws.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.GraphStationary.StationaryLaw
open Qatlib.Concepts.GraphEnergy.ZeroEnergy Finset
open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in

/-- Every real vertex degree is nonnegative. -/
lemma degree_nonneg (x : V) : 0 ≤ degree G x := by
  unfold degree
  exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num

omit [DecidableEq V] in

/-- The graph volume is nonnegative. -/
lemma volume_nonneg : 0 ≤ volume G := by
  unfold volume
  exact Finset.sum_nonneg fun x _ => degree_nonneg G x

omit [DecidableEq V] in

/-- If graph volume is zero, every vertex has degree zero. -/
lemma degree_eq_zero_of_volume_eq_zero (hv : volume G = 0) (x : V) : degree G x = 0 := by
  unfold volume at hv
  exact (Finset.sum_eq_zero_iff_of_nonneg fun i _ => degree_nonneg G i).1 hv x (mem_univ x)

omit [DecidableEq V] in

/-- A vertex of degree zero is adjacent to no vertex. -/
lemma not_adj_of_degree_eq_zero {x : V} (hx : degree G x = 0) (y : V) : ¬ G.Adj x y := by
  intro h
  unfold degree at hx
  have hterm :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun z _ => by split_ifs <;> norm_num : ∀ z ∈ Finset.univ, 0 ≤ (if G.Adj x z then (1 : ℝ) else 0))).1
      hx y (mem_univ y)
  simp [h] at hterm

/-- Every entry of the lazy graph kernel is nonnegative. -/
lemma kernel_nonneg (x y : V) : 0 ≤ kernel G x y := by
  by_cases hx : degree G x = 0
  · simp [kernel, hx]
    split_ifs <;> norm_num
  · have hpos : 0 < degree G x := lt_of_le_of_ne (degree_nonneg G x) (Ne.symm hx)
    have hker : kernel G x y =
        (if x = y then (1 / 2 : ℝ) else 0) +
          (if G.Adj x y then 1 / (2 * degree G x) else 0) := by
      simp [kernel, hx]
    rw [hker]
    have h1 : 0 ≤ (if x = y then (1 / 2 : ℝ) else 0) := by split_ifs <;> norm_num
    have h2 : 0 ≤ (if G.Adj x y then 1 / (2 * degree G x) else 0) := by
      split_ifs with h
      · positivity
      · norm_num
    exact add_nonneg h1 h2

/-- Summing a fixed scalar supported at the diagonal index returns that scalar. -/
lemma sum_diag (x : V) (c : ℝ) : ∑ y : V, (if x = y then c else 0) = c := by
  have hswap : ∀ y, (if x = y then c else 0) = (if y = x then c else 0) := by
    intro y
    by_cases hy : x = y
    · simp [hy]
    · simp [hy, Ne.symm hy]
  simp_rw [hswap]
  simp [Finset.sum_ite_eq']

/-- Each row of the lazy graph kernel sums to one. -/
lemma kernel_sum (x : V) : ∑ y, kernel G x y = 1 := by
  by_cases hx : degree G x = 0
  · simp only [kernel, hx, ite_true]
    exact sum_diag x (1 : ℝ)
  · have hpos : 0 < degree G x := lt_of_le_of_ne (degree_nonneg G x) (Ne.symm hx)
    have hker : ∀ y, kernel G x y =
        (if x = y then (1 / 2 : ℝ) else 0) +
          (if G.Adj x y then 1 / (2 * degree G x) else 0) := by
      intro y
      simp [kernel, hx]
    simp_rw [hker, Finset.sum_add_distrib]
    have hdiag : ∑ y : V, (if x = y then (1 / 2 : ℝ) else 0) = 1 / 2 :=
      sum_diag x (1 / 2 : ℝ)
    have hnbr : ∑ y : V, (if G.Adj x y then 1 / (2 * degree G x) else 0) = 1 / 2 := by
      calc ∑ y : V, (if G.Adj x y then 1 / (2 * degree G x) else 0)
          = ∑ y : V, (1 / (2 * degree G x)) * (if G.Adj x y then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl fun y _ => ?_
            by_cases hy : G.Adj x y
            · simp [hy]
            · simp [hy]
        _ = (1 / (2 * degree G x)) * ∑ y : V, (if G.Adj x y then (1 : ℝ) else 0) := by
            rw [← Finset.mul_sum]
        _ = (1 / (2 * degree G x)) * degree G x := by
            unfold degree
            rfl
        _ = 1 / 2 := by field_simp [hpos.ne']
    linarith

omit [DecidableEq V] in

/-- Each stationary vertex weight is nonnegative. -/
lemma stationary_nonneg [Nonempty V] (x : V) : 0 ≤ stationary G x := by
  by_cases hv : volume G = 0
  · have hcard : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
    simp only [stationary, hv, ite_true, one_div]
    exact inv_nonneg.mpr hcard.le
  · have hvpos : 0 < volume G := lt_of_le_of_ne (volume_nonneg G) (Ne.symm hv)
    simp [stationary, hv]
    exact div_nonneg (degree_nonneg G x) hvpos.le

omit [DecidableEq V] in

/-- The stationary weights on a nonempty finite vertex type sum to one. -/
lemma stationary_sum [Nonempty V] : ∑ x, stationary G x = 1 := by
  by_cases hv : volume G = 0
  · have hcard : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp only [stationary, hv, ite_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [hcard]
  · have hvpos : 0 < volume G := lt_of_le_of_ne (volume_nonneg G) (Ne.symm hv)
    simp only [stationary, hv, ite_false]
    rw [← Finset.sum_div]
    unfold volume
    exact div_self hvpos.ne'

/-- The stationary transition weight from `x` to `y` equals that from `y` to `x`. -/
lemma detailed_balance [Nonempty V] (x y : V) :
    stationary G x * kernel G x y = stationary G y * kernel G y x := by
  by_cases hv : volume G = 0
  · have hk : ∀ a b, kernel G a b = if a = b then (1 : ℝ) else 0 := by
      intro a b
      have ha : degree G a = 0 := degree_eq_zero_of_volume_eq_zero G hv a
      simp [kernel, ha]
    simp only [stationary, hv, ite_true, hk]
    by_cases hxy : x = y
    · simp [hxy]
    · simp [hxy, Ne.symm hxy]
  · have hvpos : 0 < volume G := lt_of_le_of_ne (volume_nonneg G) (Ne.symm hv)
    simp only [stationary, hv, ite_false]
    by_cases hx : degree G x = 0
    · have hnx : ¬ G.Adj x y := not_adj_of_degree_eq_zero G hx y
      have hny : ¬ G.Adj y x := fun h => hnx (G.adj_symm h)
      by_cases hxy : x = y
      · subst hxy
        simp [kernel, hx]
      · by_cases hy : degree G y = 0
        · simp [kernel, hx, hy, hxy, Ne.symm hxy]
        · simp [kernel, hx, hy, hxy, Ne.symm hxy, hny]
    · by_cases hy : degree G y = 0
      · have hny : ¬ G.Adj y x := not_adj_of_degree_eq_zero G hy x
        have hnx : ¬ G.Adj x y := fun h => hny (G.adj_symm h)
        by_cases hxy : x = y
        · subst hxy
          simp [hy] at hx
        · simp [kernel, hx, hy, hxy, Ne.symm hxy, hnx]
      · have hxpos : 0 < degree G x := lt_of_le_of_ne (degree_nonneg G x) (Ne.symm hx)
        have hypos : 0 < degree G y := lt_of_le_of_ne (degree_nonneg G y) (Ne.symm hy)
        simp only [kernel, hx, hy, ite_false]
        by_cases hxy : x = y
        · subst hxy
          simp
        · by_cases hadj : G.Adj x y
          · have hadj' : G.Adj y x := G.adj_symm hadj
            simp [hxy, Ne.symm hxy, hadj, hadj']
            field_simp [hxpos.ne', hypos.ne', hvpos.ne']
          · have hadj' : ¬ G.Adj y x := fun h => hadj (G.adj_symm h)
            simp [hxy, Ne.symm hxy, hadj, hadj']

/-- Summing the stationary incoming transition weights at a vertex returns its stationary
weight. -/
lemma global_balance [Nonempty V] (y : V) :
    ∑ x, stationary G x * kernel G x y = stationary G y := by
  calc ∑ x, stationary G x * kernel G x y
      = ∑ x, stationary G y * kernel G y x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        exact detailed_balance G x y
    _ = stationary G y * ∑ x, kernel G y x := by rw [Finset.mul_sum]
    _ = stationary G y := by rw [kernel_sum G y, mul_one]

/-- The lazy graph kernel and stationary weights are nonnegative and normalized and satisfy both
detailed balance and global balance. -/
theorem g1 :
    ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ x y, 0 ≤ kernel G x y) ∧ (∀ x, ∑ y, kernel G x y = 1) ∧
      (∀ x, 0 ≤ stationary G x) ∧ (∑ x, stationary G x = 1) ∧
      (∀ x y, stationary G x * kernel G x y = stationary G y * kernel G y x) ∧
      (∀ y, ∑ x, stationary G x * kernel G x y = stationary G y) := by
  intro V _ _ _ G _
  exact ⟨kernel_nonneg G, kernel_sum G, stationary_nonneg G, stationary_sum G,
    detailed_balance G, global_balance G⟩

end Qatlib.Concepts.GraphStationary.StationaryLaw
