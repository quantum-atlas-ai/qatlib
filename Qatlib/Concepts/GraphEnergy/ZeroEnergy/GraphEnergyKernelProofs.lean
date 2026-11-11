/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GraphEnergy.ZeroEnergy.GraphEnergyKernelDefs
import Qatlib.Concepts.DirichletForm.EnergyIdentity
import Mathlib.Combinatorics.SimpleGraph.LapMatrix

/-!
# Positivity and the kernel of graph energy

This module proves nonnegativity of lazy graph energy and identifies its zero set with functions
constant across every edge. It also relates energy to the combinatorial Laplacian quadratic
form, treating zero graph volume separately. These classical graph-energy facts support the
Markov-chain framework of [Szegedy2004].

## Main statements

* `energy_eq_lapQuadratic_div`: energy is the Laplacian quadratic form divided by twice the
  positive graph volume.
* `energy_zero_iff_edge_constant`: nonnegativity and the edgewise zero-energy characterization.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
open Qatlib.Concepts.DirichletForm.EnergyIdentity

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.GraphEnergy.ZeroEnergy

open Qatlib.Concepts.GraphEnergy.ZeroEnergy Qatlib.Concepts.DirichletForm.EnergyIdentity
open Qatlib.Concepts.GraphStationary.StationaryLaw
open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in

/-- A vertex incident to an edge has positive degree. -/
theorem degree_pos_of_adj {x y : V} (h : G.Adj x y) : 0 < degree G x := by
  have hpos : ∀ z ∈ (Finset.univ : Finset V),
      (0 : ℝ) ≤ (if G.Adj x z then (1 : ℝ) else 0) := by
    intro z _
    split_ifs <;> norm_num
  have hle := Finset.single_le_sum hpos (Finset.mem_univ y)
  rw [if_pos h] at hle
  unfold degree
  linarith

omit [DecidableEq V] in

/-- A graph containing an edge has positive volume. -/
theorem volume_pos_of_adj {x y : V} (h : G.Adj x y) : 0 < volume G := by
  have hx : (0 : ℝ) < degree G x := degree_pos_of_adj G h
  have hle : degree G x ≤ volume G := by
    unfold volume
    exact Finset.single_le_sum (fun z _ => degree_nonneg G z) (Finset.mem_univ x)
  linarith

/-- The stationary transition weight along any graph edge is positive. -/
theorem edge_measure_pos_of_adj {x y : V} (h : G.Adj x y) :
    0 < stationary G x * kernel G x y := by
  have hdeg : 0 < degree G x := degree_pos_of_adj G h
  have hvol : 0 < volume G := volume_pos_of_adj G h
  have hdeg0 : degree G x ≠ 0 := ne_of_gt hdeg
  have hstat : stationary G x = degree G x / volume G := by
    simp [stationary, ne_of_gt hvol]
  have hxy : x ≠ y := G.ne_of_adj h
  have hker : kernel G x y = 1 / (2 * degree G x) := by
    simp [kernel, hdeg0, h, hxy]
  rw [hstat, hker]
  have hkey : degree G x / volume G * (1 / (2 * degree G x)) = 1 / (2 * volume G) := by
    field_simp
  rw [hkey]
  have h2 : (0 : ℝ) < 2 * volume G := by linarith
  exact div_pos zero_lt_one h2

/-- The lazy kernel at a vertex of degree zero is the point mass at that vertex. -/
theorem kernel_eq_of_degree_eq_zero {x y : V} (hdeg : degree G x = 0) :
    kernel G x y = if x = y then (1 : ℝ) else 0 := by
  simp [kernel, hdeg]

/-- For positive graph volume, a stationary transition term equals the squared difference
divided by twice the volume on edges and is zero elsewhere. -/
theorem term_eq_of_volume_pos (hv : 0 < volume G) (f : V → ℝ) (x y : V) :
    stationary G x * kernel G x y * (f x - f y) ^ 2 =
      if G.Adj x y then (f x - f y) ^ 2 / (2 * volume G) else 0 := by
  by_cases hdeg : degree G x = 0
  · have hna : ¬ G.Adj x y := not_adj_of_degree_eq_zero G hdeg y
    rw [if_neg hna]
    by_cases hxy : x = y
    · subst hxy
      simp [sub_self]
    · have hk : kernel G x y = 0 := by simp [kernel, hdeg, hxy]
      simp [hk]
  · have hdegp : 0 < degree G x := lt_of_le_of_ne (degree_nonneg G x) (Ne.symm hdeg)
    have hdeg0 : degree G x ≠ 0 := ne_of_gt hdegp
    have hvol0 : volume G ≠ 0 := ne_of_gt hv
    have hstat : stationary G x = degree G x / volume G := by
      simp [stationary, hvol0]
    by_cases hadj : G.Adj x y
    · have hxy : x ≠ y := G.ne_of_adj hadj
      have hk : kernel G x y = 1 / (2 * degree G x) := by
        simp [kernel, hdeg0, hadj, hxy]
      rw [hstat, hk, if_pos hadj]
      field_simp
    · rw [if_neg hadj]
      by_cases hxy : x = y
      · subst hxy
        simp [sub_self]
      · have hk : kernel G x y = 0 := by simp [kernel, hdeg0, hadj, hxy]
        simp [hk]

/-- For positive graph volume, lazy graph energy equals the real Laplacian quadratic form
divided by twice the volume. -/
theorem energy_eq_lapQuadratic_div [Nonempty V] (hv : 0 < volume G) (f : V → ℝ) :
    energy G f = Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) f f / (2 * volume G) := by
  rw [Qatlib.Concepts.DirichletForm.EnergyIdentity.g1 V G f]
  have hterm : ∀ x y : V, stationary G x * kernel G x y * (f x - f y) ^ 2 =
      if G.Adj x y then (f x - f y) ^ 2 / (2 * volume G) else 0 :=
    fun x y => term_eq_of_volume_pos G hv f x y
  have hdiv : ∀ x y : V,
      (if G.Adj x y then (f x - f y) ^ 2 / (2 * volume G) else 0) =
        (if G.Adj x y then (f x - f y) ^ 2 else 0) / (2 * volume G) := by
    intro x y
    by_cases h : G.Adj x y <;> simp [h]
  simp_rw [hterm, hdiv, ← Finset.sum_div]
  rw [SimpleGraph.lapMatrix_toLinearMap₂' ℝ G f]
  field_simp

/-- A graph of zero volume has zero energy for every real function. -/
theorem energy_eq_zero_of_volume_eq_zero (f : V → ℝ) (hv : volume G = 0) :
    energy G f = 0 := by
  unfold energy
  refine Finset.sum_eq_zero fun x _ => ?_
  have hdeg : degree G x = 0 := degree_eq_zero_of_volume_eq_zero G hv x
  have hsum : ∑ y, kernel G x y * f y = f x := by
    have hrew : ∀ y : V, kernel G x y * f y = if x = y then f x else 0 := by
      intro y
      rw [kernel_eq_of_degree_eq_zero G hdeg]
      by_cases hxy : x = y <;> simp [hxy]
    simp_rw [hrew]
    exact sum_diag x (f x)
  rw [hsum, sub_self, mul_zero]

/-- The real Laplacian quadratic form vanishes for a graph of zero volume. -/
theorem lapQuadratic_eq_zero_of_volume_eq_zero (f : V → ℝ) (hv : volume G = 0) :
    Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) f f = 0 := by
  have hedges : ∀ x y : V, G.Adj x y → f x = f y := by
    intro x y h
    exact absurd h (not_adj_of_degree_eq_zero G (degree_eq_zero_of_volume_eq_zero G hv x) y)
  exact (SimpleGraph.lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj ℝ G f).mpr hedges

/-- The real combinatorial Laplacian quadratic form is nonnegative. -/
theorem lapQuadratic_nonneg (f : V → ℝ) :
    0 ≤ Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) f f := by
  rw [Matrix.toLinearMap₂'_apply']
  exact (SimpleGraph.posSemidef_lapMatrix ℝ G).dotProduct_mulVec_nonneg f

/-- Lazy graph energy is nonnegative on a nonempty finite vertex type. -/
theorem energy_nonneg [Nonempty V] (f : V → ℝ) : 0 ≤ energy G f := by
  by_cases hv : volume G = 0
  · rw [energy_eq_zero_of_volume_eq_zero G f hv]
  · have hvpos : 0 < volume G := lt_of_le_of_ne (volume_nonneg G) (Ne.symm hv)
    rw [energy_eq_lapQuadratic_div G hvpos f]
    have hpos : (0 : ℝ) < 2 * volume G := by linarith
    exact div_nonneg (lapQuadratic_nonneg G f) hpos.le

/-- Lazy graph energy is nonnegative and vanishes exactly for functions constant across every
edge, equivalently when `dirichletSum` vanishes. The statement also gives positive edge
weights and the Laplacian formulas for positive and zero graph volume. -/
theorem energy_zero_iff_edge_constant :
    ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ),
      0 ≤ energy G f
      ∧ (energy G f = 0 ↔ ∀ x y : V, G.Adj x y → f x = f y)
      ∧ (∀ x y : V, G.Adj x y → 0 < stationary G x * kernel G x y)
      ∧ (energy G f = 0 ↔ dirichletSum G f = 0)
      ∧ (0 < volume G →
          energy G f = Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) f f / (2 * volume G))
      ∧ (volume G = 0 →
          energy G f = 0 ∧ Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) f f = 0) := by
  intro V _ _ _ G _ f
  refine ⟨energy_nonneg G f, ?_, fun x y h => edge_measure_pos_of_adj G h, ?_,
    fun hv => energy_eq_lapQuadratic_div G hv f, ?_⟩
  · by_cases hv : volume G = 0
    · have hedges : ∀ x y : V, G.Adj x y → f x = f y := by
        intro x y h
        exact absurd h (not_adj_of_degree_eq_zero G
          (degree_eq_zero_of_volume_eq_zero G hv x) y)
      rw [energy_eq_zero_of_volume_eq_zero G f hv]
      exact ⟨fun _ => hedges, fun _ => rfl⟩
    · have hvpos : 0 < volume G := lt_of_le_of_ne (volume_nonneg G) (Ne.symm hv)
      have hvol : (2 : ℝ) * volume G ≠ 0 := by
        have h : (0 : ℝ) < 2 * volume G := by linarith
        exact ne_of_gt h
      rw [energy_eq_lapQuadratic_div G hvpos f]
      constructor
      · intro h
        rcases div_eq_zero_iff.1 h with h' | h'
        · exact (SimpleGraph.lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj ℝ G f).1 h'
        · exact absurd h' hvol
      · intro h
        rw [(SimpleGraph.lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_adj ℝ G f).2 h,
          zero_div]
  · rw [Qatlib.Concepts.DirichletForm.EnergyIdentity.g1 V G f]
    constructor
    · intro h
      rcases mul_eq_zero.1 h with h' | h'
      · norm_num at h'
      · exact h'
    · intro h
      show (1 / 2 : ℝ) * dirichletSum G f = 0
      rw [h]
      norm_num
  · intro hv
    exact ⟨energy_eq_zero_of_volume_eq_zero G f hv,
      lapQuadratic_eq_zero_of_volume_eq_zero G f hv⟩

end Qatlib.Concepts.GraphEnergy.ZeroEnergy
