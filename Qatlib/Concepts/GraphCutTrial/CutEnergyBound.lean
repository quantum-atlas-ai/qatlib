/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DirichletForm.EnergyIdentity

/-!
# Cut indicators and graph energy

This module computes the mean, variance, and energy of `centeredIndicator` for the lazy graph
kernel. The energy is the cut flow, yielding a Rayleigh quotient bound when the cut has positive
stationary mass at most one half. These are classical Markov-chain ingredients for the
quantum-walk setting of [Szegedy2004].

## Main statements

* `variance_mass`: the centered cut indicator has variance `mass * (1 - mass)`.
* `energy_flow`: its energy equals cut flow.
* `g1`: the combined cut-indicator identities and Rayleigh bound.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option warningAsError false
open Qatlib.Concepts.DirichletForm.EnergyIdentity

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.GraphCutTrial.CutEnergyBound
open Qatlib.Concepts.GraphEnergy.ZeroEnergy
open Qatlib.Concepts.GraphStationary.StationaryLaw
open Qatlib.Concepts.DirichletForm.EnergyIdentity Finset
open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The stationary mass of the complement of `S` is one minus the mass of `S`. -/
lemma mass_compl (S : Finset V) :
    ∑ x ∈ Sᶜ, stationary G x = 1 - mass G S := by
  have hsplit := Finset.sum_add_sum_compl (s := S) (f := stationary G)
  have hall : ∑ x, stationary G x = 1 := stationary_sum G
  have hS : ∑ x ∈ S, stationary G x = mass G S := by unfold mass; rfl
  linarith

omit [Nonempty V] in

/-- The centered indicator is the membership indicator minus the stationary mass of the set. -/
lemma membership_indicator (S : Finset V) (x : V) :
    centeredIndicator G S x = (if x ∈ S then (1 : ℝ) else 0) - mass G S := by
  rfl

/-- The stationary mean of a centered cut indicator is zero. -/
lemma mean_centered (S : Finset V) : mean G (centeredIndicator G S) = 0 := by
  unfold mean
  simp_rw [membership_indicator, mul_sub, Finset.sum_sub_distrib]
  have hind : ∑ x, stationary G x * (if x ∈ S then (1 : ℝ) else 0) = mass G S := by
    rw [← Finset.sum_add_sum_compl (s := S)]
    have hin : ∑ x ∈ S, stationary G x * (if x ∈ S then (1 : ℝ) else 0) = mass G S := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp [hx]
    have hout : ∑ x ∈ Sᶜ, stationary G x * (if x ∈ S then (1 : ℝ) else 0) = 0 := by
      refine Finset.sum_eq_zero fun x hx => ?_
      simp [Finset.mem_compl.mp hx]
    linarith
  have hconst : ∑ x, stationary G x * mass G S = mass G S := by
    simp_rw [mul_comm (stationary G _) (mass G S)]
    rw [← Finset.mul_sum, stationary_sum, mul_one]
  linarith

/-- The variance of a centered cut indicator equals its stationary second moment. -/
lemma variance_sq (S : Finset V) :
    variance G (centeredIndicator G S) =
      ∑ x, stationary G x * (centeredIndicator G S x)^2 := by
  unfold variance
  simp [mean_centered]

/-- The variance of a centered cut indicator is `mass G S * (1 - mass G S)`. -/
lemma variance_mass (S : Finset V) :
    variance G (centeredIndicator G S) = mass G S * (1 - mass G S) := by
  rw [variance_sq]
  simp_rw [membership_indicator]
  have hsq : ∀ x, ((if x ∈ S then (1 : ℝ) else 0) - mass G S)^2 =
      if x ∈ S then (1 - mass G S)^2 else (mass G S)^2 := by
    intro x
    by_cases hx : x ∈ S <;> simp [hx]
  simp_rw [hsq]
  rw [← Finset.sum_add_sum_compl (s := S)]
  have hin : ∑ x ∈ S, stationary G x * (if x ∈ S then (1 - mass G S)^2 else (mass G S)^2) =
      (1 - mass G S)^2 * mass G S := by
    have hsame : ∑ x ∈ S, stationary G x * (if x ∈ S then (1 - mass G S)^2 else (mass G S)^2) =
        ∑ x ∈ S, (1 - mass G S)^2 * stationary G x := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp [hx, mul_comm]
    rw [hsame, ← Finset.mul_sum]
    unfold mass
    ring
  have hout : ∑ x ∈ Sᶜ, stationary G x *
      (if x ∈ S then (1 - mass G S)^2 else (mass G S)^2) =
      (mass G S)^2 * (1 - mass G S) := by
    have hsame : ∑ x ∈ Sᶜ, stationary G x *
        (if x ∈ S then (1 - mass G S)^2 else (mass G S)^2) =
        ∑ x ∈ Sᶜ, (mass G S)^2 * stationary G x := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp [Finset.mem_compl.mp hx, mul_comm]
    rw [hsame, ← Finset.mul_sum, mass_compl]
  linarith

omit [Nonempty V] in

/-- The squared difference of centered indicator values is zero for equal membership in `S` and
one otherwise. -/
lemma diff_sq (S : Finset V) (x y : V) :
    (centeredIndicator G S x - centeredIndicator G S y)^2 =
      if (x ∈ S) = (y ∈ S) then (0 : ℝ) else 1 := by
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
  · simp [membership_indicator, hx, hy]
  · have hne : (x ∈ S) ≠ (y ∈ S) := by simp [hx, hy]
    rw [membership_indicator, membership_indicator, if_neg hne, if_pos hx, if_neg hy]
    ring
  · have hne : (x ∈ S) ≠ (y ∈ S) := by simp [hx, hy]
    rw [membership_indicator, membership_indicator, if_neg hne, if_neg hx, if_pos hy]
    ring
  · simp [membership_indicator, hx, hy]

/-- The total stationary transition weight crossing the cut in either direction equals twice its
outward flow. -/
lemma cut_both (S : Finset V) :
    ∑ x, ∑ y, stationary G x * kernel G x y *
      (if (x ∈ S) = (y ∈ S) then (0 : ℝ) else 1) =
      2 * flow G S := by
  have hsplit : ∑ x, ∑ y, stationary G x * kernel G x y *
      (if (x ∈ S) = (y ∈ S) then (0 : ℝ) else 1) =
      ∑ x ∈ S, ∑ y ∈ Sᶜ, stationary G x * kernel G x y +
        ∑ x ∈ Sᶜ, ∑ y ∈ S, stationary G x * kernel G x y := by
    rw [← Finset.sum_add_sum_compl (s := S)]
    congr 1
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [← Finset.sum_add_sum_compl (s := S)]
      have hin : ∑ y ∈ S, stationary G x * kernel G x y *
          (if (x ∈ S) = (y ∈ S) then (0 : ℝ) else 1) = 0 := by
        refine Finset.sum_eq_zero fun y hy => ?_
        simp [hx, hy]
      have hout : ∑ y ∈ Sᶜ, stationary G x * kernel G x y *
          (if (x ∈ S) = (y ∈ S) then (0 : ℝ) else 1) =
          ∑ y ∈ Sᶜ, stationary G x * kernel G x y := by
        refine Finset.sum_congr rfl fun y hy => ?_
        have hyn : y ∉ S := Finset.mem_compl.mp hy
        simp [hx, hyn]
      linarith
    · refine Finset.sum_congr rfl fun x hx => ?_
      have hxn : x ∉ S := Finset.mem_compl.mp hx
      rw [← Finset.sum_add_sum_compl (s := S)]
      have hin : ∑ y ∈ S, stationary G x * kernel G x y *
          (if (x ∈ S) = (y ∈ S) then (0 : ℝ) else 1) =
          ∑ y ∈ S, stationary G x * kernel G x y := by
        refine Finset.sum_congr rfl fun y hy => ?_
        simp [hxn, hy]
      have hout : ∑ y ∈ Sᶜ, stationary G x * kernel G x y *
          (if (x ∈ S) = (y ∈ S) then (0 : ℝ) else 1) = 0 := by
        refine Finset.sum_eq_zero fun y hy => ?_
        have hyn : y ∉ S := Finset.mem_compl.mp hy
        simp [hxn, hyn]
      linarith
  have hrev : ∑ x ∈ Sᶜ, ∑ y ∈ S, stationary G x * kernel G x y =
      ∑ x ∈ S, ∑ y ∈ Sᶜ, stationary G x * kernel G x y := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
    exact detailed_balance G x y
  unfold flow
  linarith

/-- The energy of a centered cut indicator equals the outward stationary flow of the cut. -/
lemma energy_flow (S : Finset V) :
    energy G (centeredIndicator G S) = flow G S := by
  have hE := Qatlib.Concepts.DirichletForm.EnergyIdentity.g1 (V := V) G (centeredIndicator G S)
  rw [hE]
  simp_rw [diff_sq]
  linarith [cut_both G S]

/-- The outward stationary flow of any cut is nonnegative. -/
lemma flow_nonneg (S : Finset V) : 0 ≤ flow G S := by
  unfold flow
  refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_
  exact mul_nonneg (stationary_nonneg G x) (kernel_nonneg G x y)

/-- A cut of positive stationary mass at most one half has a centered indicator of positive
variance. -/
lemma variance_pos (S : Finset V) (hm : 0 < mass G S) (hhalf : mass G S ≤ 1/2) :
    0 < variance G (centeredIndicator G S) := by
  rw [variance_mass]
  have hrest : 0 < 1 - mass G S := by linarith
  exact mul_pos hm hrest

/-- For a cut of positive mass at most one half, the centered indicator has energy-to-variance
ratio at most twice the flow divided by the mass. -/
lemma rayleigh (S : Finset V) (hm : 0 < mass G S) (hhalf : mass G S ≤ 1/2) :
    energy G (centeredIndicator G S) / variance G (centeredIndicator G S) ≤
      2 * flow G S / mass G S := by
  rw [energy_flow, variance_mass]
  have hrest : 1 / 2 ≤ 1 - mass G S := by linarith
  have hpos : 0 < 1 - mass G S := by linarith
  have hflow : 0 ≤ flow G S := flow_nonneg G S
  have hdiv : flow G S / (mass G S * (1 - mass G S)) =
      (flow G S / mass G S) * (1 / (1 - mass G S)) := by
    field_simp [hm.ne', hpos.ne']
  rw [hdiv]
  have hinv : 1 / (1 - mass G S) ≤ 2 := by
    rw [div_le_iff₀ hpos]
    linarith
  have hcoef : 0 ≤ flow G S / mass G S := div_nonneg hflow hm.le
  have hmul := mul_le_mul_of_nonneg_left hinv hcoef
  have hreorder : flow G S / mass G S * 2 = 2 * flow G S / mass G S := by ring
  linarith

/-- For a cut of positive stationary mass at most one half, the centered indicator has zero
mean, variance `mass * (1 - mass)`, energy equal to flow, and the stated Rayleigh quotient
bound. -/
theorem g1 :
    ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V),
      0 < mass G S → mass G S ≤ 1/2 →
      mean G (centeredIndicator G S) = 0 ∧
      variance G (centeredIndicator G S) = mass G S * (1 - mass G S) ∧
      energy G (centeredIndicator G S) = flow G S ∧
      0 < variance G (centeredIndicator G S) ∧
      energy G (centeredIndicator G S) / variance G (centeredIndicator G S) ≤
        2 * flow G S / mass G S := by
  intro V _ _ _ G _ S hm hhalf
  exact ⟨mean_centered G S, variance_mass G S, energy_flow G S,
    variance_pos G S hm hhalf, rayleigh G S hm hhalf⟩

end Qatlib.Concepts.GraphCutTrial.CutEnergyBound
