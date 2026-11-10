/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GraphStationary.StationaryLaw
set_option warningAsError false
open Qatlib.Concepts.GraphStationary.StationaryLaw

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.DirichletForm.EnergyIdentity
open Qatlib.Concepts.GraphEnergy.ZeroEnergy Qatlib.Concepts.GraphStationary.StationaryLaw
open Finset
open scoped BigOperators

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Nonempty V] in

lemma sum_stationary_sq (f : V → ℝ) :
    ∑ x, ∑ y, stationary G x * kernel G x y * (f x)^2 = ∑ x, stationary G x * (f x)^2 := by
  refine Finset.sum_congr rfl fun x _ => ?_
  have hcomm : ∀ y, stationary G x * kernel G x y * (f x)^2 =
      (stationary G x * (f x)^2) * kernel G x y := by
    intro y; ring
  simp_rw [hcomm, ← Finset.mul_sum, kernel_sum, mul_one]

lemma sum_shift_sq (f : V → ℝ) :
    ∑ x, ∑ y, stationary G x * kernel G x y * (f y)^2 = ∑ y, stationary G y * (f y)^2 := by
  have hswap : ∀ x y, stationary G x * kernel G x y * (f y)^2 =
      stationary G y * kernel G y x * (f y)^2 := by
    intro x y
    rw [detailed_balance G x y]
  have h1 : ∑ x, ∑ y, stationary G x * kernel G x y * (f y)^2 =
      ∑ x, ∑ y, stationary G y * kernel G y x * (f y)^2 := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hswap x y
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  have hcomm : ∀ x, stationary G y * kernel G y x * (f y)^2 =
      (stationary G y * (f y)^2) * kernel G y x := by
    intro x; ring
  simp_rw [hcomm, ← Finset.mul_sum, kernel_sum, mul_one]

omit [Nonempty V] in

lemma sum_cross (f : V → ℝ) :
    ∑ x, ∑ y, stationary G x * kernel G x y * (f x * f y) =
      ∑ x, stationary G x * f x * ∑ y, kernel G x y * f y := by
  refine Finset.sum_congr rfl fun x _ => ?_
  have hcomm : ∀ y, stationary G x * kernel G x y * (f x * f y) =
      (stationary G x * f x) * (kernel G x y * f y) := by
    intro y; ring
  simp_rw [hcomm, ← Finset.mul_sum]

omit [Nonempty V] in

lemma energy_expand (f : V → ℝ) :
    energy G f = ∑ x, stationary G x * (f x)^2 -
      ∑ x, stationary G x * f x * ∑ y, kernel G x y * f y := by
  unfold energy
  have hsub : ∀ x, stationary G x * f x * (f x - ∑ y, kernel G x y * f y) =
      stationary G x * (f x)^2 - stationary G x * f x * ∑ y, kernel G x y * f y := by
    intro x; ring
  simp_rw [hsub, Finset.sum_sub_distrib]

theorem g1 :
    ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ),
      energy G f = (1/2 : ℝ) * ∑ x, ∑ y,
        stationary G x * kernel G x y * (f x - f y)^2 := by
  intro V _ _ _ G _ f
  have hsq : ∀ x y, (f x - f y)^2 = (f x)^2 + (f y)^2 - 2 * (f x * f y) := by
    intro x y; ring
  have hlin : ∀ x y, stationary G x * kernel G x y * ((f x)^2 + (f y)^2 - 2 * (f x * f y)) =
      stationary G x * kernel G x y * (f x)^2 +
        stationary G x * kernel G x y * (f y)^2 -
        2 * (stationary G x * kernel G x y * (f x * f y)) := by
    intro x y; ring
  have hsplit : ∑ x, ∑ y, stationary G x * kernel G x y * (f x - f y)^2 =
      ∑ x, stationary G x * (f x)^2 + ∑ y, stationary G y * (f y)^2 -
        2 * ∑ x, stationary G x * f x * ∑ y, kernel G x y * f y := by
    simp_rw [hsq, hlin, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [sum_stationary_sq G f, sum_shift_sq G f]
    have htwo : ∑ x, ∑ y, 2 * (stationary G x * kernel G x y * (f x * f y)) =
        2 * ∑ x, stationary G x * f x * ∑ y, kernel G x y * f y := by
      have hinner : ∀ x, ∑ y, 2 * (stationary G x * kernel G x y * (f x * f y)) =
          2 * ∑ y, stationary G x * kernel G x y * (f x * f y) := by
        intro x
        symm
        simpa using
          (Finset.mul_sum (s := Finset.univ) (a := (2 : ℝ))
            (f := fun y => stationary G x * kernel G x y * (f x * f y)))
      simp_rw [hinner]
      rw [← Finset.mul_sum, sum_cross]
    rw [htwo]
  rw [energy_expand G f, hsplit]
  ring

end Qatlib.Concepts.DirichletForm.EnergyIdentity
