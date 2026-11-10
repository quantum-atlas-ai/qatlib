/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false

namespace Qatlib.Papers.HiddenNonlin07.MainResults.LevelSetOverlap

open scoped BigOperators
open Finset

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

def levelSet (f : X → Y) (y : Y) : Finset X := univ.filter fun x => f x = y

theorem mem_levelSet {f : X → Y} {y : Y} {x : X} : x ∈ levelSet f y ↔ f x = y := by
  simp [levelSet]

theorem levelSet_disjoint {f : X → Y} {y y' : Y} (h : y ≠ y') :
    Disjoint (levelSet f y) (levelSet f y') := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  ext x
  simp only [levelSet, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.notMem_empty, iff_false]
  rintro ⟨hx, hx'⟩
  exact h (hx.symm.trans hx')

theorem card_eq_sum_levelSet (f : X → Y) :
    (∑ y, (levelSet f y).card) = Fintype.card X := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset X))
    (t := (univ : Finset Y)) (f := f) (fun x _ => Finset.mem_univ (f x))
  simpa [levelSet, Finset.card_univ] using h.symm

def overlap (f f' : X → Y) (y y' : Y) : ℕ := ((levelSet f y) ∩ (levelSet f' y')).card

theorem sum_overlap_eq_card_levelSet (f f' : X → Y) (y : Y) :
    (∑ y', overlap f f' y y') = (levelSet f y).card := by
  have h := Finset.card_eq_sum_card_fiberwise (s := levelSet f y) (t := (univ : Finset Y))
    (f := f') (fun x _ => Finset.mem_univ (f' x))
  have hfilter (y' : Y) :
      (levelSet f y).filter (fun x => f' x = y') = levelSet f y ∩ levelSet f' y' := by
    ext x
    simp [levelSet, Finset.mem_filter]
  calc
    (∑ y', overlap f f' y y') = ∑ y' ∈ (univ : Finset Y),
        ((levelSet f y).filter fun x => f' x = y').card := by
      simp only [overlap, hfilter]
    _ = (levelSet f y).card := h.symm

noncomputable def levelKet (f : X → Y) (y : Y) : X → ℂ :=
  fun x => if f x = y then ((Real.sqrt ((levelSet f y).card : ℝ)) : ℂ)⁻¹ else 0

theorem levelKet_inner (f f' : X → Y) (y y' : Y) :
    (∑ x, star (levelKet f y x) * levelKet f' y' x) =
      (((overlap f f' y y' : ℝ) /
        (Real.sqrt ((levelSet f y).card : ℝ) *
          Real.sqrt ((levelSet f' y').card : ℝ))) : ℂ) := by
  classical
  have hterm (x : X) : star (levelKet f y x) * levelKet f' y' x =
      (((if f x = y ∧ f' x = y' then
          (Real.sqrt ((levelSet f y).card : ℝ))⁻¹ *
            (Real.sqrt ((levelSet f' y').card : ℝ))⁻¹ else 0) : ℝ) : ℂ) := by
    by_cases h1 : f x = y <;> by_cases h2 : f' x = y' <;>
      simp [levelKet, h1, h2]
  have hset : (univ.filter fun x => f x = y ∧ f' x = y') = levelSet f y ∩ levelSet f' y' := by
    ext x
    simp only [levelSet, Finset.mem_filter, Finset.mem_inter, Finset.mem_univ, true_and]
  have hval :
      (∑ x, (if f x = y ∧ f' x = y' then
          (Real.sqrt ((levelSet f y).card : ℝ))⁻¹ *
            (Real.sqrt ((levelSet f' y').card : ℝ))⁻¹ else (0 : ℝ))) =
        (overlap f f' y y' : ℝ) *
          ((Real.sqrt ((levelSet f y).card : ℝ))⁻¹ *
            (Real.sqrt ((levelSet f' y').card : ℝ))⁻¹) := by
    rw [← Finset.sum_filter, hset, Finset.sum_const, nsmul_eq_mul, overlap]
  simp_rw [hterm]
  rw [← Complex.ofReal_sum, hval]
  push_cast
  rw [div_eq_mul_inv, mul_inv]

theorem pair_sq_sum_le_card (κ : Y → Y → ℝ) (α β δ : ℝ)
    (hκ0 : ∀ y y', 0 ≤ κ y y') (hδ : ∀ y y', κ y y' ≤ δ)
    (hα : 0 ≤ α) (_hβ : 0 ≤ β)
    (hcount : (∑ y, ∑ y', if α ≤ κ y y' then (1 : ℝ) else 0) ≤
      β * (Fintype.card Y : ℝ) ^ 2) :
    (∑ y, ∑ y', κ y y' ^ 2) ≤ (α ^ 2 + β * δ ^ 2) * (Fintype.card Y : ℝ) ^ 2 := by
  have hpt : ∀ y y', κ y y' ^ 2 ≤ α ^ 2 + (if α ≤ κ y y' then δ ^ 2 else 0) := by
    intro y y'
    by_cases h : α ≤ κ y y'
    · rw [if_pos h]
      have h1 : κ y y' ^ 2 ≤ δ ^ 2 := by nlinarith [hκ0 y y', hδ y y']
      linarith [sq_nonneg α]
    · rw [if_neg h]
      have h1 : κ y y' ≤ α := le_of_not_ge h
      have h2 : κ y y' ^ 2 ≤ α ^ 2 := by nlinarith [hκ0 y y', hα]
      linarith
  have hconst : (∑ y : Y, ∑ y' : Y, α ^ 2) = (Fintype.card Y : ℝ) ^ 2 * α ^ 2 := by
    have h1 : (∑ _y' : Y, α ^ 2) = (Fintype.card Y : ℝ) * α ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.sum_congr rfl fun y _ => h1, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    ring
  have hind : (∑ y : Y, ∑ y' : Y, (if α ≤ κ y y' then δ ^ 2 else 0)) =
      δ ^ 2 * ∑ y : Y, ∑ y' : Y, (if α ≤ κ y y' then (1 : ℝ) else 0) := by
    have hpt (y y' : Y) : (if α ≤ κ y y' then δ ^ 2 else 0) =
        δ ^ 2 * (if α ≤ κ y y' then (1 : ℝ) else 0) := by
      by_cases h : α ≤ κ y y'
      · rw [if_pos h, if_pos h, mul_one]
      · rw [if_neg h, if_neg h, mul_zero]
    simp_rw [hpt]
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
  have hsum : (∑ y : Y, ∑ y' : Y, (α ^ 2 + (if α ≤ κ y y' then δ ^ 2 else 0))) =
      (Fintype.card Y : ℝ) ^ 2 * α ^ 2 +
        δ ^ 2 * ∑ y : Y, ∑ y' : Y, (if α ≤ κ y y' then (1 : ℝ) else 0) := by
    rw [← hconst, ← hind, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_add_distrib]
  calc
    (∑ y : Y, ∑ y' : Y, κ y y' ^ 2)
        ≤ ∑ y : Y, ∑ y' : Y, (α ^ 2 + (if α ≤ κ y y' then δ ^ 2 else 0)) :=
          Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun y' _ => hpt y y'
    _ = (Fintype.card Y : ℝ) ^ 2 * α ^ 2 +
          δ ^ 2 * ∑ y : Y, ∑ y' : Y, (if α ≤ κ y y' then (1 : ℝ) else 0) := hsum
    _ ≤ (α ^ 2 + β * δ ^ 2) * (Fintype.card Y : ℝ) ^ 2 := by
          have h1 : δ ^ 2 * (∑ y : Y, ∑ y' : Y, (if α ≤ κ y y' then (1 : ℝ) else 0)) ≤
              δ ^ 2 * (β * (Fintype.card Y : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hcount (by positivity)
          nlinarith [h1]

theorem pair_sq_div_sum_le (κ : Y → Y → ℝ) (sz : Y → ℕ) (α β δ : ℝ)
    (hκ0 : ∀ y y', 0 ≤ κ y y') (hrow : ∀ y, ∑ y', κ y y' = (sz y : ℝ))
    (hδ : ∀ y, (sz y : ℝ) ≤ δ) (hδ0 : 0 ≤ δ) (hα : 0 ≤ α) (_hβ : 0 ≤ β)
    (hbad : (∑ y, if ∃ y', α ≤ κ y y' then (1 : ℝ) else 0) ≤
      β * (Fintype.card Y : ℝ)) :
    (∑ y, (∑ y', κ y y' ^ 2) / (sz y : ℝ)) ≤
      α * (Fintype.card Y : ℝ) + β * δ * (Fintype.card Y : ℝ) := by
  classical
  have hgood : ∀ y, (¬ ∃ y', α ≤ κ y y') → (∑ y', κ y y' ^ 2) / (sz y : ℝ) ≤ α := by
    intro y hy
    have hlt : ∀ y', ¬ (α ≤ κ y y') := by
      intro y' hy'
      exact hy ⟨y', hy'⟩
    have hle : ∀ y', κ y y' ^ 2 ≤ α * κ y y' := by
      intro y'
      have h1 : κ y y' ≤ α := le_of_not_ge (hlt y')
      nlinarith [hκ0 y y', hα]
    have hsumle : (∑ y', κ y y' ^ 2) ≤ α * (sz y : ℝ) := by
      calc
        (∑ y', κ y y' ^ 2) ≤ ∑ y', α * κ y y' := Finset.sum_le_sum fun y' _ => hle y'
        _ = α * (sz y : ℝ) := by rw [← Finset.mul_sum, hrow y]
    by_cases hz : (sz y : ℝ) = 0
    · have hz0 : (∑ y', κ y y' ^ 2) ≤ 0 := by
        simpa [hrow y, hz] using hsumle
      have hzero : (∑ y', κ y y' ^ 2) = 0 :=
        le_antisymm hz0 (Finset.sum_nonneg fun y' _ => by
          have := hκ0 y y'; positivity)
      rw [hzero, hz, div_zero]
      exact hα
    · have hpos : (0 : ℝ) < (sz y : ℝ) := lt_of_le_of_ne (by positivity) (Ne.symm hz)
      rw [div_le_iff₀ hpos]
      exact hsumle
  have hbadrow : ∀ y, (∃ y', α ≤ κ y y') → (∑ y', κ y y' ^ 2) / (sz y : ℝ) ≤ δ := by
    intro y _
    have hsumle : (∑ y', κ y y' ^ 2) ≤ (sz y : ℝ) ^ 2 := by
      have hnn : (∑ y' : Y, κ y y' ^ 2) ≤ (∑ y' : Y, κ y y') ^ 2 := by
        simp only [pow_two]
        rw [Finset.sum_mul_sum]
        refine Finset.sum_le_sum fun y' _ => ?_
        exact Finset.single_le_sum (f := fun j : Y => κ y y' * κ y j)
          (fun j _ => mul_nonneg (hκ0 y y') (hκ0 y j)) (Finset.mem_univ y')
      rw [hrow y] at hnn
      exact hnn
    by_cases hz : (sz y : ℝ) = 0
    · rw [hz, div_zero]; exact hδ0
    · have hpos : (0 : ℝ) < (sz y : ℝ) := lt_of_le_of_ne (by positivity) (Ne.symm hz)
      rw [div_le_iff₀ hpos]
      calc
        (∑ y', κ y y' ^ 2) ≤ (sz y : ℝ) ^ 2 := hsumle
        _ = (sz y : ℝ) * (sz y : ℝ) := sq (sz y : ℝ)
        _ ≤ (sz y : ℝ) * δ := mul_le_mul_of_nonneg_left (hδ y) (le_of_lt hpos)
        _ = δ * (sz y : ℝ) := mul_comm _ _
  have hsplit : (∑ y, (∑ y', κ y y' ^ 2) / (sz y : ℝ)) =
      (∑ y, if ∃ y', α ≤ κ y y' then (∑ y', κ y y' ^ 2) / (sz y : ℝ) else 0) +
        (∑ y, if ∃ y', α ≤ κ y y' then 0 else (∑ y', κ y y' ^ 2) / (sz y : ℝ)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases h : ∃ y', α ≤ κ y y' <;> simp [h]
  have hgoodsum : (∑ y, if ∃ y', α ≤ κ y y' then 0 else (∑ y', κ y y' ^ 2) / (sz y : ℝ)) ≤
      α * (Fintype.card Y : ℝ) := by
    calc
      (∑ y, if ∃ y', α ≤ κ y y' then 0 else (∑ y', κ y y' ^ 2) / (sz y : ℝ)) ≤
          ∑ y, if ∃ y', α ≤ κ y y' then 0 else α := by
        refine Finset.sum_le_sum fun y _ => ?_
        by_cases h : ∃ y', α ≤ κ y y'
        · simp [h]
        · simp only [h, if_false]
          exact hgood y h
      _ ≤ ∑ _y : Y, α := by
        refine Finset.sum_le_sum fun y _ => ?_
        by_cases h : ∃ y', α ≤ κ y y' <;> simp [h, hα]
      _ = α * (Fintype.card Y : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]; ring
  have hbadsum : (∑ y, if ∃ y', α ≤ κ y y' then (∑ y', κ y y' ^ 2) / (sz y : ℝ) else 0) ≤
      β * δ * (Fintype.card Y : ℝ) := by
    calc
      (∑ y, if ∃ y', α ≤ κ y y' then (∑ y', κ y y' ^ 2) / (sz y : ℝ) else 0) ≤
          ∑ y, if ∃ y', α ≤ κ y y' then δ else 0 := by
        refine Finset.sum_le_sum fun y _ => ?_
        by_cases h : ∃ y', α ≤ κ y y'
        · simp only [h, if_true]
          exact hbadrow y h
        · simp [h]
      _ = δ * ∑ y, if ∃ y', α ≤ κ y y' then (1 : ℝ) else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        by_cases h : ∃ y', α ≤ κ y y' <;> simp [h]
      _ ≤ δ * (β * (Fintype.card Y : ℝ)) := mul_le_mul_of_nonneg_left hbad hδ0
      _ = β * δ * (Fintype.card Y : ℝ) := by ring
  rw [hsplit]
  linarith [hgoodsum, hbadsum]

end Qatlib.Papers.HiddenNonlin07.MainResults.LevelSetOverlap
