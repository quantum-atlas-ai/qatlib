/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.SampledAttemptSuccessStat
import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.AttemptAuxiliary
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.PeriodSampling.OrderRecovery

set_option autoImplicit false

noncomputable section
namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm
open Qatlib
open scoped Classical

private theorem attempt_single_mass (N M k : ℕ) [NeZero N] (hM : 0 < M)
    (hk : Fintype.card (ZMod N)ˣ ≤ 2 ^ k) :
    (attemptLaw N M k hM hk).probEvent (L := 1)
        (fun ω => attemptSuccess N M k (ω 0)) =
      (2 ^ k : ℝ)⁻¹ * ∑ a : (ZMod N)ˣ,
        ∑ yz ∈ Finset.univ.filter (fun yz : Fin M × Fin M =>
          (attemptFactor N M a yz).isSome),
          (modularOrderLaw N M a hM).prob yz.1 *
            (modularOrderLaw N M a hM).prob yz.2 := by
  rw [singleEvent_mass, Finset.sum_filter, Fintype.sum_sum_type]
  simp only [attemptSuccess, ↓reduceIte, Finset.sum_const_zero, zero_add]
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun yz _ => ?_
  rcases yz with ⟨y, z⟩
  by_cases h : (attemptFactor N M a (y, z)).isSome
  · simp [h, attemptLaw, attemptMass]
  · simp [h]

theorem sampledAttemptSuccess : SampledAttemptSuccess := by
  intro N M k _ hM hk hN hodd hs hsize
  refine ⟨?_, attemptFactor_sound N M⟩
  rw [attempt_single_mass]
  let C : ℝ := (8 / Real.pi ^ 2) ^ 2 / 4
  let mass := fun a : (ZMod N)ˣ =>
    ∑ yz ∈ Finset.univ.filter (fun yz : Fin M × Fin M =>
      (attemptFactor N M a yz).isSome),
      (modularOrderLaw N M a hM).prob yz.1 *
        (modularOrderLaw N M a hM).prob yz.2
  have hnonneg : ∀ a, 0 ≤ mass a := fun a =>
    Finset.sum_nonneg fun yz _ => mul_nonneg
      ((modularOrderLaw N M a hM).nonneg yz.1)
      ((modularOrderLaw N M a hM).nonneg yz.2)
  have hgood : ∀ a, randomBaseGood N a → C ≤ mass a := by
    intro a ha
    have heven := ((random_base_exact_order_factor_characterization N a
      (by omega) hodd).mp ha).1
    have hrpos := orderOf_pos a
    have hr : 1 < orderOf a := by
      obtain ⟨j, hj⟩ := heven
      omega
    have hcf := (continued_fraction_actual_fresh_order_probability_and_factor_soundness
      N M a hM (by omega) hr hsize).1
    refine hcf.trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
    · intro yz hyz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hyz ⊢
      simpa [attemptFactor, hyz, randomBaseGood] using! ha
    · intro yz _ _
      exact mul_nonneg ((modularOrderLaw N M a hM).nonneg yz.1)
        ((modularOrderLaw N M a hM).nonneg yz.2)
  have hsum : ((Finset.univ.filter (randomBaseGood N)).card : ℝ) * C ≤
      ∑ a : (ZMod N)ˣ, mass a := by
    calc
      _ = ∑ a ∈ Finset.univ.filter (randomBaseGood N), C := by simp
      _ ≤ ∑ a ∈ Finset.univ.filter (randomBaseGood N), mass a :=
        Finset.sum_le_sum fun a ha => hgood a (Finset.mem_filter.mp ha).2
      _ ≤ ∑ a : (ZMod N)ˣ, mass a :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun a _ _ => hnonneg a)
  have hcrt := random_base_crt_success_bound N (by omega) hodd hs
  have hcard : (Fintype.card (ZMod N)ˣ : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcount : (Fintype.card (ZMod N)ˣ : ℝ) *
        (1 - (2 : ℝ) ^ (-(N.primeFactors.card - 1 : ℤ))) ≤
      ((Finset.univ.filter (randomBaseGood N)).card : ℝ) := by
    unfold randomBaseSuccess at hcrt
    have hm := mul_le_mul_of_nonneg_left hcrt
      (Nat.cast_nonneg (Fintype.card (ZMod N)ˣ) : (0 : ℝ) ≤ _)
    simpa [← mul_assoc, hcard] using! hm
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hi : 0 ≤ (2 ^ k : ℝ)⁻¹ := by positivity
  change shorAttemptBound N k ≤ (2 ^ k : ℝ)⁻¹ * ∑ a, mass a
  calc
    shorAttemptBound N k = (2 ^ k : ℝ)⁻¹ *
        ((Fintype.card (ZMod N)ˣ : ℝ) *
          (1 - (2 : ℝ) ^ (-(N.primeFactors.card - 1 : ℤ))) * C) := by
      dsimp [shorAttemptBound, C]
      ring
    _ ≤ (2 ^ k : ℝ)⁻¹ *
        (((Finset.univ.filter (randomBaseGood N)).card : ℝ) * C) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcount hC) hi
    _ ≤ (2 ^ k : ℝ)⁻¹ * ∑ a, mass a :=
      mul_le_mul_of_nonneg_left hsum hi

end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
