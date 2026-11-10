/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NativeNumerics.LayeredMean.NativeLayeredMean
import Qatlib.Concepts.ProbabilityCore.Concentration.WeightedHashData
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.ProbabilityCore.Concentration
open Qatlib.Concepts.NativeNumerics.LayeredMean

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open scoped BigOperators
set_option warningAsError false

private theorem conditional_average_mono
    {H : Type} [Fintype H] (f g : H → ℝ) (hfg : ∀ h, f h ≤ g h) :
    finiteHashAverage f ≤ finiteHashAverage g := by
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s := (Finset.univ : Finset H)) (fun h _ => hfg h))
    (inv_nonneg.mpr (Nat.cast_nonneg _))

private theorem conditional_average_scale
    {H : Type} [Fintype H] (c : ℝ) (f : H → ℝ) :
    finiteHashAverage (fun h => c * f h) = c * finiteHashAverage f := by
  unfold finiteHashAverage
  rw [← Finset.mul_sum]
  ring

private theorem conditional_average_abs
    {H : Type} [Fintype H] (f : H → ℝ) :
    |finiteHashAverage f| ≤ finiteHashAverage (fun h => |f h|) := by
  unfold finiteHashAverage
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

private theorem conditional_product_l1
    {X : Type} [Fintype X] [DecidableEq X] (p q : FinDist X) (R : ℕ) :
    (∑ ω : Fin R → X, |p.probOf ω - q.probOf ω|) ≤
      (R : ℝ) * ∑ x : X, |p.prob x - q.prob x| := by
  have hh := native_product_l1 R (fun _ => p) (fun _ => q)
  simpa only [Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probOf, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] using! hh

private theorem conditional_product_observation_l1
    {X : Type} [Fintype X] [DecidableEq X] (p q : FinDist X) (R : ℕ)
    (w : (Fin R → X) → ℝ)
    (hw₀ : ∀ ω, 0 ≤ w ω) (hw₁ : ∀ ω, w ω ≤ 1) :
    |(∑ ω : Fin R → X, p.probOf ω * w ω) -
      (∑ ω : Fin R → X, q.probOf ω * w ω)| ≤
      (1 / 2 : ℝ) * ∑ ω : Fin R → X, |p.probOf ω - q.probOf ω| := by
  have hzero : (∑ ω : Fin R → X, (p.probOf ω - q.probOf ω)) = 0 := by
    rw [Finset.sum_sub_distrib, p.sum_probOf R, q.sum_probOf R, sub_self]
  have hterm (ω : Fin R → X) :
      (p.probOf ω - q.probOf ω) * (w ω - 1 / 2) =
        p.probOf ω * w ω - q.probOf ω * w ω -
          (1 / 2) * (p.probOf ω - q.probOf ω) := by ring
  have hcenter : (∑ ω : Fin R → X,
      (p.probOf ω - q.probOf ω) * (w ω - 1 / 2)) =
      (∑ ω : Fin R → X, p.probOf ω * w ω) -
        (∑ ω : Fin R → X, q.probOf ω * w ω) := by
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hzero, mul_zero, sub_zero]
  calc
    _ = |∑ ω : Fin R → X,
        (p.probOf ω - q.probOf ω) * (w ω - 1 / 2)| := congrArg abs hcenter.symm
    _ ≤ ∑ ω : Fin R → X,
        |(p.probOf ω - q.probOf ω) * (w ω - 1 / 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ω : Fin R → X, (1 / 2 : ℝ) * |p.probOf ω - q.probOf ω| := by
      apply Finset.sum_le_sum
      intro ω _
      rw [abs_mul]
      have hc : |w ω - (1 / 2 : ℝ)| ≤ 1 / 2 := by
        apply abs_le.mpr
        constructor
        · linarith [hw₀ ω]
        · linarith [hw₁ ω]
      calc
        _ ≤ |p.probOf ω - q.probOf ω| * (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left hc (abs_nonneg _)
        _ = _ := mul_comm _ _
    _ = _ := by rw [Finset.mul_sum]

theorem conditional_product_record_transport
    (H X : Type) [Fintype H] [Fintype X] [DecidableEq X]
    (p q : H → FinDist X) (R : ℕ) :
    finiteHashAverage (fun h : H =>
      ∑ ω : Fin R → X, |(p h).probOf ω - (q h).probOf ω|) ≤
      (R : ℝ) * finiteHashAverage (fun h : H =>
        ∑ x : X, |(p h).prob x - (q h).prob x|) ∧
    ∀ w : H → (Fin R → X) → ℝ,
      (∀ h ω, 0 ≤ w h ω) → (∀ h ω, w h ω ≤ 1) →
      |finiteHashAverage (fun h : H =>
          ∑ ω : Fin R → X, (p h).probOf ω * w h ω) -
        finiteHashAverage (fun h : H =>
          ∑ ω : Fin R → X, (q h).probOf ω * w h ω)| ≤
        ((R : ℝ) / 2) * finiteHashAverage (fun h : H =>
          ∑ x : X, |(p h).prob x - (q h).prob x|) := by
  have hproduct : finiteHashAverage (fun h : H =>
      ∑ ω : Fin R → X, |(p h).probOf ω - (q h).probOf ω|) ≤
      (R : ℝ) * finiteHashAverage (fun h : H =>
        ∑ x : X, |(p h).prob x - (q h).prob x|) := by
    calc
      _ ≤ finiteHashAverage (fun h : H =>
          (R : ℝ) * ∑ x : X, |(p h).prob x - (q h).prob x|) :=
        conditional_average_mono _ _ (fun h => conditional_product_l1 (p h) (q h) R)
      _ = _ := conditional_average_scale _ _
  refine ⟨hproduct, ?_⟩
  intro w hw₀ hw₁
  have hsub : finiteHashAverage (fun h : H =>
      ∑ ω : Fin R → X, (p h).probOf ω * w h ω) -
      finiteHashAverage (fun h : H =>
        ∑ ω : Fin R → X, (q h).probOf ω * w h ω) =
      finiteHashAverage (fun h : H =>
        (∑ ω : Fin R → X, (p h).probOf ω * w h ω) -
          (∑ ω : Fin R → X, (q h).probOf ω * w h ω)) := by
    simp only [finiteHashAverage, Finset.sum_sub_distrib, mul_sub]
  calc
    _ = |finiteHashAverage (fun h : H =>
        (∑ ω : Fin R → X, (p h).probOf ω * w h ω) -
          (∑ ω : Fin R → X, (q h).probOf ω * w h ω))| := congrArg abs hsub
    _ ≤ finiteHashAverage (fun h : H =>
        |(∑ ω : Fin R → X, (p h).probOf ω * w h ω) -
          (∑ ω : Fin R → X, (q h).probOf ω * w h ω)|) := conditional_average_abs _
    _ ≤ finiteHashAverage (fun h : H => (1 / 2 : ℝ) *
        ∑ ω : Fin R → X, |(p h).probOf ω - (q h).probOf ω|) :=
      conditional_average_mono _ _ (fun h => conditional_product_observation_l1
        (p h) (q h) R (w h) (hw₀ h) (hw₁ h))
    _ = (1 / 2 : ℝ) * finiteHashAverage (fun h : H =>
        ∑ ω : Fin R → X, |(p h).probOf ω - (q h).probOf ω|) :=
      conditional_average_scale _ _
    _ ≤ (1 / 2 : ℝ) * ((R : ℝ) * finiteHashAverage (fun h : H =>
        ∑ x : X, |(p h).prob x - (q h).prob x|)) :=
      mul_le_mul_of_nonneg_left hproduct (by norm_num)
    _ = _ := by ring

end Qatlib.Concepts.AdversaryBounds.AdvDuality
