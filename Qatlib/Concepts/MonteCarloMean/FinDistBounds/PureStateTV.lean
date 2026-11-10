/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Concepts.MonteCarloMean.FinDistBounds

open scoped BigOperators

private theorem born_tv_le_sqrt_inner {I : Type} [Fintype I] [DecidableEq I]
    (ψ φ : QState I) (hψ : Normalized ψ) (hφ : Normalized φ) :
    (1 / 2 : ℝ) * ∑ i, |BornProb ψ i - BornProb φ i| ≤
      Real.sqrt (1 - ‖Inner ψ φ‖ ^ 2) := by
  let r := fun i : I => ‖ψ i‖
  let s := fun i : I => ‖φ i‖
  let B := ∑ i, r i * s i
  let L := ∑ i, |r i ^ 2 - s i ^ 2|
  have hr : ∑ i, r i ^ 2 = 1 := hψ
  have hs : ∑ i, s i ^ 2 = 1 := hφ
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hF : ‖Inner ψ φ‖ ≤ B := by
    rw [inner_apply]
    calc
      _ ≤ ∑ i, ‖(starRingEnd ℂ) (ψ i) * φ i‖ := norm_sum_le _ _
      _ = B := by simp [B, r, s]
  have hm : ∑ i, (r i - s i) ^ 2 = 2 - 2 * B := by
    have he : ∑ i, (r i - s i) ^ 2 = ∑ i, (r i ^ 2 + s i ^ 2 - 2 * (r i * s i)) :=
      Finset.sum_congr rfl (fun i _ => by ring)
    rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hr, hs]
    ring
  have hp : ∑ i, (r i + s i) ^ 2 = 2 + 2 * B := by
    have he : ∑ i, (r i + s i) ^ 2 = ∑ i, (r i ^ 2 + s i ^ 2 + 2 * (r i * s i)) :=
      Finset.sum_congr rfl (fun i _ => by ring)
    rw [he, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hr, hs]
    ring
  have hL : ∑ i, |r i - s i| * (r i + s i) = L := by
    apply Finset.sum_congr rfl
    intro i _
    rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => |r i - s i|) (fun i => r i + s i)
  simp only [sq_abs, hL, hm, hp] at hcs
  have hsq : ((1 / 2 : ℝ) * L) ^ 2 ≤ 1 - ‖Inner ψ φ‖ ^ 2 := by
    nlinarith [norm_nonneg (Inner ψ φ)]
  have hnonneg : 0 ≤ 1 - ‖Inner ψ φ‖ ^ 2 := by nlinarith [sq_nonneg ((1 / 2 : ℝ) * L)]
  change (1 / 2 : ℝ) * L ≤ Real.sqrt (1 - ‖Inner ψ φ‖ ^ 2)
  nlinarith [Real.sq_sqrt hnonneg, Real.sqrt_nonneg (1 - ‖Inner ψ φ‖ ^ 2)]

theorem pureState_born_tv_le_sqrt_fidelity {I : Type} [Fintype I] [DecidableEq I]
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (ψ φ : QState I) (hψ : Normalized ψ) (hφ : Normalized φ) :
    (1 / 2 : ℝ) * ∑ z : I, |BornProb (ApplyGate U ψ) z - BornProb (ApplyGate U φ) z| ≤
      Real.sqrt (1 - ‖Inner ψ φ‖ ^ 2) := by
  have h := born_tv_le_sqrt_inner (ApplyGate U ψ) (ApplyGate U φ)
    (normalized_applyGate hU hψ) (normalized_applyGate hU hφ)
  simpa only [inner_applyGate hU] using h

end Qatlib.Concepts.MonteCarloMean.FinDistBounds
