/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SdpMmwSolver.OracleError.ResidualDiagnosticContracts
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sampled oracle bounds on a good event

`not_sdpStep2SampledOracle` refutes the proposed sampled-oracle contract without sample
approximation assumptions. `sdpStep2SampledOracleOnGoodEvent` supplies the width and separation
bounds when empirical cost and expectation are related to their true weighted values.

For the mathematical background, see [BrandaoSvore2017].

## Main statements

* `sdpStep2SampledOracleOnGoodEvent`: Under the stated empirical approximation, acceptance, and
  scale bounds, scaling `q` by κN satisfies `sdpSampledWidthBudget` and
  `sdpSampledSeparationSlack`. See [BrandaoSvore2017].

## References

* [Brandao and Svore, 2017][BrandaoSvore2017]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.SdpMmwSolver.OracleError
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder MatrixOrder

/-- The proposed sampled-oracle contract is false without assumptions relating empirical
averages to the true distribution. -/
theorem not_sdpStep2SampledOracle : ¬ SdpStep2SampledOracle := by
  intro h
  let b : Fin 2 → ℝ := fun i => if i = 0 then 1 else 10
  let q : Fin 2 → ℝ := fun i => if i = 0 then 0 else 1
  have hf := h 1 2 1 (fun _ => 0) 0 b (fun _ => q)
    1 1 1 1 1 0 1 q (fun _ => 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by intro i; exact ⟨Matrix.isHermitian_zero, by simp⟩)
    ⟨Matrix.isHermitian_zero, by simp⟩
    (by intro i; dsimp [b]; split_ifs <;> norm_num)
    (by intro i; dsimp [q]; split_ifs <;> norm_num)
    (by simp [q, Fin.sum_univ_two])
    (by intro i; dsimp [q]; split_ifs <;> norm_num)
    (by intro i; simp)
    (by simp)
    (by norm_num [b])
  have hw := hf.1
  norm_num [b, q, Fin.sum_univ_two, sdpSampledWidthBudget] at hw

/-- Under the stated empirical approximation, acceptance, and scale bounds, scaling `q` by κN
satisfies `sdpSampledWidthBudget` and `sdpSampledSeparationSlack`. See [BrandaoSvore2017]. -/
theorem sdpStep2SampledOracleOnGoodEvent (m M N : ℕ)
    (b e q : Fin m → ℝ) (idx : Fin M → Fin m) (c α R κ ν : ℝ)
    (hscale : 0 < κ * (N : ℝ)) (hgrid : κ * (N : ℝ) ≤ α)
    (hR : 0 ≤ R) (htol : 0 ≤ κ + ν)
    (hcost : (∑ i, q i * b i) ≤ (∑ j, b (idx j)) / (M : ℝ) + R * (κ + ν))
    (hexpect : (∑ j, e (idx j)) / (M : ℝ) - (κ + ν) ≤ ∑ i, q i * e i)
    (hacceptCost : (∑ j, b (idx j)) / (M : ℝ) ≤
      α / (κ * (N : ℝ)) + R * (κ + ν))
    (hacceptExpect : c / (κ * (N : ℝ)) - (κ + ν) ≤
      (∑ j, e (idx j)) / (M : ℝ)) :
    (∑ i, b i * (κ * (N : ℝ) * q i)) ≤ sdpSampledWidthBudget α R κ ν ∧
    c - sdpSampledSeparationSlack α κ ν ≤
      ∑ i, (κ * (N : ℝ) * q i) * e i := by
  have hw : (∑ i, q i * b i) ≤ α / (κ * (N : ℝ)) + 2 * R * (κ + ν) := by
    linarith
  have he : c / (κ * (N : ℝ)) - 2 * (κ + ν) ≤ ∑ i, q i * e i := by
    linarith
  have hcan : κ * (N : ℝ) * (α / (κ * (N : ℝ))) = α :=
    mul_div_cancel₀ α hscale.ne'
  have hcanC : κ * (N : ℝ) * (c / (κ * (N : ℝ))) = c :=
    mul_div_cancel₀ c hscale.ne'
  have hcostScale := mul_le_mul_of_nonneg_left hw hscale.le
  have heScale := mul_le_mul_of_nonneg_left he hscale.le
  have hwidthSlack := mul_le_mul_of_nonneg_right hgrid
    (by positivity : 0 ≤ 2 * R * (κ + ν))
  have hsepSlack := mul_le_mul_of_nonneg_right hgrid
    (by positivity : 0 ≤ 2 * (κ + ν))
  constructor
  · rw [show (∑ i, b i * (κ * (N : ℝ) * q i)) =
        κ * (N : ℝ) * ∑ i, q i * b i by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring]
    dsimp [sdpSampledWidthBudget]
    rw [mul_add, hcan] at hcostScale
    nlinarith
  · rw [show (∑ i, (κ * (N : ℝ) * q i) * e i) =
        κ * (N : ℝ) * ∑ i, q i * e i by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring]
    dsimp [sdpSampledSeparationSlack]
    rw [mul_sub, hcanC] at heScale
    nlinarith

end Qatlib.Concepts.SdpMmwSolver.OracleError
