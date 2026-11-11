/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.InhomLeftGrid.InhomOptimalPreparationCostStat
import Qatlib.Concepts.LchsSimulation.InhomLeftGrid.InhomogeneousPreparedSolutionLine

/-!
# Preparation-window cost for inhomogeneous LCHS

`inhomogeneousOptimalPreparationCost` bounds the amplification-window length for the unified
inhomogeneous LCHS coefficients. With the prescribed quadrature schedule, derivative and norm
bounds, source-integral slack, and solution-norm lower bound τ, the window length is at most
`8*q + 1`, where `q = (1 + ∫ ‖b(u)‖ du) / τ`. This gives a concrete finite-grid preparation
estimate related to [AnLiuLin2023].

## Main statements

* `inhomogeneousOptimalPreparationCost`: the explicit source-norm preparation-window bound.

## References

* [An, Liu, and Lin, 2023][AnLiuLin2023]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LchsSimulation.WindowLchs

namespace Qatlib.Concepts.LchsSimulation.InhomLeftGrid
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- Proves `InhomogeneousOptimalPreparationCost`, bounding the prescribed preparation-window
length by `8*q + 1` with `q = (1 + ∫ ‖b(u)‖ du) / τ` under its schedule and regularity
hypotheses; see [AnLiuLin2023]. -/
theorem inhomogeneousOptimalPreparationCost : InhomogeneousOptimalPreparationCost := by
  intro I _ _ L H b b' s t ε τ Λ β lamL lamH bmax Mt B P i₀ hL hH hb hPSD hHerm hst
    hε hbmax0 hτ _hετ hd hβ hbmax hlL hlH hΛ _hB _hP _hprep hMt hslack _hτx
  (try dsimp only)
  let δ := min (ε/2) (ε/(4*(t-s)*bmax))
  let K := timeDependentLchsWindowCutoff δ
  let N := timeDependentLchsWindowNodes δ Λ
  let R := ∫ u in s..t, ‖toEuclidean_fromVec (b u)‖
  let S := ∑ l : Fin Mt, inhStep Mt s t*‖toEuclidean_fromVec (b (inhNode Mt s t l))‖
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hs := inh_schedule_raw_bound δ Λ (2/Real.pi+∫ u in s..t, ‖L u‖) hδ hΛ
  have hpos : 0 < Mt := by rw [hMt]; exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hmass := inh_source_mass_quadrature b b' s t β Mt hb hst.le hpos hd hβ
  have hS : S ≤ 2*R := by dsimp [S, R]; linarith
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun _ _ =>
    mul_nonneg (inh_step_nonneg Mt s t hst.le) (norm_nonneg _))
  have hR0 : 0 ≤ R := intervalIntegral.integral_nonneg hst.le (fun _ _ => norm_nonneg _)
  have hα := inh_unified_mass_pos b s t K N Mt hst.le hs.1 hs.2.1
  have hαbound : coefficientMass (inhUnifiedCoeff b s t K N Mt) ≤ 4*(1+R) := by
    rw [inh_unified_coefficient_mass b s t K N Mt hst.le]
    change coefficientMass (staticLchsCoeff K N)*(1+S) ≤ _
    have hh := static_lchs_grid_coefficient_mass_le_two K N hs.2.1 hs.2.2.1
    calc
      _ ≤ 2*(1+S) := mul_le_mul_of_nonneg_right hh (by linarith)
      _ ≤ 4*(1+R) := by linarith
  have hm := (static_lchs_window_bound _ τ hα hτ).2
  refine hm.trans (add_le_add ?_ le_rfl)
  change 2*coefficientMass (inhUnifiedCoeff b s t K N Mt)/τ ≤ 8*((1+R)/τ)
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (by linarith) hτ.le

end Qatlib.Concepts.LchsSimulation.InhomLeftGrid
