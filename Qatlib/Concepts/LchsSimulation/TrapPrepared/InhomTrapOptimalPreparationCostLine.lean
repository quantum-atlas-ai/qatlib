/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.TrapPrepared.InhomTrapOptimalPreparationCostStat
import Qatlib.Concepts.LchsSimulation.TrapPrepared.InhomTrapPreparedSolutionLine

/-!
# Preparation-window bound for trapezoidal forced evolution

`inhomogeneousTrapezoidOptimalPreparationCost` bounds the prescribed amplification window by `8
* q + 1`, where `q` is the initial-plus-integrated-source mass divided by the output norm lower
bound. The estimate uses the computed source schedule and its source-mass condition.

The mathematical background is described in [AnLiuLin2023].

## Main statements

* `inhomogeneousTrapezoidOptimalPreparationCost`: proves the `8 * q + 1` window bound.

## References

* [An et al., 2023][AnLiuLin2023]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.LchsSimulation.InhomLeftGrid
open Qatlib.Concepts.LchsSimulation.KTrapezoid
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LchsSimulation.TimeTrapezoid
open Qatlib.Concepts.LchsSimulation.WindowLchs

namespace Qatlib.Concepts.LchsSimulation.TrapPrepared
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- Under the prescribed trapezoidal source schedule and source-mass condition, the
amplification window is at most `8 * q + 1`, where `q = (1 + ∫ u in s..t,
‖toEuclidean_fromVec (b u)‖) / τ` [AnLiuLin2023]. -/
theorem inhomogeneousTrapezoidOptimalPreparationCost :
    InhomogeneousTrapezoidOptimalPreparationCost := by
  intro I _ _ L L' H H' b b' b'' s t ε τ Λ β β₂ lamL lamH lamLd lamHd bmax Mt B P i₀ hL hH hb
    hPSD hHerm hst hε hbmax0 hτ _hετ hdL hdH hnLd hnHd hd hd' hβ hβ₂ hbmax hlL hlH hΛ
    _hB _hP _hprep hMt hslack _hτx
  (try dsimp only)
  let δ := min (ε/2) (ε/(4*(t-s)*bmax))
  let K := timeDependentLchsWindowCutoff δ
  let N := timeDependentLchsWindowNodes δ Λ
  let R := ∫ u in s..t, ‖toEuclidean_fromVec (b u)‖
  let S := ∑ l : Fin (Mt+1), inhTrapWeight Mt s t l*
    ‖toEuclidean_fromVec (b (inhTrapNode Mt s t l))‖
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hs := inh_schedule_raw_bound δ Λ (2/Real.pi+∫ u in s..t, ‖L u‖) hδ hΛ
  have hpos : 0 < Mt := by rw [hMt]; exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hmass := inh_trap_source_mass_quadrature b b' s t β Mt hb hst.le hpos hd hβ
  have hS : S ≤ 2*R := by dsimp [S, R]; linarith
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun _ _ =>
    mul_nonneg (inh_trap_weight_nonneg Mt s t hst.le _) (norm_nonneg _))
  have hR0 : 0 ≤ R := intervalIntegral.integral_nonneg hst.le (fun _ _ => norm_nonneg _)
  have hα := inhTrap_unified_mass_pos b s t K N Mt hst.le hs.1 hs.2.1
  have hαbound : coefficientMass (inhTrapUnifiedCoeff b s t K N Mt) ≤ 4*(1+R) := by
    rw [inhTrap_unified_coefficient_mass b s t K N Mt hst.le]
    change coefficientMass (staticLchsCoeff K N)*(1+S) ≤ _
    have hh := static_lchs_grid_coefficient_mass_le_two K N hs.2.1 hs.2.2.1
    calc
      _ ≤ 2*(1+S) := mul_le_mul_of_nonneg_right hh (by linarith)
      _ ≤ 4*(1+R) := by linarith
  have hm := (static_lchs_window_bound _ τ hα hτ).2
  refine hm.trans (add_le_add ?_ le_rfl)
  change 2*coefficientMass (inhTrapUnifiedCoeff b s t K N Mt)/τ ≤ 8*((1+R)/τ)
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (by linarith) hτ.le

end Qatlib.Concepts.LchsSimulation.TrapPrepared
