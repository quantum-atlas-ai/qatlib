/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.WindowLchs.TimeDependentLCHSWindow
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.LchsSimulation.WindowLchs
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding MeasureTheory
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

theorem time_dependent_lchs_window_optimal_preparation_cost :
  ∀ (I : Type) [Fintype I] [DecidableEq I] (L H : ℝ → Matrix I I ℂ)
    (s t ε Λ : ℝ) (B : Matrix I I ℂ) (i₀ : I),
    Continuous L → Continuous H → (∀ u : ℝ, (L u).PosSemidef) →
    (∀ u : ℝ, (H u).IsHermitian) → s ≤ t → B ∈ Matrix.unitaryGroup I ℂ →
    0 < ε → 2/Real.pi + (∫ u in s..t, ‖L u‖) ≤ Λ →
    let v := orderedEvolution (fun u => L u+Complex.I • H u) s t *ᵥ (B *ᵥ Ket i₀)
    0 < ‖toEuclidean_fromVec v‖ → ε ≤ ‖toEuclidean_fromVec v‖/2 →
    let K := timeDependentLchsWindowCutoff ε
    let N := timeDependentLchsWindowNodes ε Λ
    let c := staticLchsCoeff K N
    let α := coefficientMass c
    let q := ‖toEuclidean_fromVec v‖⁻¹
    (staticLchsWindow α ‖toEuclidean_fromVec v‖ : ℝ) ≤ 4*q+1 := by
  intro I _ _ L H s t ε Λ B i₀ hL hH hPSD hHerm hst _hB hε hΛ
  (try dsimp only)
  intro hv _hεv
  have hs := time_dependent_lchs_window_schedule_quadrature I L H s t ε Λ
    hL hH hPSD hHerm hst hε hΛ
  have hmb := (static_lchs_window_bound _ _ hs.2.2.2.1 hv).2
  refine hmb.trans (add_le_add ?_ le_rfl)
  rw [← div_eq_mul_inv]
  apply div_le_div_of_nonneg_right _ hv.le
  have := hs.2.2.2.2.1
  linarith

end Qatlib.Concepts.LchsSimulation.WindowLchs
