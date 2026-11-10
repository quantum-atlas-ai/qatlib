/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.MatrixResidue
import Qatlib.Foundations.CbmdAnalysis.Core.PiecewiseRepresentation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.Cbmd26.Results
namespace CBMD
open Set Matrix
open Qatlib.Foundations.CbmdAnalysis.Core.CBMD
open Qatlib.Foundations.CbmdAnalysis.Residue.CBMDResidue
open Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti
open Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Contour
open scoped BigOperators

section Residue
open scoped Topology Matrix.Norms.Elementwise

theorem matrix_residue_on_open {n m : Type*} [Fintype n] [Fintype m]
    (Γ : PositiveJordanContour) (F : ℂ → Matrix n m ℂ)
    (U : Set ℂ) (_hU : IsOpen U) (hfill : filledHull Γ.trace ⊆ U)
    (hf : ∀ i j, MeromorphicOn (fun w => F w i j) U) (S : Finset ℂ)
    (hS : ∀ s ∈ S, s ∈ Γ.inside)
    (hboundary : ∀ i j z, z ∈ Γ.trace → AnalyticAt ℂ (fun w => F w i j) z)
    (hall : ∀ i j z, z ∈ Γ.inside → ¬ AnalyticAt ℂ (fun w => F w i j) z → z ∈ S) :
    (∫ t in Γ.start..Γ.finish, deriv Γ.curve t • F (Γ.curve t)) =
      (2 * (Real.pi : ℂ) * Complex.I) • ∑ s ∈ S, PositiveJordanContour.matrixResidue F s := by
  exact Qatlib.Foundations.CbmdAnalysis.Residue.CBMDResidue.PositiveJordanContour.matrix_residue_on_open
    Γ F U _hU hfill hf S hS hboundary hall

end Residue

open scoped Topology Matrix.Norms.L2Operator ComplexOrder MatrixOrder
variable {I : Type} [Fintype I] [DecidableEq I]
variable {H L : ℝ → Matrix I I ℂ} {a b : ℝ}

theorem matrix_series_original_input
    (P : FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b)
    (hH : ∀ t ∈ Icc a b, (H t).IsHermitian) (hL : ∀ t ∈ Icc a b, (L t).PosSemidef)
    (s : Finset ℂ) (hs : s.Nonempty) (hsTarget : -Complex.I ∉ s)
    {spacing : ℝ} (ha : 0 < spacing)
    (hsLattice : ∀ p ∈ s, ∀ k : ℤ, p ≠ (((k : ℝ) / spacing : ℝ) : ℂ))
    (hbudget : (∫ t in a..b, ‖L t‖) ≤ 2 * Real.pi * spacing) :
    let U := fun z => P.evolution z b
    Summable (fun k : ℤ => ‖auxSample s spacing U k‖) ∧
    U (-Complex.I) - (∑' k : ℤ, auxSample s spacing U k) -
      (∑ p ∈ s,
        (((Real.exp (-2 * Real.pi * spacing) - 1 : ℝ) : ℂ) /
          ((Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (spacing : ℂ) * p) - 1) *
            auxDeletedPoleProduct s p)) • U p) = 0  := by
  exact Qatlib.Foundations.CbmdAnalysis.Core.CBMD.FinitePiecewiseContinuousOn.matrix_series_original_input
    P hH hL s hs hsTarget ha hsLattice hbudget

theorem fast_lcu_original_input
    (P : FinitePiecewiseContinuousOn (fun t => (H t, L t)) a b)
    (hH : ∀ t ∈ Icc a b, (H t).IsHermitian) (hL : ∀ t ∈ Icc a b, (L t).PosSemidef)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let ρ := ∫ t in a..b, ‖L t‖
    let m := kernelOrder (δ / 2)
    let spacing := kernelSpacing ρ (δ / 2) m
    let K := kernelCutoff spacing (δ / 2)
    let U := fun z => P.evolution z b
    let B := max 0 (Real.log (kernelTailConstant / (δ / 2)) / 2) + 2
    ‖U (-Complex.I) - integerLCUSum m spacing K U‖ ≤ δ ∧
    (∀ k : ℤ, U (((k : ℝ) / spacing : ℝ) : ℂ) ∈ Matrix.unitaryGroup I ℂ) ∧
    (∑ k ∈ Finset.Icc (-(K : ℤ)) K, ‖integerWeight m spacing ((k : ℝ) / spacing)‖) ≤
      5 * integerWeightConstant ∧
    (∀ k ∈ Finset.Icc (-(K : ℤ)) K,
      |(k : ℝ) / spacing| < 2 * max 0 (Real.log (kernelTailConstant / (δ / 2)) / 2) + 5) ∧
    (Finset.Icc (-(K : ℤ)) K).card = 2 * K + 1 ∧
    ((Finset.Icc (-(K : ℤ)) K).card : ℝ) <
      4 * (1 + (ρ + Real.log (kernelAuxiliaryConstant / (δ / 2)) + B) /
        (2 * Real.pi)) * B + 3  := by
  exact Qatlib.Foundations.CbmdAnalysis.Core.CBMD.FinitePiecewiseContinuousOn.fast_lcu_original_input
    P hH hL hδ hδ1

end CBMD
end Qatlib.Papers.Cbmd26.Results
