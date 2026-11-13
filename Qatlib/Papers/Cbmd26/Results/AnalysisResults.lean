/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.MatrixResidue
import Qatlib.Foundations.CbmdAnalysis.Core.PiecewiseRepresentation

/-!
# Analytic results for contour-based matrix decomposition

This module exposes the matrix residue formula, the absolutely summable auxiliary-pole sampling
identity, and the finite real-sample LCU approximation for piecewise-continuous dissipative
evolution. These statements formalize the analytic ingredients of [WangEtAl2026].

## Main statements

* `matrix_residue_on_open`: integrates a meromorphic matrix function around a positive Jordan
  contour.
* `matrix_series_original_input`: gives the auxiliary-pole sampling identity.
* `fast_lcu_original_input`: provides finite unitary samples with explicit error, mass,
  frequency, and cardinality bounds.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

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

/-- For an entrywise meromorphic matrix function on an open set containing the filled contour
hull, analytic on the contour and with every interior singularity in the finite interior set
`S`, the contour integral is `2πi` times the sum of matrix residues over `S`. This is the
matrix residue statement of [Wang et al., Lemma 1][WangEtAl2026]. -/
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

/-- For piecewise-continuous dissipative evolution and auxiliary poles avoiding the target and
real sampling lattice, the integrated norm budget implies absolute summability of the
auxiliary samples and the stated target-minus-series-minus-pole-corrections identity. This
gives the sampling formula of [Wang et al., Lemma 2][WangEtAl2026]. -/
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

/-- For piecewise-continuous dissipative evolution and `δ ∈ (0, 1]`, the chosen finite integer
LCU approximates the target within `δ` using unitary real samples, with explicit
coefficient-mass, frequency, and sample-count bounds. This is the finite-sample
approximation underlying [Wang et al., Lemma 3][WangEtAl2026]. -/
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
