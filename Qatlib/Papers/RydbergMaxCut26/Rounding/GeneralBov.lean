/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.JointTransport
import Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPhysicalCases
import Qatlib.Papers.RydbergMaxCut26.Rounding.Analytic.ActualGaussianEndpoints
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped RealInnerProductSpace Classical ComplexOrder
open MeasureTheory ProbabilityTheory Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPair
open Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianMatrix
open Qatlib.Papers.RydbergMaxCut26.Rounding.Laplace
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.Gram Qatlib.Papers.RydbergMaxCut26.Rounding.Physical
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.EnergyBounds
open Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPhysical
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Bloch
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph

namespace Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianJoint

theorem rawExpectation_eq_actualKernel_closed {I : Type} [Fintype I] (u v : Row I)
    (hu : ‖u‖=1) (hv : ‖v‖=1) : rawExpectation u v=actualKernel (inner ℝ u v) := by
  have hle : |inner ℝ u v|≤1 := by simpa only [hu,hv,one_mul] using abs_real_inner_le_norm u v
  by_cases hi : |inner ℝ u v|<1
  · exact rawExpectation_eq_actualKernel u v hu hv hi
  have he : |inner ℝ u v|=1 := le_antisymm hle (le_of_not_gt hi)
  rcases (abs_eq (by norm_num : (0:ℝ)≤1)).mp he with h|h
  · rw [rawExpectation_inner_one u v hu hv h,h,actualKernel_one]
  · rw [rawExpectation_inner_neg_one u v hu hv h,h,actualKernel_neg_one]

theorem actual_raw_BOV_three {I : Type} [Fintype I] (u v : Row I)
    (hu : ‖u‖=1) (hv : ‖v‖=1) :
    rawExpectation u v=bovThreeKernel (inner ℝ u v) := by
  rw [rawExpectation_eq_actualKernel_closed u v hu hv]
  exact actualKernel_hypergeom_closed _
      (by simpa only [hu,hv,one_mul] using abs_real_inner_le_norm u v)

theorem actual_physical_BOV_three (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (i j : Fin n) (hij : i≠j) :
    (∫ R : Fin 3→Fin 2×MomentIndex n→ℝ,
      ∑ a : Fin 3,physicalRound n ρ hρ htr R i a*physicalRound n ρ hρ htr R j a
        ∂rawMatrixLaw (Fin 2×MomentIndex n))=bovThreeKernel (tParam ρ i j) := by
  rw [physical_dot_expectation]
  rw [actual_raw_BOV_three _ _ (physicalFitEuclidean_unit n ρ hρ htr i) (physicalFitEuclidean_unit n ρ hρ htr j)]
  rw [physicalFitEuclidean_dot n ρ hρ htr i j hij]

theorem actual_physical_energy_BOV {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    (∫ R : Fin 3→Fin 2×MomentIndex n→ℝ,
      energy (qmcHamiltonian ends w) (productState (physicalRound n ρ hρ htr R))
        ∂rawMatrixLaw (Fin 2×MomentIndex n))=
      -(1/4:ℝ)*∑ e,w e*(1-bovThreeKernel (tParam ρ (ends e).1 (ends e).2)) := by
  rw [physical_energy_expectation ends hends w ρ hρ htr]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  rw [actual_raw_BOV_three _ _ (physicalFitEuclidean_unit n ρ hρ htr (ends e).1)
    (physicalFitEuclidean_unit n ρ hρ htr (ends e).2)]
  rw [physicalFitEuclidean_dot n ρ hρ htr _ _ (hends e)]

end Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianJoint
