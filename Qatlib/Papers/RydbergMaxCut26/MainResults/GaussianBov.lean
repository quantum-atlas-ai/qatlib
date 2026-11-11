/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.Rounding.GeneralBov
import Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianEnergy
import Qatlib.Papers.RydbergMaxCut26.MainResults.PhysicalRatios

/-!
# Gaussian kernel for physical rounding

Identifies the expected inner product of physically rounded vectors at distinct sites under the
raw Gaussian matrix law. The expectation is `kernelConstant` times `Fhat` evaluated at the
physical two-site correlation `tParam`, connecting the physical moment construction to the
scalar kernel estimates. See [CrostaSaubanereHuber2026].

## Main statements

* `actual_root_physical_BOV`: evaluates the expected rounded inner product for a positive
  semidefinite trace-one input.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped RealInnerProductSpace Classical ComplexOrder
open MeasureTheory ProbabilityTheory Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Bloch
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.Gram
open Qatlib.Papers.RydbergMaxCut26.Rounding.Physical
open Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianPhysical
open Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianMatrix
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.EnergyBounds
open Qatlib.Papers.RydbergMaxCut26.RatioBounds.SOS

namespace Qatlib.Papers.RydbergMaxCut26.MainResults.GaussianHybrid

/-- For a positive semidefinite trace-one `ρ` and distinct sites `i` and `j`, the expected inner
product of their physically rounded vectors under the raw Gaussian matrix law equals
`kernelConstant * Fhat (tParam ρ i j)` [CrostaSaubanereHuber2026]. -/
theorem actual_root_physical_BOV (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (i j : Fin n) (hij : i≠j) :
    (∫ R : Fin 3→Fin 2×MomentIndex n→ℝ,
      ∑ a : Fin 3,physicalRound n ρ hρ htr R i a*physicalRound n ρ hρ htr R j a
        ∂rawMatrixLaw (Fin 2×MomentIndex n))=
      kernelConstant*Qatlib.Papers.RydbergMaxCut26.RatioBounds.Core.Fhat (tParam ρ i j) := by
  rw [physical_dot_expectation]
  have h := Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianJoint.actual_raw_BOV_three
    (physicalFitEuclidean n ρ hρ htr i) (physicalFitEuclidean n ρ hρ htr j)
    (physicalFitEuclidean_unit n ρ hρ htr i) (physicalFitEuclidean_unit n ρ hρ htr j)
  change rawExpectation _ _=Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianMatrix.bovThreeKernel
    (inner ℝ (physicalFitEuclidean n ρ hρ htr i) (physicalFitEuclidean n ρ hρ htr j)) at h
  rw [h,physicalFitEuclidean_dot n ρ hρ htr i j hij]
  simp only [Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianMatrix.bovThreeKernel,kernelConstant,
    Qatlib.Papers.RydbergMaxCut26.RatioBounds.Core.Fhat]
  ring

end Qatlib.Papers.RydbergMaxCut26.MainResults.GaussianHybrid
