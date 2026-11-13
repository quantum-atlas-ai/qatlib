/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.MainResults.GaussianBov
import Qatlib.Papers.RydbergMaxCut26.MainResults.GraphSigns

/-!
# Gaussian hybrid approximation guarantees

Defines the Gaussian sample space and the expected QMC energy of the physical hybrid selector.
For loopless endpoints and nonnegative weights, an exact secondary ground density gives the
0.651 comparison with every physical QMC candidate, while a physical input with secondary energy
at most 0.89 times that ground energy gives the 0.614 comparison. Positive total weight permits
the corresponding ratios against a QMC ground density. See [CrostaSaubanereHuber2026].

## Main statements

* `gaussian_physical_651` and `gaussian_physical_614`: prove the conditional energy comparisons.
* `gaussian_physical_ratio_651` and `gaussian_physical_ratio_614`: express them as ratio lower
  bounds.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped Classical ComplexOrder
open MeasureTheory Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Bloch
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.Gram
open Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianMatrix
open Qatlib.Papers.RydbergMaxCut26.Rounding.Physical
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Ground
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.EnergyBounds
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.Phase
open Qatlib.Papers.RydbergMaxCut26.StateBounds.Variational
open Qatlib.Papers.RydbergMaxCut26.MainResults.FiniteHybrid
open Qatlib.Papers.RydbergMaxCut26.MainResults.MeasureHybrid
open Qatlib.Papers.RydbergMaxCut26.MainResults.PhysicalHybrid
open Qatlib.Papers.RydbergMaxCut26.MainResults.PhysicalRatios
open Qatlib.Papers.RydbergMaxCut26.MainResults.GraphSigns

namespace Qatlib.Papers.RydbergMaxCut26.MainResults.GaussianHybrid

/-- The type of real three-row sample matrices with columns indexed by `Fin 2 × MomentIndex n`. -/
abbrev GaussianSamples (n : ℕ) := Fin 3→Fin 2×MomentIndex n→ℝ

/-- Every coordinate evaluation on the Gaussian sample-matrix space is measurable. -/
theorem gaussian_entries_measurable (n : ℕ) (a : Fin 3) (c : Fin 2×MomentIndex n) :
    Measurable (fun R : GaussianSamples n => R a c) :=
  (measurable_pi_apply c).comp (measurable_pi_apply a)

/-- The integral of the selected QMC energy under the Gaussian hybrid output law built from `ρ`
and its rounded product candidates. -/
def gaussianOutputEnergy {n : ℕ} {E : Type*} [Fintype E] (ends : E→Fin n×Fin n) (w : E→ℝ)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) : ℝ :=
  ∫ z,energy (qmcHamiltonian ends w) (outputDensity ρ (productCandidate ρ hρ htr (id : GaussianSamples n→GaussianSamples n)) z)
    ∂outputLaw (rawMatrixLaw (Fin 2×MomentIndex n)) (qmcHamiltonian ends w) ρ
      (productCandidate ρ hρ htr (id : GaussianSamples n→GaussianSamples n))

/-- For loopless endpoints and nonnegative weights, a secondary ground density gives expected
Gaussian hybrid energy at most `651 / 1000` times the QMC energy of any positive
semidefinite trace-one candidate [CrostaSaubanereHuber2026]. -/
theorem gaussian_physical_651 {n : ℕ} {E : Type*} [Fintype E]
    (ends : E→Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2)
    (w : E→ℝ) (hw : ∀ e,0≤w e)
    (ρR : Matrix (Reg n) (Reg n) ℂ) (hgroundR : GroundDensity (secondaryHamiltonian ends w) ρR)
    (ρQ : Matrix (Reg n) (Reg n) ℂ) (hQ : ρQ.PosSemidef) (hQtr : ρQ.trace=1) :
    gaussianOutputEnergy ends w ρR hgroundR.1 hgroundR.2.1≤
      (651/1000:ℝ)*energy (qmcHamiltonian ends w) ρQ := by
  exact physical_651 (rawMatrixLaw (Fin 2×MomentIndex n)) ends hends w hw ρR hgroundR
    ρQ hQ hQtr id (gaussian_entries_measurable n)
    (fun e => actual_root_physical_BOV n ρR hgroundR.1 hgroundR.2.1 _ _ (hends e))

/-- For loopless endpoints and nonnegative weights, a physical input with secondary energy at
most `89 / 100` times a secondary ground energy gives expected Gaussian hybrid energy at
most `614 / 1000` times the QMC energy of any physical candidate [CrostaSaubanereHuber2026]. -/
theorem gaussian_physical_614 {n : ℕ} {E : Type*} [Fintype E]
    (ends : E→Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2)
    (w : E→ℝ) (hw : ∀ e,0≤w e)
    (ρR : Matrix (Reg n) (Reg n) ℂ) (hgroundR : GroundDensity (secondaryHamiltonian ends w) ρR)
    (ρA : Matrix (Reg n) (Reg n) ℂ) (hA : ρA.PosSemidef) (hAtr : ρA.trace=1)
    (hquality : energy (secondaryHamiltonian ends w) ρA≤(89/100:ℝ)*energy (secondaryHamiltonian ends w) ρR)
    (ρQ : Matrix (Reg n) (Reg n) ℂ) (hQ : ρQ.PosSemidef) (hQtr : ρQ.trace=1) :
    gaussianOutputEnergy ends w ρA hA hAtr≤(614/1000:ℝ)*energy (qmcHamiltonian ends w) ρQ := by
  exact physical_614 (rawMatrixLaw (Fin 2×MomentIndex n)) ends hends w hw ρR hgroundR
    ρA hA hAtr hquality ρQ hQ hQtr id (gaussian_entries_measurable n)
    (fun e => actual_root_physical_BOV n ρA hA hAtr _ _ (hends e))

/-- For loopless endpoints, nonnegative weights, and positive total weight, the expected
Gaussian hybrid energy from a secondary ground density divided by a QMC ground energy is at
least `651 / 1000` [CrostaSaubanereHuber2026]. -/
theorem gaussian_physical_ratio_651 {n : ℕ} {E : Type*} [Fintype E]
    (ends : E→Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2)
    (w : E→ℝ) (hw : ∀ e,0≤w e) (hW : 0<∑ e,w e)
    (ρR : Matrix (Reg n) (Reg n) ℂ) (hgroundR : GroundDensity (secondaryHamiltonian ends w) ρR)
    (ρQ : Matrix (Reg n) (Reg n) ℂ) (hQ : GroundDensity (qmcHamiltonian ends w) ρQ) :
    (651/1000:ℝ)≤gaussianOutputEnergy ends w ρR hgroundR.1 hgroundR.2.1/
      energy (qmcHamiltonian ends w) ρQ :=
  physical_ratio ends hends w hW ρQ hQ _ _
    (gaussian_physical_651 ends hends w hw ρR hgroundR ρQ hQ.1 hQ.2.1)

/-- For loopless endpoints, nonnegative weights, and positive total weight, a physical input
satisfying the `89 / 100` secondary-energy quality bound gives an expected Gaussian hybrid
to QMC ground-energy ratio at least `614 / 1000` [CrostaSaubanereHuber2026]. -/
theorem gaussian_physical_ratio_614 {n : ℕ} {E : Type*} [Fintype E]
    (ends : E→Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2)
    (w : E→ℝ) (hw : ∀ e,0≤w e) (hW : 0<∑ e,w e)
    (ρR : Matrix (Reg n) (Reg n) ℂ) (hgroundR : GroundDensity (secondaryHamiltonian ends w) ρR)
    (ρA : Matrix (Reg n) (Reg n) ℂ) (hA : ρA.PosSemidef) (hAtr : ρA.trace=1)
    (hquality : energy (secondaryHamiltonian ends w) ρA≤(89/100:ℝ)*energy (secondaryHamiltonian ends w) ρR)
    (ρQ : Matrix (Reg n) (Reg n) ℂ) (hQ : GroundDensity (qmcHamiltonian ends w) ρQ) :
    (614/1000:ℝ)≤gaussianOutputEnergy ends w ρA hA hAtr/energy (qmcHamiltonian ends w) ρQ :=
  physical_ratio ends hends w hW ρQ hQ _ _
    (gaussian_physical_614 ends hends w hw ρR hgroundR ρA hA hAtr hquality ρQ hQ.1 hQ.2.1)

end Qatlib.Papers.RydbergMaxCut26.MainResults.GaussianHybrid
