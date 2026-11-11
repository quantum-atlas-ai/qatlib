/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.MainResults.GaussianHybrid

/-!
# Physical Gaussian hybrid output

Establishes that Gaussian hybrid selection defines a probability law and produces positive
semidefinite trace-one output matrices. Its expected energy equals the Gaussian integral of the
minimum of the fixed-state and rounded product-state energies. See [CrostaSaubanereHuber2026].

## Main statements

* `gaussianOutputLaw_probability`: proves that the output law is a probability measure.
* `gaussianOutputEnergy_eq_min`: rewrites expected energy as an integral of candidate-energy
  minima.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped Classical ComplexOrder
open MeasureTheory Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Bloch
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.Gram
open Qatlib.Papers.RydbergMaxCut26.Rounding.GaussianMatrix
open Qatlib.Papers.RydbergMaxCut26.MainResults.FiniteHybrid
open Qatlib.Papers.RydbergMaxCut26.MainResults.MeasureHybrid
open Qatlib.Papers.RydbergMaxCut26.MainResults.PhysicalHybrid

namespace Qatlib.Papers.RydbergMaxCut26.MainResults.GaussianHybrid

/-- For loopless endpoints and a positive semidefinite trace-one input, the Gaussian hybrid
output law is a probability measure [CrostaSaubanereHuber2026]. -/
theorem gaussianOutputLaw_probability {n : ℕ} {E : Type*} [Fintype E]
    (ends : E→Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E→ℝ)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    IsProbabilityMeasure (outputLaw (rawMatrixLaw (Fin 2×MomentIndex n)) (qmcHamiltonian ends w) ρ
      (productCandidate ρ hρ htr (id : GaussianSamples n→GaussianSamples n))) :=
  outputLaw_probability _ _ _ _
    (product_energy_measurable ends hends w ρ hρ htr id (gaussian_entries_measurable n))

/-- Every output matrix selected between a physical input and its Gaussian rounded product
candidate is positive semidefinite with trace one [CrostaSaubanereHuber2026]. -/
theorem gaussianOutputDensity_physical {n : ℕ}
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (z : GaussianSamples n×Bool) :
    (outputDensity ρ (productCandidate ρ hρ htr id) z).PosSemidef ∧
      (outputDensity ρ (productCandidate ρ hρ htr id) z).trace=1 :=
  output_density ρ hρ htr _ (productCandidate_density ρ hρ htr id) z

/-- For loopless endpoints and a physical input, the expected Gaussian hybrid energy equals the
raw Gaussian integral of the minimum of the input and rounded product-candidate QMC energies
[CrostaSaubanereHuber2026]. -/
theorem gaussianOutputEnergy_eq_min {n : ℕ} {E : Type*} [Fintype E]
    (ends : E→Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E→ℝ)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    gaussianOutputEnergy ends w ρ hρ htr=
      ∫ R : GaussianSamples n,min (energy (qmcHamiltonian ends w) ρ)
        (energy (qmcHamiltonian ends w) (productCandidate ρ hρ htr id R))
        ∂rawMatrixLaw (Fin 2×MomentIndex n) :=
  output_energy _ _ _ _
    (product_energy_measurable ends hends w ρ hρ htr id (gaussian_entries_measurable n))

end Qatlib.Papers.RydbergMaxCut26.MainResults.GaussianHybrid
