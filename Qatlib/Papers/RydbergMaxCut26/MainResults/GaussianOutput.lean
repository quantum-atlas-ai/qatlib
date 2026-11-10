/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.MainResults.GaussianHybrid
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

theorem gaussianOutputLaw_probability {n : ℕ} {E : Type*} [Fintype E]
    (ends : E→Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E→ℝ)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    IsProbabilityMeasure (outputLaw (rawMatrixLaw (Fin 2×MomentIndex n)) (qmcHamiltonian ends w) ρ
      (productCandidate ρ hρ htr (id : GaussianSamples n→GaussianSamples n))) :=
  outputLaw_probability _ _ _ _
    (product_energy_measurable ends hends w ρ hρ htr id (gaussian_entries_measurable n))

theorem gaussianOutputDensity_physical {n : ℕ}
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (z : GaussianSamples n×Bool) :
    (outputDensity ρ (productCandidate ρ hρ htr id) z).PosSemidef ∧
      (outputDensity ρ (productCandidate ρ hρ htr id) z).trace=1 :=
  output_density ρ hρ htr _ (productCandidate_density ρ hρ htr id) z

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
