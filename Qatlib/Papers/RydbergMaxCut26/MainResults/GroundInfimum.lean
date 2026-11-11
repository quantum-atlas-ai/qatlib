/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.MainResults.GaussianHybrid
import Qatlib.Papers.RydbergMaxCut26.StateBounds.TwoThirds

/-!
# Gaussian guarantees against the ground-energy infimum

Transfers the Gaussian hybrid energy comparisons to `qmcGroundEnergy`, the infimum over all
physical density matrices. For loopless endpoints and nonnegative weights, the resulting bounds
retain the exact-secondary-ground-state assumption for 0.651 and the secondary-energy quality
assumption for 0.614. See [CrostaSaubanereHuber2026].

## Main statements

* `gaussian_physical_infimum_651`: compares the exact-resource output with the QMC ground-energy
  infimum.
* `gaussian_physical_infimum_614`: gives the comparison under the `89 / 100` quality bound.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped Classical ComplexOrder
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Bloch
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.EnergyBounds
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.Phase
open Qatlib.Papers.RydbergMaxCut26.StateBounds.Variational
open Qatlib.Papers.RydbergMaxCut26.StateBounds.TwoThirds

namespace Qatlib.Papers.RydbergMaxCut26.MainResults.GaussianHybrid

/-- For loopless endpoints and nonnegative weights, the Gaussian hybrid output built from a
secondary ground density has expected energy at most `(651 / 1000) * qmcGroundEnergy ends w`
[CrostaSaubanereHuber2026]. -/
theorem gaussian_physical_infimum_651 {n : ℕ} {E : Type*} [Fintype E]
    (ends : E→Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2)
    (w : E→ℝ) (hw : ∀ e,0≤w e)
    (ρR : Matrix (Reg n) (Reg n) ℂ) (hgroundR : GroundDensity (secondaryHamiltonian ends w) ρR) :
    gaussianOutputEnergy ends w ρR hgroundR.1 hgroundR.2.1≤(651/1000:ℝ)*qmcGroundEnergy ends w := by
  have hb : (1000/651:ℝ)*gaussianOutputEnergy ends w ρR hgroundR.1 hgroundR.2.1≤qmcGroundEnergy ends w := by
    apply le_csInf
    · exact ⟨energy (qmcHamiltonian ends w) ρR,ρR,hgroundR.1,hgroundR.2.1,rfl⟩
    · rintro e ⟨ρ,hρ,htr,rfl⟩
      have h := gaussian_physical_651 ends hends w hw ρR hgroundR ρ hρ htr
      linarith
  linarith

/-- For loopless endpoints and nonnegative weights, a physical input with secondary energy at
most `89 / 100` times a secondary ground energy has expected Gaussian hybrid energy at most
`(614 / 1000) * qmcGroundEnergy ends w` [CrostaSaubanereHuber2026]. -/
theorem gaussian_physical_infimum_614 {n : ℕ} {E : Type*} [Fintype E]
    (ends : E→Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2)
    (w : E→ℝ) (hw : ∀ e,0≤w e)
    (ρR : Matrix (Reg n) (Reg n) ℂ) (hgroundR : GroundDensity (secondaryHamiltonian ends w) ρR)
    (ρA : Matrix (Reg n) (Reg n) ℂ) (hA : ρA.PosSemidef) (hAtr : ρA.trace=1)
    (hquality : energy (secondaryHamiltonian ends w) ρA≤(89/100:ℝ)*energy (secondaryHamiltonian ends w) ρR) :
    gaussianOutputEnergy ends w ρA hA hAtr≤(614/1000:ℝ)*qmcGroundEnergy ends w := by
  have hb : (1000/614:ℝ)*gaussianOutputEnergy ends w ρA hA hAtr≤qmcGroundEnergy ends w := by
    apply le_csInf
    · exact ⟨energy (qmcHamiltonian ends w) ρA,ρA,hA,hAtr,rfl⟩
    · rintro e ⟨ρ,hρ,htr,rfl⟩
      have h := gaussian_physical_614 ends hends w hw ρR hgroundR ρA hA hAtr hquality ρ hρ htr
      linarith
  linarith

end Qatlib.Papers.RydbergMaxCut26.MainResults.GaussianHybrid
