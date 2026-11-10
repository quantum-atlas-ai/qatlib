/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.MainResults.GaussianHybrid
import Qatlib.Papers.RydbergMaxCut26.StateBounds.TwoThirds
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
