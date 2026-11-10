/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.StateBounds.CliffordIsotropy
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Matrix
open Qatlib
open Qatlib.Foundations.PureStateMath
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.StateBounds.Variational
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.EnergyBounds
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.Phase
open Qatlib.Papers.RydbergMaxCut26.StateBounds.Clifford

def GroundDensity {I : Type*} [Fintype I] (H ρ : Matrix I I ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace=1 ∧ ∀ σ : Matrix I I ℂ, σ.PosSemidef → σ.trace=1 → energy H ρ≤energy H σ

theorem weighted_denom_sum {E : Type*} [Fintype E] (w t : E → ℝ) (c : ℝ) :
    (∑ e,w e*(1-c*t e))=(∑ e,w e)-c*(∑ e,w e*t e) := by
  have he : ∀ e,w e*(1-c*t e)=w e-c*(w e*t e) := by intro e;ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum]

theorem secondary_ground_lower {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ)
    (ρR : Matrix (Reg n) (Reg n) ℂ) (hR : GroundDensity (secondaryHamiltonian ends w) ρR)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    -(1/4:ℝ)*(∑ e,w e)+(3/8:ℝ)*energy (secondaryHamiltonian ends w) ρR ≤ energy (qmcHamiltonian ends w) ρ := by
  have hd := isotropic_density n ρ hρ htr
  have hmin := hR.2.2 (isotropicState n ρ) hd.1 hd.2
  calc
    _ ≤ -(1/4:ℝ)*(∑ e,w e)+(3/8:ℝ)*energy (secondaryHamiltonian ends w) (isotropicState n ρ) := by linarith
    _ = energy (qmcHamiltonian ends w) (isotropicState n ρ) := (isotropic_energy_relation ends hends w ρ hρ htr).symm
    _ = _ := isotropic_qmc_energy ends hends w ρ hρ htr

theorem ground_lower_edges {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ)
    (ρR : Matrix (Reg n) (Reg n) ℂ) (hR : GroundDensity (secondaryHamiltonian ends w) ρR)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    -(1/4:ℝ)*(∑ e,w e*(1-3*tParam ρR (ends e).1 (ends e).2)) ≤ energy (qmcHamiltonian ends w) ρ := by
  have h := secondary_ground_lower ends hends w ρR hR ρ hρ htr
  rw [secondary_energy] at h
  have he : -(1/4:ℝ)*(∑ e,w e*(1-3*tParam ρR (ends e).1 (ends e).2)) =
      -(1/4:ℝ)*(∑ e,w e)+(3/8:ℝ)*(2*∑ e,w e*tParam ρR (ends e).1 (ends e).2) := by
    rw [weighted_denom_sum]
    ring
  rw [he]
  exact h

theorem eta_ground_lower {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ)
    (ρR : Matrix (Reg n) (Reg n) ℂ) (hR : GroundDensity (secondaryHamiltonian ends w) ρR)
    (ρA : Matrix (Reg n) (Reg n) ℂ) (η : ℝ) (hη : 0<η)
    (hquality : energy (secondaryHamiltonian ends w) ρA≤η*energy (secondaryHamiltonian ends w) ρR)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    -(1/4:ℝ)*(∑ e,w e)+(3/(8*η):ℝ)*energy (secondaryHamiltonian ends w) ρA ≤ energy (qmcHamiltonian ends w) ρ := by
  have hq : energy (secondaryHamiltonian ends w) ρA/η≤energy (secondaryHamiltonian ends w) ρR := by
    apply (div_le_iff₀ hη).2
    simpa only [mul_comm] using hquality
  have hbase := secondary_ground_lower ends hends w ρR hR ρ hρ htr
  calc
    _ = -(1/4:ℝ)*(∑ e,w e)+(3/8:ℝ)*(energy (secondaryHamiltonian ends w) ρA/η) := by ring
    _ ≤ -(1/4:ℝ)*(∑ e,w e)+(3/8:ℝ)*energy (secondaryHamiltonian ends w) ρR := by linarith
    _ ≤ _ := hbase

theorem eta_lower_edges {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ)
    (ρR : Matrix (Reg n) (Reg n) ℂ) (hR : GroundDensity (secondaryHamiltonian ends w) ρR)
    (ρA : Matrix (Reg n) (Reg n) ℂ) (η : ℝ) (hη : 0<η)
    (hquality : energy (secondaryHamiltonian ends w) ρA≤η*energy (secondaryHamiltonian ends w) ρR)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    -(1/4:ℝ)*(∑ e,w e*(1-(3/η)*tParam ρA (ends e).1 (ends e).2)) ≤ energy (qmcHamiltonian ends w) ρ := by
  have h := eta_ground_lower ends hends w ρR hR ρA η hη hquality ρ hρ htr
  rw [secondary_energy] at h
  have he : -(1/4:ℝ)*(∑ e,w e*(1-(3/η)*tParam ρA (ends e).1 (ends e).2)) =
      -(1/4:ℝ)*(∑ e,w e)+(3/(8*η):ℝ)*(2*∑ e,w e*tParam ρA (ends e).1 (ends e).2) := by
    rw [weighted_denom_sum]
    ring
  rw [he]
  exact h

theorem eta_lower_clipped {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ) (hw : ∀ e,0≤w e)
    (ρR : Matrix (Reg n) (Reg n) ℂ) (hR : GroundDensity (secondaryHamiltonian ends w) ρR)
    (ρA : Matrix (Reg n) (Reg n) ℂ) (η : ℝ) (hη : 0<η)
    (hquality : energy (secondaryHamiltonian ends w) ρA≤η*energy (secondaryHamiltonian ends w) ρR)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    -(1/4:ℝ)*(∑ e,w e*max (1-(3/η)*tParam ρA (ends e).1 (ends e).2) 0) ≤ energy (qmcHamiltonian ends w) ρ := by
  have hbase := eta_lower_edges ends hends w ρR hR ρA η hη hquality ρ hρ htr
  have hs : (∑ e,w e*(1-(3/η)*tParam ρA (ends e).1 (ends e).2)) ≤
      ∑ e,w e*max (1-(3/η)*tParam ρA (ends e).1 (ends e).2) 0 :=
    Finset.sum_le_sum (fun e _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hw e))
  linarith
end Qatlib.Papers.RydbergMaxCut26.StateBounds.Variational
