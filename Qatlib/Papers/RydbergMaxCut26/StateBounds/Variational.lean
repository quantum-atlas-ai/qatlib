/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.StateBounds.CliffordIsotropy

/-!
# Variational QMC bounds from secondary energies

The predicate `GroundDensity` expresses physicality and global energy minimality among density
matrices. Isotropic averaging converts a secondary ground energy into a QMC lower bound; the
variants `eta_ground_lower`, `eta_lower_edges`, and `eta_lower_clipped` incorporate a positive
energy-quality parameter. See [CrostaSaubanereHuber2026].

## Main statements

* `secondary_ground_lower`: derives a QMC lower bound from a secondary ground density.
* `eta_lower_edges`: writes the quality-dependent bound as an edge sum.
* `eta_lower_clipped`: gives the clipped bound for nonnegative weights.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

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

/-- The condition that `ρ` is positive semidefinite, has trace one, and minimizes the energy of
`H` among all density matrices. -/
def GroundDensity {I : Type*} [Fintype I] (H ρ : Matrix I I ℂ) : Prop :=
  ρ.PosSemidef ∧ ρ.trace=1 ∧ ∀ σ : Matrix I I ℂ, σ.PosSemidef → σ.trace=1 → energy H ρ≤energy H σ

/-- The weighted sum of `1 - c * t` equals the total weight minus `c` times the weighted sum of
`t`. -/
theorem weighted_denom_sum {E : Type*} [Fintype E] (w t : E → ℝ) (c : ℝ) :
    (∑ e,w e*(1-c*t e))=(∑ e,w e)-c*(∑ e,w e*t e) := by
  have he : ∀ e,w e*(1-c*t e)=w e-c*(w e*t e) := by intro e;ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum]

/-- For distinct edge endpoints, minus one quarter of the total weight plus three eighths of the
secondary ground energy bounds below the QMC energy of every physical density; see
[CrostaSaubanereHuber2026]. -/
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

/-- For distinct edge endpoints and a secondary ground density, `-1/4 * ∑ e, w e * (1 - 3 *
tParam ρR i j)` bounds below every physical QMC energy. -/
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

/-- For positive `η`, if the secondary energy of `ρA` is at most `η` times the secondary ground
energy, then minus one quarter of the total weight plus `3 / (8 * η)` times the energy of
`ρA` bounds below every physical QMC energy. -/
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

/-- Under the positive-`η` secondary energy-quality inequality, the weighted expression `-1/4 *
∑ e, w e * (1 - (3 / η) * tParam ρA i j)` bounds below every physical QMC energy. -/
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

/-- Under the positive-`η` secondary energy-quality inequality and nonnegative edge weights,
replacing each edge factor by `max (1 - (3 / η) * tParam ρA i j) 0` gives a QMC lower bound;
see [CrostaSaubanereHuber2026]. -/
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
