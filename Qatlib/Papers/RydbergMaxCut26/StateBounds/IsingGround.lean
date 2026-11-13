/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.StateBounds.XProductBasis
import Qatlib.Papers.RydbergMaxCut26.StateBounds.Variational

/-!
# Ising ground states in the X product basis

The Ising Hamiltonian `isingHamiltonian` has the explicit X product-basis spectral decomposition
given by `classicalEnergy`. Choosing a minimizing spin configuration produces a ground density
matrix and an upper bound on its QMC energy in terms of the edge parameters of any physical
comparison state. See [CrostaSaubanereHuber2026].

## Main statements

* `actual_ising_ground`: constructs an Ising ground density from a minimizing spin assignment.
* `actual_ideal_product_upper`: bounds the QMC energy of this X product state.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open Matrix Qatlib
open Qatlib.Foundations.PureStateMath
open scoped Classical ComplexOrder
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Bloch
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.EnergyBounds
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.Phase
open Qatlib.Papers.RydbergMaxCut26.StateBounds.Variational
open Qatlib.Papers.RydbergMaxCut26.StateBounds.XBasis

namespace Qatlib.Papers.RydbergMaxCut26.StateBounds.Ising

/-- The weighted sum of the XX Pauli interactions over the graph edges. -/
def isingHamiltonian {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (w : E → ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  ∑ e,w e • pairPauli (ends e).1 (ends e).2 0

/-- The weighted classical spin energy, summing the products of endpoint signs over the edges. -/
def classicalEnergy {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (w : E → ℝ) (s : Reg n) : ℝ :=
  ∑ e,w e*(sign (s (ends e).1)*sign (s (ends e).2))

/-- For distinct edge endpoints, `xDensity s` is an Ising eigendensity with eigenvalue
`classicalEnergy ends w s`. -/
theorem ising_eigen {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ) (s : Reg n) :
    isingHamiltonian ends w*xDensity s=classicalEnergy ends w s • xDensity s := by
  rw [isingHamiltonian,Matrix.sum_mul]
  have he (e : E) : (w e • pairPauli (ends e).1 (ends e).2 0)*xDensity s=
      (w e*(sign (s (ends e).1)*sign (s (ends e).2))) • xDensity s := by
    rw [Matrix.smul_mul,pair_x_eigen s _ _ (hends e),smul_smul]
  simp_rw [he]
  rw [← Finset.sum_smul]
  rfl

/-- For distinct edge endpoints, the Ising Hamiltonian is the sum of the X product-basis
projectors weighted by their classical spin energies. -/
theorem ising_spectral {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ) :
    isingHamiltonian ends w=∑ s : Reg n,classicalEnergy ends w s • xDensity s := by
  calc
    _ = isingHamiltonian ends w*1 := (Matrix.mul_one _).symm
    _ = isingHamiltonian ends w*(∑ s : Reg n,xDensity s) := by rw [x_resolution]
    _ = ∑ s : Reg n,isingHamiltonian ends w*xDensity s := by rw [Matrix.mul_sum]
    _ = _ := Finset.sum_congr rfl (fun s _ => ising_eigen ends hends w s)

/-- For distinct edge endpoints, the Ising energy of `xDensity s` equals its classical spin
energy. -/
theorem ising_x_energy {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ) (s : Reg n) :
    energy (isingHamiltonian ends w) (xDensity s)=classicalEnergy ends w s := by
  rw [energy,ising_eigen ends hends w s,Matrix.trace_smul,(x_density s).2]
  simp

/-- For distinct edge endpoints, the Ising energy of a matrix is the sum of classical spin
energies weighted by its X-basis trace pairings. -/
theorem ising_born_mean {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ)
    (ρ : Matrix (Reg n) (Reg n) ℂ) :
    energy (isingHamiltonian ends w) ρ=
      ∑ s : Reg n,classicalEnergy ends w s*(xDensity s*ρ).trace.re := by
  rw [energy,ising_spectral ends hends w]
  simp only [Matrix.sum_mul,Matrix.smul_mul,Matrix.trace_sum,Matrix.trace_smul,
    Complex.re_sum,Complex.smul_re,smul_eq_mul]

/-- A spin assignment minimizing the classical energy exists on the finite register. -/
theorem exists_classical_min {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (w : E → ℝ) :
    ∃ s : Reg n,∀ u : Reg n,classicalEnergy ends w s≤classicalEnergy ends w u := by
  obtain ⟨s,_hs,he⟩ :=
      Finset.exists_mem_eq_inf' (s:=Finset.univ) Finset.univ_nonempty (classicalEnergy ends w)
  refine ⟨s,fun u => ?_⟩
  rw [← he]
  exact Finset.inf'_le _ (Finset.mem_univ u)

/-- A choice of spin assignment minimizing the classical energy. -/
def minSpin {n : ℕ} {E : Type*} [Fintype E] (ends : E → Fin n×Fin n) (w : E → ℝ) : Reg n :=
  Classical.choose (exists_classical_min ends w)

/-- The selected spin assignment has classical energy at most that of every other assignment. -/
theorem minSpin_le {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (w : E → ℝ) (u : Reg n) :
    classicalEnergy ends w (minSpin ends w)≤classicalEnergy ends w u :=
  Classical.choose_spec (exists_classical_min ends w) u

/-- For distinct edge endpoints, the X product density of the selected minimizing assignment is
an Ising ground density, as in [Crosta et al., Appendix D][CrostaSaubanereHuber2026]. -/
theorem actual_ising_ground {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ) :
    GroundDensity (isingHamiltonian ends w) (xDensity (minSpin ends w)) := by
  refine ⟨(x_density _).1,(x_density _).2,?_⟩
  intro ρ hρ htr
  rw [ising_x_energy ends hends w,ising_born_mean ends hends w]
  calc
    _ = classicalEnergy ends w (minSpin ends w)*1 := by ring
    _ = classicalEnergy ends w (minSpin ends w)*(∑ s : Reg n,(xDensity s*ρ).trace.re) := by rw [x_born_sum ρ htr]
    _ = ∑ s : Reg n,classicalEnergy ends w (minSpin ends w)*(xDensity s*ρ).trace.re := Finset.mul_sum _ _ _
    _ ≤ _ := Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_right (minSpin_le ends w s) (x_born_nonneg ρ hρ s))

/-- For distinct edge endpoints, the QMC energy of an X product density equals `-(1/4) * ((∑ e,
w e) - classicalEnergy ends w s)`. -/
theorem qmc_x_energy {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ) (s : Reg n) :
    energy (qmcHamiltonian ends w) (xDensity s)=-(1/4:ℝ)*((∑ e,w e)-classicalEnergy ends w s) := by
  rw [qmc_energy_sum]
  have he (e : E) : w e*energy ((-1/4:ℝ) • edgeOperator (ends e).1 (ends e).2) (xDensity s)=
      -(1/4:ℝ)*(w e-w e*(sign (s (ends e).1)*sign (s (ends e).2))) := by
    rw [energy_smul,energy_edge _ (x_density s).2]
    have hc := x_correlations s (ends e).1 (ends e).2 (hends e)
    rw [hc.1,hc.2.1,hc.2.2]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum,Finset.sum_sub_distrib]
  rfl

/-- For distinct edge endpoints, the Ising energy of the phase-averaged matrix is the sum of
edge weights multiplied by the original `tParam` values. -/
theorem phase_ising_energy {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ)
    (ρ : Matrix (Reg n) (Reg n) ℂ) :
    energy (isingHamiltonian ends w) (phaseState n ρ)=∑ e,w e*tParam ρ (ends e).1 (ends e).2 := by
  simp only [energy,isingHamiltonian,Matrix.sum_mul,Matrix.smul_mul,Matrix.trace_sum,
    Matrix.trace_smul,Complex.re_sum,Complex.smul_re,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro e _
  exact congrArg (fun z => w e*z) (phase_xx n ρ _ _ (hends e))

/-- For any physical comparison state and distinct edge endpoints, the QMC energy of the
minimizing X product density is at most `-1/4` times the weighted sum of `1 - tParam`, as in
[Crosta et al., Appendix D][CrostaSaubanereHuber2026]. -/
theorem actual_ideal_product_upper {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ)
    (ρR : Matrix (Reg n) (Reg n) ℂ) (hρR : ρR.PosSemidef) (htrR : ρR.trace=1) :
    energy (qmcHamiltonian ends w) (xDensity (minSpin ends w))≤
      -(1/4:ℝ)*(∑ e,w e*(1-tParam ρR (ends e).1 (ends e).2)) := by
  have hd := phase_density n ρR hρR htrR
  have hmin := (actual_ising_ground ends hends w).2.2 (phaseState n ρR) hd.1 hd.2
  rw [ising_x_energy ends hends w,phase_ising_energy ends hends w] at hmin
  have hden : (∑ e,w e*(1-tParam ρR (ends e).1 (ends e).2))=
      (∑ e,w e)-(∑ e,w e*tParam ρR (ends e).1 (ends e).2) := by
    simpa only [one_mul] using weighted_denom_sum w (fun e => tParam ρR (ends e).1 (ends e).2) 1
  rw [qmc_x_energy ends hends w,hden]
  linarith

end Qatlib.Papers.RydbergMaxCut26.StateBounds.Ising
