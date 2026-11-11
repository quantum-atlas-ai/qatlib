/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.MomentSdp.PauliRotation

/-!
# Phase averaging and the source moment matrix

`phaseState` averages a register matrix with its common phase rotation, equalizing distinct-site
XX and YY correlations while preserving their average and the relevant graph energies.
`sourceSDP` is the real X/Y moment matrix of this averaged state; physical inputs yield a
positive semidefinite matrix with unit diagonal and entries matching `tParam`.

These results support the development of [CrostaSaubanereHuber2026].

## Main statements

* `phase_secondary_energy` and `phase_qmc_energy`: preserve the two graph energies.
* `sourceSDP_pos` and `sourceSDP_diag`: establish moment-matrix feasibility.
* `sourceSDP_xx` and `sourceSDP_yy`: identify the fitted correlations.

## References

* [Crosta et al., 2026][CrostaSaubanereHuber2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Matrix
open Qatlib
open Qatlib.Foundations.PureStateMath
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.MomentSdp.Phase
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.EnergyBounds
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.Gram
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.Rotation
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.DensityMoment

/-- The equal mixture of `ρ` and its global phase rotation. -/
noncomputable def phaseState (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  (1/2:ℝ) • (ρ+rotate n phase ρ)

/-- Phase averaging preserves positive semidefiniteness and trace one. -/
theorem phase_density (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    (phaseState n ρ).PosSemidef ∧ (phaseState n ρ).trace=1 := by
  have hr := rotate_density n phase phase_unitary ρ hρ htr
  refine ⟨(hρ.add hr.1).smul (by norm_num : (0:ℝ)≤1/2),?_⟩
  norm_num [phaseState,Matrix.trace_smul,Matrix.trace_add,htr,hr.2]

/-- Every correlation of the phase-averaged matrix is the arithmetic mean of the original and
phase-rotated correlations. -/
theorem phase_corr (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (i j : Fin n) (a : Fin 3) :
    corr (phaseState n ρ) i j a=(corr ρ i j a+corr (rotate n phase ρ) i j a)/2 := by
  simp [corr,phaseState,Matrix.mul_add,Matrix.trace_add,Matrix.trace_smul]
  ring

/-- At distinct sites, the XX correlation of the phase-averaged matrix equals the original
parameter `tParam`. -/
theorem phase_xx (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (i j : Fin n) (hij : i≠j) :
    corr (phaseState n ρ) i j 0=tParam ρ i j := by
  rw [phase_corr,phase_corr_x n i j hij]
  rfl

/-- At distinct sites, the YY correlation of the phase-averaged matrix equals the original
parameter `tParam`. -/
theorem phase_yy (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (i j : Fin n) (hij : i≠j) :
    corr (phaseState n ρ) i j 1=tParam ρ i j := by
  rw [phase_corr,phase_corr_y n i j hij]
  dsimp only [tParam]
  ring

/-- At distinct sites, phase averaging preserves the ZZ correlation. -/
theorem phase_zz (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (i j : Fin n) (hij : i≠j) :
    corr (phaseState n ρ) i j 2=corr ρ i j 2 := by
  rw [phase_corr,phase_corr_z n i j hij]
  ring

/-- At distinct sites, phase averaging preserves `tParam`. -/
theorem phase_t (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (i j : Fin n) (hij : i≠j) :
    tParam (phaseState n ρ) i j=tParam ρ i j := by
  rw [tParam,phase_xx n ρ i j hij,phase_yy n ρ i j hij]
  ring

/-- The weighted secondary Hamiltonian obtained by summing the XX and YY pair operators on each
edge. -/
noncomputable def secondaryHamiltonian {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (w : E → ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  ∑ e, w e • (pairPauli (ends e).1 (ends e).2 0+pairPauli (ends e).1 (ends e).2 1)

/-- The secondary energy equals twice the weighted sum of the edge parameters `tParam`. -/
theorem secondary_energy {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (w : E → ℝ) (ρ : Matrix (Reg n) (Reg n) ℂ) :
    energy (secondaryHamiltonian ends w) ρ=2*∑ e, w e*tParam ρ (ends e).1 (ends e).2 := by
  simp only [secondaryHamiltonian,energy,tParam,corr,Matrix.sum_mul,Matrix.trace_sum,
    Matrix.add_mul,Matrix.trace_add,Complex.re_sum,Matrix.smul_mul,Matrix.trace_smul,
    Complex.smul_re,Complex.add_re,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- Phase averaging preserves the secondary Hamiltonian energy when every edge has distinct
endpoints. -/
theorem phase_secondary_energy {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ)
    (ρ : Matrix (Reg n) (Reg n) ℂ) :
    energy (secondaryHamiltonian ends w) (phaseState n ρ)=energy (secondaryHamiltonian ends w) ρ := by
  rw [secondary_energy,secondary_energy]
  simp_rw [phase_t n ρ _ _ (hends _)]

/-- For a positive semidefinite trace-one matrix and distinct-site edges, phase averaging
preserves QMC energy. -/
theorem phase_qmc_energy {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    energy (qmcHamiltonian ends w) (phaseState n ρ)=energy (qmcHamiltonian ends w) ρ := by
  rw [qmc_energy_sum,qmc_energy_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [energy_smul,energy_smul,energy_edge _ (phase_density n ρ hρ htr).2,energy_edge _ htr,
    phase_xx n ρ _ _ (hends e),phase_yy n ρ _ _ (hends e),phase_zz n ρ _ _ (hends e)]
  dsimp only [tParam]
  ring

/-- The single-site X/Y Pauli family indexed by `MomentIndex n`. -/
noncomputable def sourcePaulis (n : ℕ) (a : MomentIndex n) : Matrix (Reg n) (Reg n) ℂ :=
  sitePauli n a.1 (Fin.castLE (by decide : 2≤3) a.2)

/-- Every source Pauli operator satisfies the unitary identity `(sourcePaulis n a)ᴴ *
sourcePaulis n a = 1`. -/
theorem source_unitary (n : ℕ) (a : MomentIndex n) : (sourcePaulis n a)ᴴ*sourcePaulis n a=1 :=
  site_unitary n _ _

/-- The real moment matrix of the source X/Y Pauli family against `phaseState n ρ`. -/
noncomputable def sourceSDP (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) :
    Matrix (MomentIndex n) (MomentIndex n) ℝ := realMoment (sourcePaulis n) (phaseState n ρ)

/-- For a physical density matrix, `sourceSDP` is positive semidefinite, providing the source
moment completion of [CrostaSaubanereHuber2026]. -/
theorem sourceSDP_pos (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    (sourceSDP n ρ).PosSemidef :=
  realMoment_posSemidef _ _ (phase_density n ρ hρ htr).1

/-- For a physical density matrix, every diagonal entry of `sourceSDP` is one, as required by
the completion in [CrostaSaubanereHuber2026]. -/
theorem sourceSDP_diag (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (a : MomentIndex n) : sourceSDP n ρ a a=1 :=
  realMoment_diag _ (source_unitary n) _ (phase_density n ρ hρ htr).2 a

/-- A real scalar relation between source Pauli products induces the same relation between
entries of `sourceSDP`. -/
theorem sourceSDP_relation (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ)
    (a b c d : MomentIndex n) (s : ℝ)
    (hrel : (sourcePaulis n a)ᴴ*sourcePaulis n b=s • ((sourcePaulis n c)ᴴ*sourcePaulis n d)) :
    sourceSDP n ρ a b=s*sourceSDP n ρ c d :=
  realMoment_relation _ _ a b c d s hrel

/-- For distinct sites, the axis-zero source moment entry equals `tParam ρ i j`. -/
theorem sourceSDP_xx (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (i j : Fin n) (hij : i≠j) :
    sourceSDP n ρ (i,0) (j,0)=tParam ρ i j := by
  change (((sitePauli n i 0)ᴴ*sitePauli n j 0*phaseState n ρ).trace).re=tParam ρ i j
  rw [site_hermitian,site_pair n i j hij]
  exact phase_xx n ρ i j hij

/-- For distinct sites, the axis-one source moment entry equals `tParam ρ i j`. -/
theorem sourceSDP_yy (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (i j : Fin n) (hij : i≠j) :
    sourceSDP n ρ (i,1) (j,1)=tParam ρ i j := by
  change (((sitePauli n i 1)ᴴ*sitePauli n j 1*phaseState n ρ).trace).re=tParam ρ i j
  rw [site_hermitian,site_pair n i j hij]
  exact phase_yy n ρ i j hij
end Qatlib.Papers.RydbergMaxCut26.MomentSdp.Phase
