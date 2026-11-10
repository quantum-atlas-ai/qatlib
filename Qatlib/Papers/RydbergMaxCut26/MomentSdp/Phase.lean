/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.MomentSdp.PauliRotation
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

noncomputable def phaseState (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  (1/2:ℝ) • (ρ+rotate n phase ρ)

theorem phase_density (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    (phaseState n ρ).PosSemidef ∧ (phaseState n ρ).trace=1 := by
  have hr := rotate_density n phase phase_unitary ρ hρ htr
  refine ⟨(hρ.add hr.1).smul (by norm_num : (0:ℝ)≤1/2),?_⟩
  norm_num [phaseState,Matrix.trace_smul,Matrix.trace_add,htr,hr.2]

theorem phase_corr (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (i j : Fin n) (a : Fin 3) :
    corr (phaseState n ρ) i j a=(corr ρ i j a+corr (rotate n phase ρ) i j a)/2 := by
  simp [corr,phaseState,Matrix.mul_add,Matrix.trace_add,Matrix.trace_smul]
  ring

theorem phase_xx (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (i j : Fin n) (hij : i≠j) :
    corr (phaseState n ρ) i j 0=tParam ρ i j := by
  rw [phase_corr,phase_corr_x n i j hij]
  rfl

theorem phase_yy (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (i j : Fin n) (hij : i≠j) :
    corr (phaseState n ρ) i j 1=tParam ρ i j := by
  rw [phase_corr,phase_corr_y n i j hij]
  dsimp only [tParam]
  ring

theorem phase_zz (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (i j : Fin n) (hij : i≠j) :
    corr (phaseState n ρ) i j 2=corr ρ i j 2 := by
  rw [phase_corr,phase_corr_z n i j hij]
  ring

theorem phase_t (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (i j : Fin n) (hij : i≠j) :
    tParam (phaseState n ρ) i j=tParam ρ i j := by
  rw [tParam,phase_xx n ρ i j hij,phase_yy n ρ i j hij]
  ring

noncomputable def secondaryHamiltonian {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (w : E → ℝ) : Matrix (Reg n) (Reg n) ℂ :=
  ∑ e, w e • (pairPauli (ends e).1 (ends e).2 0+pairPauli (ends e).1 (ends e).2 1)

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

theorem phase_secondary_energy {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ)
    (ρ : Matrix (Reg n) (Reg n) ℂ) :
    energy (secondaryHamiltonian ends w) (phaseState n ρ)=energy (secondaryHamiltonian ends w) ρ := by
  rw [secondary_energy,secondary_energy]
  simp_rw [phase_t n ρ _ _ (hends _)]

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

noncomputable def sourcePaulis (n : ℕ) (a : MomentIndex n) : Matrix (Reg n) (Reg n) ℂ :=
  sitePauli n a.1 (Fin.castLE (by decide : 2≤3) a.2)

theorem source_unitary (n : ℕ) (a : MomentIndex n) : (sourcePaulis n a)ᴴ*sourcePaulis n a=1 :=
  site_unitary n _ _

noncomputable def sourceSDP (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) :
    Matrix (MomentIndex n) (MomentIndex n) ℝ := realMoment (sourcePaulis n) (phaseState n ρ)

theorem sourceSDP_pos (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    (sourceSDP n ρ).PosSemidef :=
  realMoment_posSemidef _ _ (phase_density n ρ hρ htr).1

theorem sourceSDP_diag (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (a : MomentIndex n) : sourceSDP n ρ a a=1 :=
  realMoment_diag _ (source_unitary n) _ (phase_density n ρ hρ htr).2 a

theorem sourceSDP_relation (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ)
    (a b c d : MomentIndex n) (s : ℝ)
    (hrel : (sourcePaulis n a)ᴴ*sourcePaulis n b=s • ((sourcePaulis n c)ᴴ*sourcePaulis n d)) :
    sourceSDP n ρ a b=s*sourceSDP n ρ c d :=
  realMoment_relation _ _ a b c d s hrel

theorem sourceSDP_xx (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (i j : Fin n) (hij : i≠j) :
    sourceSDP n ρ (i,0) (j,0)=tParam ρ i j := by
  change (((sitePauli n i 0)ᴴ*sitePauli n j 0*phaseState n ρ).trace).re=tParam ρ i j
  rw [site_hermitian,site_pair n i j hij]
  exact phase_xx n ρ i j hij

theorem sourceSDP_yy (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (i j : Fin n) (hij : i≠j) :
    sourceSDP n ρ (i,1) (j,1)=tParam ρ i j := by
  change (((sitePauli n i 1)ᴴ*sitePauli n j 1*phaseState n ρ).trace).re=tParam ρ i j
  rw [site_hermitian,site_pair n i j hij]
  exact phase_yy n ρ i j hij
end Qatlib.Papers.RydbergMaxCut26.MomentSdp.Phase
