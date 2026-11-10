/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RydbergMaxCut26.MomentSdp.Phase
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Matrix
open Qatlib
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ChannelTheory.Stinespring
open scoped Classical ComplexOrder
namespace Qatlib.Papers.RydbergMaxCut26.StateBounds.Clifford
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.Graph
open Qatlib.Papers.RydbergMaxCut26.QubitPhysics.EnergyBounds
open Qatlib.Papers.RydbergMaxCut26.MomentSdp.Rotation Qatlib.Papers.RydbergMaxCut26.MomentSdp.Phase

noncomputable def cycleGate : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1-Complex.I)/2,(-1-Complex.I)/2;(1-Complex.I)/2,(1+Complex.I)/2]

theorem cycle_unitary : cycleGate ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have htwo : (starRingEnd ℂ) (2:ℂ)=2 := Complex.conj_ofNat 2
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycleGate,Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply] <;> ring_nf <;> norm_num [Complex.I_sq,htwo]

theorem cycle_x : cycleGateᴴ*pauliMatrix 0*cycleGate=pauliMatrix 2 := by
  have htwo : (starRingEnd ℂ) (2:ℂ)=2 := Complex.conj_ofNat 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycleGate,pauliMatrix,pauliX,pauliZ,Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply] <;> ring_nf <;> norm_num [Complex.I_sq,htwo]

theorem cycle_y : cycleGateᴴ*pauliMatrix 1*cycleGate=pauliMatrix 0 := by
  have htwo : (starRingEnd ℂ) (2:ℂ)=2 := Complex.conj_ofNat 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycleGate,pauliMatrix,pauliX,pauliY,Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply] <;> ring_nf <;> norm_num [Complex.I_sq,htwo]

theorem cycle_z : cycleGateᴴ*pauliMatrix 2*cycleGate=pauliMatrix 1 := by
  have htwo : (starRingEnd ℂ) (2:ℂ)=2 := Complex.conj_ofNat 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cycleGate,pauliMatrix,pauliY,pauliZ,Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply] <;> ring_nf <;> norm_num [Complex.I_sq,htwo]
  all_goals ring

theorem cycle_corr_x (n : ℕ) (i j : Fin n) (hij : i≠j) (ρ : Matrix (Reg n) (Reg n) ℂ) :
    corr (rotate n cycleGate ρ) i j 0=corr ρ i j 2 := by
  rw [corr,rotated_trace,pair_conjugate n i j hij cycleGate cycle_unitary 0 2 1 (by norm_num) (by simpa using cycle_x)]
  rfl

theorem cycle_corr_y (n : ℕ) (i j : Fin n) (hij : i≠j) (ρ : Matrix (Reg n) (Reg n) ℂ) :
    corr (rotate n cycleGate ρ) i j 1=corr ρ i j 0 := by
  rw [corr,rotated_trace,pair_conjugate n i j hij cycleGate cycle_unitary 1 0 1 (by norm_num) (by simpa using cycle_y)]
  rfl

theorem cycle_corr_z (n : ℕ) (i j : Fin n) (hij : i≠j) (ρ : Matrix (Reg n) (Reg n) ℂ) :
    corr (rotate n cycleGate ρ) i j 2=corr ρ i j 1 := by
  rw [corr,rotated_trace,pair_conjugate n i j hij cycleGate cycle_unitary 2 1 1 (by norm_num) (by simpa using cycle_z)]
  rfl

noncomputable def isotropicState (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) : Matrix (Reg n) (Reg n) ℂ :=
  (1/3:ℝ) • (ρ+rotate n cycleGate ρ+rotate n cycleGate (rotate n cycleGate ρ))

theorem isotropic_density (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    (isotropicState n ρ).PosSemidef ∧ (isotropicState n ρ).trace=1 := by
  have h1 := rotate_density n cycleGate cycle_unitary ρ hρ htr
  have h2 := rotate_density n cycleGate cycle_unitary _ h1.1 h1.2
  refine ⟨((hρ.add h1.1).add h2.1).smul (by norm_num : (0:ℝ)≤1/3),?_⟩
  norm_num [isotropicState,Matrix.trace_smul,Matrix.trace_add,htr,h1.2,h2.2]

noncomputable def meanCorrelation {n : ℕ} (ρ : Matrix (Reg n) (Reg n) ℂ) (i j : Fin n) : ℝ :=
  (corr ρ i j 0+corr ρ i j 1+corr ρ i j 2)/3

theorem isotropic_xx (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (i j : Fin n) (hij : i≠j) :
    corr (isotropicState n ρ) i j 0=meanCorrelation ρ i j := by
  have hlin : corr (isotropicState n ρ) i j 0=
      (corr ρ i j 0+corr (rotate n cycleGate ρ) i j 0+
        corr (rotate n cycleGate (rotate n cycleGate ρ)) i j 0)/3 := by
    simp [corr,isotropicState,Matrix.mul_add,Matrix.trace_add,Matrix.trace_smul]
    ring
  rw [hlin,cycle_corr_x n i j hij,cycle_corr_x n i j hij,cycle_corr_z n i j hij]
  dsimp only [meanCorrelation]
  ring

theorem isotropic_yy (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (i j : Fin n) (hij : i≠j) :
    corr (isotropicState n ρ) i j 1=meanCorrelation ρ i j := by
  have hlin : corr (isotropicState n ρ) i j 1=
      (corr ρ i j 1+corr (rotate n cycleGate ρ) i j 1+
        corr (rotate n cycleGate (rotate n cycleGate ρ)) i j 1)/3 := by
    simp [corr,isotropicState,Matrix.mul_add,Matrix.trace_add,Matrix.trace_smul]
    ring
  rw [hlin,cycle_corr_y n i j hij,cycle_corr_y n i j hij,cycle_corr_x n i j hij]
  dsimp only [meanCorrelation]
  ring

theorem isotropic_zz (n : ℕ) (ρ : Matrix (Reg n) (Reg n) ℂ) (i j : Fin n) (hij : i≠j) :
    corr (isotropicState n ρ) i j 2=meanCorrelation ρ i j := by
  have hlin : corr (isotropicState n ρ) i j 2=
      (corr ρ i j 2+corr (rotate n cycleGate ρ) i j 2+
        corr (rotate n cycleGate (rotate n cycleGate ρ)) i j 2)/3 := by
    simp [corr,isotropicState,Matrix.mul_add,Matrix.trace_add,Matrix.trace_smul]
    ring
  rw [hlin,cycle_corr_z n i j hij,cycle_corr_z n i j hij,cycle_corr_y n i j hij]
  dsimp only [meanCorrelation]
  ring

theorem isotropic_qmc_energy {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    energy (qmcHamiltonian ends w) (isotropicState n ρ)=energy (qmcHamiltonian ends w) ρ := by
  rw [qmc_energy_sum,qmc_energy_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [energy_smul,energy_smul,energy_edge _ (isotropic_density n ρ hρ htr).2,energy_edge _ htr,
    isotropic_xx n ρ _ _ (hends e),isotropic_yy n ρ _ _ (hends e),isotropic_zz n ρ _ _ (hends e)]
  dsimp only [meanCorrelation]
  ring

theorem isotropic_energy_relation {n : ℕ} {E : Type*} [Fintype E]
    (ends : E → Fin n×Fin n) (hends : ∀ e,(ends e).1≠(ends e).2) (w : E → ℝ)
    (ρ : Matrix (Reg n) (Reg n) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) :
    energy (qmcHamiltonian ends w) (isotropicState n ρ)=
      -(1/4:ℝ)*(∑ e,w e)+(3/8:ℝ)*energy (secondaryHamiltonian ends w) (isotropicState n ρ) := by
  rw [qmc_energy_sum,secondary_energy]
  simp_rw [energy_smul,energy_edge _ (isotropic_density n ρ hρ htr).2,
    isotropic_xx n ρ _ _ (hends _),isotropic_yy n ρ _ _ (hends _),isotropic_zz n ρ _ _ (hends _)]
  have ht : ∀ e, tParam (isotropicState n ρ) (ends e).1 (ends e).2=meanCorrelation ρ (ends e).1 (ends e).2 := by
    intro e
    rw [tParam,isotropic_xx n ρ _ _ (hends e),isotropic_yy n ρ _ _ (hends e)]
    ring
  simp_rw [ht]
  have he : ∀ e, w e*((-1/4:ℝ)*(1-(meanCorrelation ρ (ends e).1 (ends e).2+
      meanCorrelation ρ (ends e).1 (ends e).2+meanCorrelation ρ (ends e).1 (ends e).2))) =
      (-1/4:ℝ)*w e+(3/4:ℝ)*(w e*meanCorrelation ρ (ends e).1 (ends e).2) := by
    intro e
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  ring
end Qatlib.Papers.RydbergMaxCut26.StateBounds.Clifford
