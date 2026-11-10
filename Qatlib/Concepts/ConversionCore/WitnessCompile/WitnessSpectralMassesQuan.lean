/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.WitnessCompile.WitnessSpectralMassesStat
import Qatlib.Concepts.ConversionCore.WitnessCompile.EffectiveSpectralGapQuan
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.AlphabetWitnessGeometryQuan
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.NoncommRing
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.BlockEncoding.EncodingCore

namespace Qatlib.Concepts.ConversionCore.WitnessCompile
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators ComplexOrder

theorem sourcePhaseProjector_isOrthogonalProjector {H : Type} [Fintype H] [DecidableEq H]
    (V : Matrix H H ℂ) (hV : V ∈ Matrix.unitaryGroup H ℂ) (angles : H → ℝ) (Θ : ℝ) :
    IsOrthogonalProjector (sourcePhaseProjector V angles Θ) := by
  let D := Matrix.diagonal (fun h => if |angles h| ≤ Θ then (1 : ℂ) else 0)
  have hDD : D*D=D := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext h
    (try dsimp [D])
    split_ifs <;> simp
  have hDH : Dᴴ=D := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext h
    (try dsimp [D])
    split_ifs <;> simp
  have hVV : Vᴴ*V=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hV.1
  constructor
  · change (V*D*Vᴴ)*(V*D*Vᴴ)=V*D*Vᴴ
    calc
      _ = V*(D*((Vᴴ*V)*D))*Vᴴ := by noncomm_ring
      _ = _ := by rw [hVV,Matrix.one_mul,hDD]
  · change (V*D*Vᴴ)ᴴ=V*D*Vᴴ
    simp only [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hDH,Matrix.mul_assoc]

theorem sourcePhaseProjector_basis_norm {H : Type} [Fintype H] [DecidableEq H]
    (V : Matrix H H ℂ) (hV : V ∈ Matrix.unitaryGroup H ℂ) (angles : H → ℝ) (Θ : ℝ)
    (ψ : QState H) :
    ‖toEuclidean_fromVec (sourcePhaseProjector V angles Θ *ᵥ ψ)‖ =
      ‖toEuclidean_fromVec
        (Matrix.diagonal (fun h => if |angles h| ≤ Θ then (1 : ℂ) else 0) *ᵥ (Vᴴ *ᵥ ψ))‖ := by
  have hi : IsIsometry V := by simpa only [Matrix.star_eq_conjTranspose] using! hV.1
  simp only [sourcePhaseProjector,← Matrix.mulVec_mulVec]
  exact isometry_mulVec_norm hi _

theorem sourcePhaseProjector_complement_vec {H : Type} [Fintype H] [DecidableEq H]
    (V : Matrix H H ℂ) (hV : V ∈ Matrix.unitaryGroup H ℂ) (angles : H → ℝ) (Θ : ℝ)
    (ψ : QState H) :
    (1-sourcePhaseProjector V angles Θ) *ᵥ ψ =
      V *ᵥ (Matrix.diagonal (fun h => if |angles h| ≤ Θ then (0 : ℂ) else 1) *ᵥ (Vᴴ *ᵥ ψ)) := by
  have hVV : V*Vᴴ=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hV.2
  let z := Vᴴ *ᵥ ψ
  have hw : V *ᵥ z=ψ := by dsimp [z]; rw [Matrix.mulVec_mulVec,hVV,Matrix.one_mulVec]
  calc
    _ = ψ-V *ᵥ (Matrix.diagonal (fun h => if |angles h| ≤ Θ then (1 : ℂ) else 0) *ᵥ z) := by
      simp only [Matrix.sub_mulVec,Matrix.one_mulVec,sourcePhaseProjector,← Matrix.mulVec_mulVec,z]
    _ = V *ᵥ (z-Matrix.diagonal (fun h => if |angles h| ≤ Θ then (1 : ℂ) else 0) *ᵥ z) := by
      rw [Matrix.mulVec_sub,hw]
    _ = _ := by
      congr 1
      ext h
      simp only [Pi.sub_apply,Matrix.mulVec_diagonal]
      split_ifs <;> simp [z]

theorem sourcePhaseProjector_complement_norm_le {H : Type} [Fintype H] [DecidableEq H]
    (V : Matrix H H ℂ) (hV : V ∈ Matrix.unitaryGroup H ℂ) (angles : H → ℝ) (Θ : ℝ)
    (ψ : QState H) :
    ‖toEuclidean_fromVec ((1-sourcePhaseProjector V angles Θ) *ᵥ ψ)‖ ≤ ‖toEuclidean_fromVec ψ‖ := by
  have hi : IsIsometry V := by simpa only [Matrix.star_eq_conjTranspose] using! hV.1
  have hi' : IsIsometry Vᴴ := by
    change (Vᴴ)ᴴ*Vᴴ=1
    simpa only [Matrix.conjTranspose_conjTranspose,Matrix.star_eq_conjTranspose] using! hV.2
  rw [sourcePhaseProjector_complement_vec V hV,isometry_mulVec_norm hi]
  have hb := source_diagonal_mulVec_bound
    (fun h => if |angles h| ≤ Θ then (0 : ℂ) else 1) 1 (by norm_num)
    (by intro h; (try dsimp only); split_ifs <;> norm_num) (Vᴴ *ᵥ ψ)
  simpa only [one_mul,isometry_mulVec_norm hi'] using! hb

theorem sourcePhaseProjector_pythagoras {H : Type} [Fintype H] [DecidableEq H]
    (V : Matrix H H ℂ) (hV : V ∈ Matrix.unitaryGroup H ℂ) (angles : H → ℝ) (Θ : ℝ)
    (ψ : QState H) :
    ‖toEuclidean_fromVec (sourcePhaseProjector V angles Θ *ᵥ ψ)‖^2+
      ‖toEuclidean_fromVec ((1-sourcePhaseProjector V angles Θ) *ᵥ ψ)‖^2 =
      ‖toEuclidean_fromVec ψ‖^2 := by
  have hi : IsIsometry V := by simpa only [Matrix.star_eq_conjTranspose] using! hV.1
  have hi' : IsIsometry Vᴴ := by
    change (Vᴴ)ᴴ*Vᴴ=1
    simpa only [Matrix.conjTranspose_conjTranspose,Matrix.star_eq_conjTranspose] using! hV.2
  rw [sourcePhaseProjector_basis_norm V hV,sourcePhaseProjector_complement_vec V hV,
    isometry_mulVec_norm hi,← isometry_mulVec_norm hi' ψ]
  rw [norm_toEuclidean_fromVec_sq,norm_toEuclidean_fromVec_sq,norm_toEuclidean_fromVec_sq,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  simp only [Matrix.mulVec_diagonal]
  split_ifs <;> simp

theorem source_branch_exp_eq_one {θ : ℝ} (hθ : -Real.pi < θ ∧ θ ≤ Real.pi) :
    Complex.exp (Complex.I*θ)=1 ↔ θ=0 := by
  constructor
  · intro h
    have heq : Complex.I*(θ : ℂ)=0 := Complex.exp_inj_of_neg_pi_lt_of_le_pi
      (by simpa using! hθ.1) (by simpa using! hθ.2)
      (by simpa using! (neg_lt_zero.mpr Real.pi_pos)) (by simpa using! Real.pi_pos.le)
      (by simpa using! h)
    simpa using! congrArg Complex.im heq
  · intro h
    simp [h]

theorem sourcePhaseProjector_zero_fixed {H : Type} [Fintype H] [DecidableEq H]
    (U V : Matrix H H ℂ) (hV : V ∈ Matrix.unitaryGroup H ℂ) (angles : H → ℝ)
    (ha : ∀ h, -Real.pi < angles h ∧ angles h ≤ Real.pi)
    (hU : U=V*Matrix.diagonal (fun h => Complex.exp (Complex.I*angles h))*Vᴴ)
    (ψ : QState H) (hψ : U *ᵥ ψ=ψ) : sourcePhaseProjector V angles 0 *ᵥ ψ=ψ := by
  let z := Vᴴ *ᵥ ψ
  have hVV : V*Vᴴ=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hV.2
  have hVhV : Vᴴ*V=1 := by simpa only [Matrix.star_eq_conjTranspose] using! hV.1
  have hw : V *ᵥ z=ψ := by dsimp [z]; rw [Matrix.mulVec_mulVec,hVV,Matrix.one_mulVec]
  have heigen : Matrix.diagonal (fun h => Complex.exp (Complex.I*angles h)) *ᵥ z=z := by
    have hh := congrArg (fun f => Vᴴ *ᵥ f) hψ
    rw [hU] at hh
    simp only [← Matrix.mulVec_mulVec] at hh
    change Vᴴ *ᵥ (V *ᵥ (Matrix.diagonal (fun h => Complex.exp (Complex.I*angles h)) *ᵥ z))=z at hh
    rw [Matrix.mulVec_mulVec _ Vᴴ V,hVhV,Matrix.one_mulVec] at hh
    exact hh
  have hcut : Matrix.diagonal (fun h => if |angles h| ≤ 0 then (1 : ℂ) else 0) *ᵥ z=z := by
    ext h
    have hh := congrFun heigen h
    simp only [Matrix.mulVec_diagonal] at hh ⊢
    by_cases hθ : angles h=0
    · simp [hθ]
    · have heig_ne : Complex.exp (Complex.I*angles h)≠1 := fun he => hθ ((source_branch_exp_eq_one (ha h)).mp he)
      have hz : z h=0 := (mul_eq_zero.mp (show (Complex.exp (Complex.I*angles h)-1)*z h=0 by
        rw [sub_mul,one_mul,hh,sub_self])).resolve_left (sub_ne_zero.mpr heig_ne)
      simp [hz]
  simp only [sourcePhaseProjector,← Matrix.mulVec_mulVec]
  rw [hcut,hw]

private theorem source_reflection_fixed {H : Type} [Fintype H] [DecidableEq H]
    (P : Matrix H H ℂ) (ψ : QState H) (h : P *ᵥ ψ=ψ) : ReflectionAbout P *ᵥ ψ=ψ := by
  unfold ReflectionAbout
  rw [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,h]
  simp only [two_smul]
  abel

theorem source_walk_zero_mass {H : Type} [Fintype H] [DecidableEq H]
    (P L V : Matrix H H ℂ) (hV : V ∈ Matrix.unitaryGroup H ℂ)
    (angles : H → ℝ) (ha : ∀ h, -Real.pi < angles h ∧ angles h ≤ Real.pi)
    (hU : ReflectionAbout P*ReflectionAbout L=
      V*Matrix.diagonal (fun h => Complex.exp (Complex.I*angles h))*Vᴴ)
    (ψ φ : QState H) (hφP : P *ᵥ φ=φ) (hφL : L *ᵥ φ=φ)
    (hψ : ‖toEuclidean_fromVec ψ‖^2=1) (ε : ℝ) (hε : 0 ≤ ε)
    (hdistance : ‖toEuclidean_fromVec (φ-ψ)‖^2 ≤ ε^2) :
    1-ε^2 ≤ ‖toEuclidean_fromVec (sourcePhaseProjector V angles 0 *ᵥ ψ)‖^2 := by
  have hwalk : (ReflectionAbout P*ReflectionAbout L) *ᵥ φ=φ := by
    rw [← Matrix.mulVec_mulVec,source_reflection_fixed L φ hφL,source_reflection_fixed P φ hφP]
  have hzeroFixed := sourcePhaseProjector_zero_fixed _ V hV angles ha hU φ hwalk
  have hcompFixed : (1-sourcePhaseProjector V angles 0) *ᵥ φ=0 := by
    rw [Matrix.sub_mulVec,Matrix.one_mulVec,hzeroFixed,sub_self]
  have hcompDifference : (1-sourcePhaseProjector V angles 0) *ᵥ ψ =
      (1-sourcePhaseProjector V angles 0) *ᵥ (ψ-φ) := by
    rw [Matrix.mulVec_sub,hcompFixed,sub_zero]
  have hbound := sourcePhaseProjector_complement_norm_le V hV angles 0 (ψ-φ)
  rw [← hcompDifference] at hbound
  have hnormsym : ‖toEuclidean_fromVec (ψ-φ)‖=‖toEuclidean_fromVec (φ-ψ)‖ := by
    change ‖toEuclidean_fromVec ψ-toEuclidean_fromVec φ‖=
      ‖toEuclidean_fromVec φ-toEuclidean_fromVec ψ‖
    exact norm_sub_rev _ _
  rw [hnormsym] at hbound
  have hdiff : ‖toEuclidean_fromVec (φ-ψ)‖ ≤ ε := by
    nlinarith [norm_nonneg (toEuclidean_fromVec (φ-ψ))]
  have hcomple : ‖toEuclidean_fromVec ((1-sourcePhaseProjector V angles 0) *ᵥ ψ)‖ ≤ ε :=
    le_trans hbound hdiff
  have hpyth := sourcePhaseProjector_pythagoras V hV angles 0 ψ
  rw [hψ] at hpyth
  nlinarith [norm_nonneg (toEuclidean_fromVec ((1-sourcePhaseProjector V angles 0) *ᵥ ψ))]

theorem source_walk_low_mass {H : Type} [Fintype H] [DecidableEq H]
    (P L V : Matrix H H ℂ) (hP : IsOrthogonalProjector P) (hL : IsOrthogonalProjector L)
    (hV : V ∈ Matrix.unitaryGroup H ℂ) (angles : H → ℝ)
    (ha : ∀ h, -Real.pi < angles h ∧ angles h ≤ Real.pi)
    (hU : ReflectionAbout P*ReflectionAbout L=
      V*Matrix.diagonal (fun h => Complex.exp (Complex.I*angles h))*Vᴴ)
    (w ψ : QState H) (hLw : L *ᵥ w=0) (hPw : P *ᵥ w=ψ)
    (C Θ : ℝ) (hC : ‖toEuclidean_fromVec w‖^2 ≤ C) (hΘ : 0 ≤ Θ) :
    ‖toEuclidean_fromVec (sourcePhaseProjector V angles Θ *ᵥ ψ)‖^2 ≤ Θ^2/4*C := by
  have hb := effectiveSpectralGap H P L V angles Θ w hP hL hV ha hU hΘ hLw
  rw [hPw] at hb
  have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hcoef : (Θ/2*‖toEuclidean_fromVec w‖)^2=(Θ^2/4)*‖toEuclidean_fromVec w‖^2 := by ring
  rw [hcoef] at hb2
  exact le_trans hb2 (mul_le_mul_of_nonneg_left hC (by positivity))

theorem witnessSpectralMasses : WitnessSpectralMasses := by
  intro X H _ _ _ _ n q m input ρ σ u v W ε hnorm hq hW hε hEq hbudget x V angles hV ha hU
  obtain ⟨hL,hgeometry⟩ := sourceGeometry_of_witness input ρ σ u v W ε hnorm hq hW hε hEq hbudget
  obtain ⟨hP,hLforbidden,hLfixed,hPfixed,hPforbidden,hdistance,hnormForbidden⟩ := hgeometry x
  constructor
  · exact source_walk_zero_mass (sourceKeep input x) (sourceComplement input ρ σ u W ε) V hV
      angles ha hU (sourcePlus (ρ x) (σ x)) (sourceFixed input ρ σ v W ε x)
      hPfixed hLfixed
      (sourcePlusMinus_norm (n := n) (q := q) (m := m) (ρ x) (σ x) (hnorm x).1 (hnorm x).2).1
      ε hε.le hdistance
  · intro Θ hΘ
    let w := ((Real.sqrt W/ε : ℝ) : ℂ) • sourceForbidden input ρ σ u W ε x
    have hLw : sourceComplement input ρ σ u W ε *ᵥ w=0 := by
      dsimp only [w]
      rw [Matrix.mulVec_smul,hLforbidden,smul_zero]
    have hPw : sourceKeep input x *ᵥ w=sourceMinus (ρ x) (σ x) := by
      dsimp only [w]
      rw [Matrix.mulVec_smul,hPforbidden,smul_smul]
      have hc : ((Real.sqrt W/ε : ℝ) : ℂ)*((ε/Real.sqrt W : ℝ) : ℂ)=1 := by
        push_cast
        have hr : (Real.sqrt W : ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr hW).ne'
        have he : (ε : ℂ)≠0 := by exact_mod_cast hε.ne'
        field_simp
      rw [hc,one_smul]
    exact source_walk_low_mass (sourceKeep input x) (sourceComplement input ρ σ u W ε) V
      hP hL hV angles ha hU w (sourceMinus (ρ x) (σ x)) hLw hPw
      (W^2/ε^2+1) Θ hnormForbidden hΘ

end Qatlib.Concepts.ConversionCore.WitnessCompile
