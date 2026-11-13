/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.Structure.Theorem9Stat
import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem7Quan
import Qatlib.Papers.QLinearODE17.Structure.Theorem9Encoding
import Qatlib.Papers.QLinearODE17.Structure.Theorem9Readout

/-!
# Quantitative ODE construction with measured readout

This module proves `theorem9V3`, the quantitative construction packaged by `Theorem9V3`. It
combines the sparse overlap encoding and singular-value gap with a finite inverse word, then
derives a clipped joint success bound and a conditional normalized-block readout estimate.

The result is the V2 Taylor-system formulation associated with Theorem 9 of [BerryEtAl2017ODE],
with its resource counts and positivity guard stated explicitly in `Theorem9V3`.

## Main statements

* `theorem9V3`: The quantitative construction, postselection, and guarded readout theorem.

## References

* [Berry et al., 2017][BerryEtAl2017ODE]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution Qatlib.Papers.QLinearODE17.TaylorAnalysis
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QLinearODE17.StructureCore
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

set_option maxHeartbeats 1000000 in

/-- Establishes `Theorem9V3`, including the sparse encoding and gap parameter, finite
inverse-word counts and output accuracy, clipped joint success bound, and guarded
normalized-block readout estimate. This is the formal quantitative construction associated
with [Berry et al., Theorem 9][BerryEtAl2017ODE]. -/
theorem theorem9V3 : Theorem9V3 := by
  classical
  intro N _ _ s m k p kq A V D h g x_in b x hm hk hp hh hg hkq hfac hr hc hd hA hV1 hV2 hre hM hq hacc hdecay hx
  haveI : Nonempty N := by
    rcases isEmpty_or_nonempty N with hE | hN
    · letI := hE
      have hz : stateVector (taylorODESolution A b x_in ((m : ℝ)*h))=0 := Subsingleton.elim _ _
      rw [hz,norm_zero] at hq
      exact False.elim (by linarith)
    · exact hN
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hfactor : (m : ℝ)/(25*m)=1/25 := by field_simp
  have hError := taylorV2_error_of_accuracy m k p A V D h x_in b x hm hk hp hh
    hd hA hV1 hV2 hre hM hq hacc hx m le_rfl
  rw [hfactor] at hError
  have hxne : x≠0 := by
    intro hz
    rw [hz,show stateVector (taylorBlock (0 : QState (Fin (m*(k+1)+p+1) × N))
      (taylorTimeLabel m k p m le_rfl))=0 from rfl,sub_zero] at hError
    linarith
  have hxn : 0 < ‖stateVector x‖ := norm_pos_iff.mpr ((stateVector_eq_zero_iff x).not.mpr hxne)
  let C := taylorStepMatrixV2 m k p (h • A)
  let rhs := taylorRHS m k p h x_in b
  have hrhs : 0 < ‖stateVector rhs‖ := by
    apply norm_pos_iff.mpr
    apply (stateVector_eq_zero_iff rhs).not.mpr
    intro hz
    have he := congrArg (fun v => C⁻¹ *ᵥ v) hx
    change C⁻¹ *ᵥ (C *ᵥ x)=C⁻¹ *ᵥ rhs at he
    rw [Matrix.mulVec_mulVec,(taylorStepMatrixV2_inverse m k p (h • A)).2,
      Matrix.one_mulVec,hz,Matrix.mulVec_zero] at he
    exact hxne he
  obtain ⟨κ,hκ,hbudget,hgap,henc⟩ := taylorV2_encoding_and_gap s m k p A V D h
    hm hk hp hh hfac hr hc hd hA hV1 hV2 hre hM
  refine ⟨κ,hκ,hbudget,hgap,henc,?_⟩
  (try dsimp only)
  let scale : ℕ := k+s+3
  let frameScale : ℝ := (k : ℝ)+(s : ℝ)+3
  let Cbar : Matrix (Fin (m*(k+1)+p+1) × N) _ ℂ := (scale : ℂ)⁻¹ • C
  let Bbar : Matrix (Fin (m*(k+1)+p+1) × N) _ ℂ := (scale : ℂ) • C⁻¹
  let z : QState (Fin (m*(k+1)+p+1) × N) := ((‖stateVector rhs‖ : ℝ) : ℂ)⁻¹ • rhs
  let β : ℝ := (scale : ℝ)/‖stateVector rhs‖
  let y : QState (Fin (m*(k+1)+p+1) × N) := (β : ℂ) • x
  have hβ : 0 < β := by dsimp [β,scale]; positivity
  have hz : Normalized z := by
    apply (normalized_iff_stateVector_norm z).mpr
    change ‖stateVector (((‖stateVector rhs‖ : ℝ) : ℂ)⁻¹ • rhs)‖=1
    rw [taylor_state_inv_norm]
    exact NormedSpace.norm_normalize_eq_one_iff.mpr (norm_pos_iff.mp hrhs)
  have hsne : (scale : ℂ)≠0 := by dsimp [scale]; exact_mod_cast (show k+s+3≠0 by omega)
  have hrne : ((‖stateVector rhs‖ : ℝ) : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hrhs.ne'
  have hcoeff : (scale : ℂ)⁻¹*(β : ℂ)=((‖stateVector rhs‖ : ℝ) : ℂ)⁻¹ := by
    dsimp [β]
    push_cast
    field_simp
  have hy : Cbar *ᵥ y=z := by
    dsimp only [Cbar,y,z]
    rw [Matrix.smul_mulVec,Matrix.mulVec_smul,hx,smul_smul,hcoeff]
  have hBbar : Bbar*Cbar=1 := (taylor_scaled_inverse m k p s (h • A)).1
  have hyDir : NormedSpace.normalize (stateVector y)=NormedSpace.normalize (stateVector x) := by
    dsimp only [y]
    rw [taylor_state_real_smul,NormedSpace.normalize_smul_of_pos hβ]
  obtain ⟨hquery,hgate,φ,hout,hφ,herr,hprob⟩ := taylor_actual_inverse_word_of_solved
    Cbar Bbar (1 : Matrix _ _ ℂ) (sparseOverlapLeft C frameScale) (sparseOverlapRight C frameScale)
    κ kq z y henc hκ hz hgap hBbar hy
  rw [hyDir] at herr
  let ψ : QState (Fin (m*(k+1)+p+1) × N) := ((‖stateVector x‖ : ℝ) : ℂ)⁻¹ • x
  have hψ : stateVector ψ=NormedSpace.normalize (stateVector x) := taylor_state_inv_norm x
  have herrψ : ‖stateVector φ-stateVector ψ‖ ≤ (1 : ℝ)/2^kq := by rw [hψ]; exact herr
  let Dmass : ℝ := (p : ℝ)+77*(m : ℝ)*g^2
  have hDmass : 0 < Dmass := by dsimp [Dmass]; positivity
  have hFrac :=
      theorem7V2 N m k p A V D h g x_in b x hm hk hp hh hg hd hA hV1 hV2 hre hM hq hacc hdecay hx
  have hMass : Real.sqrt ((p+1 : ℕ)/Dmass) ≤ Real.sqrt (MeasureProb ψ (taylorSuccessSet m k p)) :=
    taylor_normalized_success_mass m k p Dmass hDmass x hxn (fun j => hFrac j.val (by omega))
  refine ⟨hquery,hgate,φ,hout,hφ,herr,hprob,?_,?_⟩
  · exact taylor_joint_probability_clipped ψ φ (taylorSuccessSet m k p)
      (Real.sqrt ((p+1 : ℕ)/Dmass)) ((1 : ℝ)/2^kq) _ _ (by positivity) hprob hMass herrψ
  · intro hguard
    refine ⟨taylorMeasuredDensityV2_posSemidef m k p φ,taylorMeasuredDensityV2_trace m k p φ,?_⟩
    intro l hl
    let j : ℕ := l.val-m*(k+1)
    have hjp : j ≤ p := by have := l.isLt; dsimp [j]; omega
    have hlabel : taylorFinalLabel m k p j hjp=l := by
      apply Fin.ext
      dsimp only [taylorFinalLabel,j]
      omega
    have hfl := hFrac j hjp
    rw [hlabel] at hfl
    have hlo : 1/Real.sqrt Dmass ≤ ‖stateVector (taylorBlock ψ l)‖ :=
      taylor_normalized_block_lower x hxn l _ hfl
    have he := (taylor_block_error_le φ ψ l).trans herrψ
    have hδ : (0 : ℝ) ≤ (1 : ℝ)/2^kq := by positivity
    have hgapBlock : (1 : ℝ)/2^kq < ‖stateVector (taylorBlock ψ l)‖ := lt_of_lt_of_le hguard hlo
    have hnorm := (normalize_error_of_gap he hgapBlock).2
    have hden : 0 < 1/Real.sqrt Dmass-(1 : ℝ)/2^kq := sub_pos.mpr hguard
    have hdenle : 1/Real.sqrt Dmass-(1 : ℝ)/2^kq ≤ ‖stateVector (taylorBlock ψ l)‖ := by linarith
    have hn : ‖NormedSpace.normalize (stateVector (taylorBlock φ l))-
        NormedSpace.normalize (stateVector (taylorBlock ψ l))‖ ≤
        2*((1 : ℝ)/2^kq)/(1/Real.sqrt Dmass-(1 : ℝ)/2^kq) :=
      hnorm.trans (div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hδ) hden hdenle)
    have hcopy : taylorBlock x l=taylorBlock x (taylorTimeLabel m k p m le_rfl) := by
      rw [← taylorNatBlock_eq x l,show l.val=m*(k+1)+j by dsimp [j]; omega]
      exact taylorNatBlock_pad m k p (h • A) h x_in b x hx j hjp
    have hterminal := taylorV2_terminal_direction m k p A V D h x_in b x hm hk hp hh
      hd hA hV1 hV2 hre hM hq hacc hx
    have ht : ‖NormedSpace.normalize (stateVector (taylorBlock ψ l))-
        NormedSpace.normalize (stateVector (taylorODESolution A b x_in ((m : ℝ)*h)))‖ ≤ 1/12 := by
      rw [taylor_normalized_block_direction x hxn l,hcopy]
      exact hterminal
    exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hn ht)

example := taylorV2_zero_generator_consumer

end Qatlib.Papers.QLinearODE17.StructureCore
