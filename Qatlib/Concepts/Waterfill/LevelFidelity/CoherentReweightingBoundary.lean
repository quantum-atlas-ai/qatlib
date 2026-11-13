/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Waterfill.LevelFidelity.CoherentReweightingBoundaryDefs
import Qatlib.Concepts.Waterfill.LevelFidelity.RealFidelityEndpoints
import Qatlib.Concepts.Waterfill.LevelFidelity.EffectiveFidelitySearch
import Qatlib.Concepts.Waterfill.LevelFidelity.AccessReweighting

/-!
# Boundary cases and complete reweighting contracts

`gext1_complete` combines endpoint formulas, level existence, and source-box optimality,
including a collapsed bracket. `gext2_complete` supplies certified rational brackets and
mass-error estimates, while `gext3_complete` derives a source-query bound conditionally on a
filtered consumer and records its failure on a zero-query instance.

These statements refine the water-level setting of quantum rejection sampling
[OzolsRoettelerRoland2013]; see [Ozols et al., 2013][OzolsRoettelerRoland2013].
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.NativeNumerics.WaterFilling
open Qatlib.Concepts.Waterfill.LevelFidelity.EffectiveFidelitySearch
open Qatlib.Concepts.Waterfill.LevelSearch

namespace Qatlib.Concepts.Waterfill.LevelFidelity

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Matrix
open Qatlib
open Qatlib.Concepts.Waterfill.ExactResampling
open Qatlib
open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.Waterfill.LevelFidelity.RealTableWaterLevel
open Qatlib.Concepts.WaterLevel.WaterPrecision
open Qatlib
open scoped BigOperators ComplexOrder ENNReal

variable {m : ℕ}

/-- Combines the endpoint fill, mass, and overlap formulas with level existence for a strict
extended bracket and the fidelity characterization for a collapsed bracket. It also proves
the overlap comparison at bounded mass and the mass optimality of a realizing fill among
source-box competitors meeting the fidelity constraint. -/
theorem gext1_complete :
    ∀ (m : ℕ) (π σ : Fin m → ℝ) (γlo γhi : ℝ) (p : ℝ),
      (∑ i, π i ^ 2) = 1 → (∑ i, σ i ^ 2) = 1 →
      ExtendedBracket π σ γlo γhi →
      realPmin π σ ≤ p → p ≤ realPmax π σ →
      (∀ i, σ i = 0 → realFill π σ γlo i = 0) ∧
      (∀ i, realFill π σ γlo i = if 0 < π i then γlo * σ i else 0) ∧
      realDot π σ γlo = γlo * realPmax π σ ∧
      realMass π σ γlo = γlo ^ 2 * realPmax π σ ∧
      (∀ i, realFill π σ γhi i = π i) ∧
      realMass π σ γhi = 1 ∧
      realDot π σ γhi = ∑ i, π i * σ i ∧
      (γlo < γhi → ∃ γ, γlo ≤ γ ∧ γ ≤ γhi ∧ 0 < realMass π σ γ ∧
        realDot π σ γ ^ 2 = p * realMass π σ γ) ∧
      (γlo = γhi → (realDot π σ γlo ^ 2 = p * realMass π σ γlo ↔ p = realPmax π σ)) ∧
      (∀ γ, 0 < γ → ∀ v, SourceBox π v → (∑ i, v i ^ 2) ≤ realMass π σ γ →
        (∑ i, σ i * v i) ≤ realDot π σ γ) ∧
      (∀ γ, γlo < γ → γ ≤ γhi → RealizesFidelity π σ p γ →
        ∀ v, SourceBox π v → p * (∑ i, v i ^ 2) ≤ (∑ i, σ i * v i) ^ 2 →
          (∑ i, v i ^ 2) ≤ realMass π σ γ) := by
  intro m π σ γlo γhi p hπn _hσn hEB hpmin hpmax
  rcases hEB with ⟨hγ0, hγlo, hπ, hσ, hsupp, hBlo, hBhi, hBloT, hBhiT⟩
  obtain ⟨i₀, hi₀π, hi₀eq⟩ := hBloT
  obtain ⟨i₁, hi₁σ, hi₁π, hi₁eq⟩ := hBhiT

  have hi₀σ : 0 < σ i₀ := by
    by_contra h
    have hz : σ i₀ = 0 := le_antisymm (not_lt.mp h) (hσ i₀)
    rw [hz, mul_zero] at hi₀eq
    linarith
  have hγlo_pos : 0 < γlo := by
    have hpos : 0 < γlo * σ i₀ := by rw [hi₀eq]; exact hi₀π
    have hq : 0 < (γlo * σ i₀) / σ i₀ := div_pos hpos hi₀σ
    have heq : (γlo * σ i₀) / σ i₀ = γlo := by
      rw [mul_div_assoc, div_self (ne_of_gt hi₀σ), mul_one]
    linarith

  have hpmax_pos : 0 < realPmax π σ := by
    have hnonneg : ∀ j, 0 ≤ (if 0 < π j then σ j ^ 2 else 0) := by
      intro j; split_ifs <;> positivity
    have hterm : 0 < (if 0 < π i₀ then σ i₀ ^ 2 else 0) := by
      rw [if_pos hi₀π]; positivity
    unfold realPmax
    exact Finset.sum_pos' (fun j _ => hnonneg j) ⟨i₀, Finset.mem_univ i₀, hterm⟩

  have hzero : ∀ i, σ i = 0 → realFill π σ γlo i = 0 :=
    fun i hi => realFill_zeroSigma hπ i hi

  have hlow : ∀ i, realFill π σ γlo i = if 0 < π i then γlo * σ i else 0 := by
    intro i
    by_cases hi : 0 < π i
    · rw [realFill_bracketLow hπ hBlo i hi, if_pos hi]
    · rw [realFill_sourceZero hσ hγ0 i (le_antisymm (not_lt.mp hi) (hπ i)), if_neg hi]
  have hdotlo : realDot π σ γlo = γlo * realPmax π σ :=
    realDot_bracketLow hπ hσ hγ0 hBlo
  have hmasslo : realMass π σ γlo = γlo ^ 2 * realPmax π σ :=
    realMass_bracketLow hπ hσ hγ0 hBlo

  have hhigh : ∀ i, realFill π σ γhi i = π i :=
    fun i => realFill_bracketHigh_all hπ hσ hsupp hBhi i
  have hmasshi : realMass π σ γhi = 1 :=
    realMass_bracketHigh hπ hσ hsupp hBhi hπn
  have hdothi : realDot π σ γhi = ∑ i, π i * σ i :=
    realDot_bracketHigh hπ hσ hsupp hBhi

  have hf : Continuous (fun γ : ℝ => realDot π σ γ ^ 2 - p * realMass π σ γ) :=
    (continuous_realDot (π := π) (σ := σ)).pow 2 |>.sub
      (continuous_const.mul (continuous_realMass (π := π) (σ := σ)))
  have hflo : 0 ≤ realDot π σ γlo ^ 2 - p * realMass π σ γlo := by
    rw [hdotlo, hmasslo]
    have hpmax0 := realPmax_nonneg (π := π) (σ := σ)
    nlinarith
  have hfhi : realDot π σ γhi ^ 2 - p * realMass π σ γhi ≤ 0 := by
    have hmin : realDot π σ γhi ^ 2 = realPmin π σ := by
      rw [hdothi]; rfl
    rw [hmin, hmasshi]
    linarith
  have hexist : γlo < γhi →
      ∃ γ, γlo ≤ γ ∧ γ ≤ γhi ∧ 0 < realMass π σ γ ∧
        realDot π σ γ ^ 2 = p * realMass π σ γ := by
    intro hlt
    have hcont : ContinuousOn (fun γ : ℝ => realDot π σ γ ^ 2 - p * realMass π σ γ)
        (Set.Icc γlo γhi) := hf.continuousOn
    have hIcc : (0 : ℝ) ∈ Set.Icc (realDot π σ γhi ^ 2 - p * realMass π σ γhi)
        (realDot π σ γlo ^ 2 - p * realMass π σ γlo) := ⟨hfhi, hflo⟩
    obtain ⟨γ, hγmem, hfγ⟩ :=
      intermediate_value_Icc' (show γlo ≤ γhi from hγlo) hcont hIcc
    refine ⟨γ, hγmem.1, hγmem.2, ?_, ?_⟩
    · have hmono := realMass_mono π σ hπ hσ hγ0 hγmem.1
      have hmasslo_pos : 0 < realMass π σ γlo := by
        rw [hmasslo]
        exact mul_pos (sq_pos_of_pos hγlo_pos) hpmax_pos
      linarith
    · have hz : realDot π σ γ ^ 2 - p * realMass π σ γ = 0 := hfγ
      linarith

  have hdeg : γlo = γhi → (realDot π σ γlo ^ 2 = p * realMass π σ γlo ↔
      p = realPmax π σ) := by
    intro hEq
    rw [hdotlo, hmasslo]
    constructor
    · intro h
      have hA : 0 < γlo ^ 2 * realPmax π σ :=
        mul_pos (sq_pos_of_pos hγlo_pos) hpmax_pos
      have hz : (γlo ^ 2 * realPmax π σ) * (realPmax π σ - p) = 0 := by
        have h1 : (γlo * realPmax π σ) ^ 2
            = (γlo ^ 2 * realPmax π σ) * realPmax π σ := by ring
        rw [h1] at h
        have h2 : (γlo ^ 2 * realPmax π σ) * realPmax π σ
            - p * (γlo ^ 2 * realPmax π σ) = 0 := by linarith
        calc (γlo ^ 2 * realPmax π σ) * (realPmax π σ - p)
            = (γlo ^ 2 * realPmax π σ) * realPmax π σ
                - p * (γlo ^ 2 * realPmax π σ) := by ring
          _ = 0 := h2
      have : realPmax π σ - p = 0 :=
        (mul_eq_zero.mp hz).resolve_left (ne_of_gt hA)
      linarith
    · intro h
      rw [h]
      ring

  have hover : ∀ γ, 0 < γ → ∀ v, SourceBox π v → (∑ i, v i ^ 2) ≤ realMass π σ γ →
      (∑ i, σ i * v i) ≤ realDot π σ γ :=
    fun γ hγ v hv he => real_overlap_le π σ hπ hσ hγ v hv he

  have hopt : ∀ γ, γlo < γ → γ ≤ γhi → RealizesFidelity π σ p γ →
      ∀ v, SourceBox π v → p * (∑ i, v i ^ 2) ≤ (∑ i, σ i * v i) ^ 2 →
        (∑ i, v i ^ 2) ≤ realMass π σ γ := by
    intro γ hγ0 hγ1 hreal v hv hcomp
    by_cases hEq : γ = γhi
    · subst hEq
      have hvle : (∑ i, v i ^ 2) ≤ ∑ i, π i ^ 2 := by
        apply Finset.sum_le_sum; intro i _
        have h1 := (hv i).1
        have h2 := (hv i).2
        nlinarith
      have hmass : realMass π σ γ = 1 := realMass_bracketHigh hπ hσ hsupp hBhi hπn
      linarith
    · have hlt : γ < γhi := lt_of_le_of_ne hγ1 hEq
      by_contra hcon
      push Not at hcon
      have hmasspos : 0 < realMass π σ γ := hreal.1
      have hdotrel : realDot π σ γ ^ 2 = p * realMass π σ γ := hreal.2
      have hγpos : 0 < γ := by linarith

      have hvsum : (∑ i, v i ^ 2) ≤ 1 := by
        have hvle : (∑ i, v i ^ 2) ≤ ∑ i, π i ^ 2 := by
          apply Finset.sum_le_sum; intro i _
          have h1 := (hv i).1
          have h2 := (hv i).2
          nlinarith
        linarith
      have hmg1 : realMass π σ γ < 1 := by linarith

      let sat : ℝ := ∑ i, if 0 < π i then π i / σ i else 0
      have hg : ∀ j, 0 ≤ (if 0 < π j then π j / σ j else 0) := by
        intro j
        by_cases hj : 0 < π j
        · rw [if_pos hj]
          have hσj : 0 < σ j := by
            by_contra h
            have hz : σ j = 0 := le_antisymm (not_lt.mp h) (hσ j)
            have hpi0 : π j = 0 := hsupp j hz
            exact absurd hj (by rw [hpi0]; exact lt_irrefl _)
          exact div_nonneg (le_of_lt hj) (le_of_lt hσj)
        · rw [if_neg hj]
      have hsat0 : 0 ≤ sat := by
        unfold sat
        exact Finset.sum_nonneg fun j _ => hg j
      have hsatfill : ∀ i, realFill π σ sat i = π i := by
        intro i
        by_cases hi : 0 < π i
        · have hσpos : 0 < σ i := by
            by_contra h
            have hz : σ i = 0 := le_antisymm (not_lt.mp h) (hσ i)
            have hpi0 : π i = 0 := hsupp i hz
            exact absurd hi (by rw [hpi0]; exact lt_irrefl _)
          have hge : π i / σ i ≤ ∑ j, if 0 < π j then π j / σ j else 0 := by
            have h := Finset.single_le_sum (fun j _ => hg j) (Finset.mem_univ i)
            rw [if_pos hi] at h
            exact h
          have hge' : π i / σ i ≤ sat := by unfold sat; linarith
          have hkey : π i ≤ sat * σ i := by
            have h2 : (π i / σ i) * σ i ≤ sat * σ i :=
              mul_le_mul_of_nonneg_right hge' (le_of_lt hσpos)
            have h3 : (π i / σ i) * σ i = π i := by field_simp
            linarith
          rw [realFill, min_eq_left hkey]
        · have hpi0 : π i = 0 := le_antisymm (not_lt.mp hi) (hπ i)
          rw [realFill, hpi0, min_eq_left (mul_nonneg hsat0 (hσ i))]
      have hsatmass : realMass π σ sat = 1 := by
        have hstep : (∑ i, (realFill π σ sat i) ^ 2) = ∑ i, π i ^ 2 := by
          apply Finset.sum_congr rfl; intro i _
          rw [hsatfill i]
        rw [realMass, hstep, hπn]

      have hγsat : γ < sat := by
        by_contra h
        have hle := realMass_mono π σ hπ hσ hsat0 (le_of_not_gt h)
        rw [hsatmass] at hle
        linarith

      have hcont : ContinuousOn (fun γ : ℝ => realMass π σ γ) (Set.Icc γ sat) :=
        (continuous_realMass (π := π) (σ := σ)).continuousOn
      have hIcc : (∑ i, v i ^ 2) ∈ Set.Icc (realMass π σ γ) (realMass π σ sat) :=
        ⟨by linarith, by rw [hsatmass]; exact hvsum⟩
      obtain ⟨γ₂, hγ₂mem, hmass₂⟩ :=
        intermediate_value_Icc (show γ ≤ sat from le_of_lt hγsat) hcont hIcc
      have hmass₂' : realMass π σ γ₂ = ∑ i, v i ^ 2 := hmass₂
      have hγ₂pos : γ < γ₂ := by
        by_contra h
        have hγ₂0 : 0 ≤ γ₂ := le_trans (le_of_lt hγpos) hγ₂mem.1
        have hle := realMass_mono (a := γ₂) (b := γ) π σ hπ hσ hγ₂0 (le_of_not_gt h)
        rw [hmass₂'] at hle
        linarith

      have hlo' : ∃ j, 0 < π j ∧ π j < γ * σ j :=
        ⟨i₀, hi₀π, by rw [← hi₀eq]; exact mul_lt_mul_of_pos_right hγ0 hi₀σ⟩
      have hhi' : ∃ i, 0 < σ i ∧ γ * σ i < π i :=
        ⟨i₁, hi₁σ, by rw [hi₁eq]; exact mul_lt_mul_of_pos_right hlt hi₁σ⟩
      have hanti := realFidelity_anti_lt π σ hπ hσ hγpos hγ₂pos hlo' hhi'
      have hoverlap : (∑ i, σ i * v i) ≤ realDot π σ γ₂ := by
        apply real_overlap_le (γ := γ₂) π σ hπ hσ (by linarith) v hv
        rw [hmass₂']
      have hdot0 : 0 ≤ realDot π σ γ₂ :=
        (realMass_le_level_dot (γ := γ₂) π σ hπ hσ (by linarith)).2.1
      have hvnonneg : 0 ≤ ∑ i, σ i * v i := by
        apply Finset.sum_nonneg; intro i _
        exact mul_nonneg (hσ i) ((hv i).1)
      have hsq : (∑ i, σ i * v i) ^ 2 ≤ realDot π σ γ₂ ^ 2 :=
        (sq_le_sq₀ hvnonneg hdot0).mpr hoverlap
      have hcontra : realDot π σ γ₂ ^ 2 < p * (∑ i, v i ^ 2) := by
        have h1 := hanti
        rw [hmass₂', hdotrel] at h1
        have h1' : realDot π σ γ₂ ^ 2 * realMass π σ γ
            < p * realMass π σ γ * (∑ i, v i ^ 2) := by
          calc realDot π σ γ₂ ^ 2 * realMass π σ γ
              < (p * realMass π σ γ) * (∑ i, v i ^ 2) := h1
            _ = p * realMass π σ γ * (∑ i, v i ^ 2) := by ring
        have hkey : realDot π σ γ₂ ^ 2 * realMass π σ γ
            < (p * (∑ i, v i ^ 2)) * realMass π σ γ := by
          calc realDot π σ γ₂ ^ 2 * realMass π σ γ
              < p * realMass π σ γ * (∑ i, v i ^ 2) := h1'
            _ = (p * (∑ i, v i ^ 2)) * realMass π σ γ := by ring
        exact lt_of_mul_lt_mul_right hkey (le_of_lt hmasspos)
      nlinarith [hcomp, hsq, hcontra]
  refine ⟨hzero, hlow, hdotlo, hmasslo, hhigh, hmasshi, hdothi, hexist, hdeg, hover, hopt⟩

/-- For admissible normalized rational tables, supplies certified brackets and exact
arithmetic-work counts at every search depth. The selected level bounds every positive-mass
realizing level from above, lies within the stated dyadic distance of a residual root, and
gives a corresponding local mass-error estimate. -/
theorem gext2_complete :
    ∀ (m : ℕ) (π σ : Fin m → ℚ) (p : ℚ),
      (∀ i, 0 ≤ π i) → (∀ i, 0 ≤ σ i) →
      (∑ i, (π i : ℝ) ^ 2) = 1 → (∑ i, (σ i : ℝ) ^ 2) = 1 →
      computedFidelity π σ (computedWaterHigh π σ) < p →
      p ≤ computedPmax π σ →
      (∀ k : ℕ,
        CertifiedBracket π σ p k ∧
        (searchWork m k).divisions = m ∧
        (searchWork m k).energyEvaluations = m * k ∧
        (searchWork m k).comparisons = k ∧
        (∀ γt,
          0 < realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) γt →
          realDot (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) γt ^ 2 =
            (p : ℝ) * realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) γt →
          γt ≤ selectedLevel π σ p k) ∧
        (∃ γt,
          realDot (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) γt ^ 2 =
            (p : ℝ) * realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) γt ∧
          (selectedLevel π σ p k : ℝ) - ((computedWaterHigh π σ : ℝ) / 2 ^ k) ≤ γt ∧
          γt ≤ (selectedLevel π σ p k : ℝ) + ((computedWaterHigh π σ : ℝ) / 2 ^ k)) ∧
        (∀ γt, 0 ≤ γt →
          |γt - (selectedLevel π σ p k : ℝ)| ≤ ((computedWaterHigh π σ : ℝ) / 2 ^ k) →
          |realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) γt
              - realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) (selectedLevel π σ p k)|
            ≤ 2 * ((computedWaterHigh π σ : ℝ) / 2 ^ k) * (∑ i, (σ i : ℝ) * (π i : ℝ)))) := by
  intro m π σ p hπ hσ hπn hσn hfid hmax
  obtain ⟨hB, hT, _, _⟩ := gext2 m π σ p hπ hσ hπn hσn hfid hmax
  intro k
  have hk := hB k

  have hcert : CertifiedBracket π σ p k := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hk.1
    · exact hk.2.1
    · exact hk.2.2.1
    · exact hk.2.2.2.1
    · exact hk.2.2.2.2.1
    · exact hk.2.2.2.2.2.1
  have hdiv : (searchWork m k).divisions = m := hk.2.2.2.2.2.2.1
  have henergy : (searchWork m k).energyEvaluations = m * k := hk.2.2.2.2.2.2.2.1
  have hcomp : (searchWork m k).comparisons = k := hk.2.2.2.2.2.2.2.2

  have hsel0 : 0 ≤ (selectedLevel π σ p k : ℝ) := by
    have h1 : (0 : ℚ) ≤ (fidelityBracket π σ p k).1 := hk.1
    have h2 : (fidelityBracket π σ p k).1 ≤ (fidelityBracket π σ p k).2 := hk.2.1
    have h3 : (0 : ℚ) ≤ (fidelityBracket π σ p k).2 := le_trans h1 h2
    have h4 : (0 : ℚ) ≤ (selectedLevel π σ p k) := by
      rw [selectedLevel]
      exact h3
    exact_mod_cast h4
  have hnot : ¬ fidelityReaches π σ p (selectedLevel π σ p k) := by
    have h := hk.2.2.2.2.2.1
    simpa [selectedLevel] using! h
  have hq : computedDot π σ (selectedLevel π σ p k) ^ 2
      < p * computedMass π σ (selectedLevel π σ p k) := by
    unfold fidelityReaches at hnot
    exact lt_of_not_ge hnot
  have hcast : realDot (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) (selectedLevel π σ p k) ^ 2
      < (p : ℝ) * realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ))
        (selectedLevel π σ p k) := by
    have h1 : (computedDot π σ (selectedLevel π σ p k) : ℝ) ^ 2
        < (p : ℝ) * (computedMass π σ (selectedLevel π σ p k) : ℝ) := by
      have h := hq
      norm_cast
    rw [realDot_cast, realMass_cast]
    exact h1

  have hdom : ∀ γt,
      0 < realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) γt →
      realDot (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) γt ^ 2 =
        (p : ℝ) * realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) γt →
      γt ≤ selectedLevel π σ p k := by
    intro γt hmass hrel
    by_contra hcon
    push Not at hcon
    have hanti := realFidelity_anti (m := m) (fun i => (π i : ℝ)) (fun i => (σ i : ℝ))
      (fun i => Rat.cast_nonneg.mpr (hπ i)) (fun i => Rat.cast_nonneg.mpr (hσ i))
      hsel0 (by exact_mod_cast (show selectedLevel π σ p k ≤ γt from le_of_lt hcon))
    have hmul : (p : ℝ) *
          (realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) (selectedLevel π σ p k) : ℝ) *
          (realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) γt : ℝ)
        ≤ (realDot (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) (selectedLevel π σ p k) : ℝ) ^ 2 *
          (realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) γt : ℝ) := by
      have h1 := hanti
      rw [hrel] at h1
      calc (p : ℝ) *
          (realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) (selectedLevel π σ p k) : ℝ) *
          (realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) γt : ℝ)
          = (p * (realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) γt : ℝ)) *
            (realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) (selectedLevel π σ p k) : ℝ) := by
              ring
        _ ≤ (realDot (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) (selectedLevel π σ p k) : ℝ) ^ 2 *
            (realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) γt : ℝ) := h1
    have hlt : (realDot (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) (selectedLevel π σ p k) : ℝ) ^ 2 *
          (realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) γt : ℝ)
        < (p : ℝ) *
          (realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) (selectedLevel π σ p k) : ℝ) *
          (realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) γt : ℝ) :=
      mul_lt_mul_of_pos_right hcast hmass
    have hcontra : (p : ℝ) *
          (realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) (selectedLevel π σ p k) : ℝ) *
          (realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) γt : ℝ)
        < (p : ℝ) *
          (realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) (selectedLevel π σ p k) : ℝ) *
          (realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) γt : ℝ) :=
      lt_of_le_of_lt hmul hlt
    exact (lt_irrefl _ hcontra)

  obtain ⟨γt, habs, htransrel⟩ := hT k
  have hlo' : (selectedLevel π σ p k : ℝ) - ((computedWaterHigh π σ : ℝ) / 2 ^ k) ≤ γt := by
    have := (abs_le.mp habs).2
    linarith
  have hhi' : γt ≤ (selectedLevel π σ p k : ℝ) + ((computedWaterHigh π σ : ℝ) / 2 ^ k) := by
    have := (abs_le.mp habs).1
    linarith

  have hprec : ∀ γt, 0 ≤ γt →
      |γt - (selectedLevel π σ p k : ℝ)| ≤ ((computedWaterHigh π σ : ℝ) / 2 ^ k) →
      |realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) γt
          - realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) (selectedLevel π σ p k)|
        ≤ 2 * ((computedWaterHigh π σ : ℝ) / 2 ^ k) * (∑ i, (σ i : ℝ) * (π i : ℝ)) := by
    intro γt hγt0 hδ
    have h := realMass_abs_le (π := fun i => (π i : ℝ)) (σ := fun i => (σ i : ℝ))
      (fun i => Rat.cast_nonneg.mpr (hπ i)) (fun i => Rat.cast_nonneg.mpr (hσ i))
      hγt0 hsel0
    have hS : 0 ≤ ∑ i, (σ i : ℝ) * (π i : ℝ) := by
      apply Finset.sum_nonneg; intro i _
      exact mul_nonneg (Rat.cast_nonneg.mpr (hσ i)) (Rat.cast_nonneg.mpr (hπ i))
    calc |realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) γt
          - realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) (selectedLevel π σ p k)|
        ≤ 2 * |γt - (selectedLevel π σ p k : ℝ)| * (∑ i, (σ i : ℝ) * (π i : ℝ)) := h
      _ ≤ 2 * ((computedWaterHigh π σ : ℝ) / 2 ^ k) * (∑ i, (σ i : ℝ) * (π i : ℝ)) := by
        have hmul := mul_le_mul_of_nonneg_right hδ (by positivity : (0:ℝ) ≤
          2 * (∑ i, (σ i : ℝ) * (π i : ℝ)))
        nlinarith
  refine ⟨hcert, hdiv, henergy, hcomp, hdom, ⟨γt, htransrel, hlo', hhi'⟩, hprec⟩

/-- The empty prepared word succeeds with fidelity one for the one-coordinate constant-one
source and target with ancillary dimension one at level one. -/
theorem easyInstance_success :
    ReweightingSuccess (D := 1) ((0, 0) : Fin 1 × Fin 1) easyPi easySig (1 : ℝ) 1
      (List.nil : List (PreparedStep ((Fin 1 × Fin 1) × Bool))) := by
  have hm : levelMass easyPi easySig (1 : ℝ) = 1 := by
    unfold levelMass levelFill easyPi easySig
    rw [Fin.sum_univ_one]
    norm_num
  have hmass : 0 < levelMass easyPi easySig (1 : ℝ) := by rw [hm]; norm_num
  have hd : levelDot easyPi easySig (1 : ℝ) = 1 := by
    unfold levelDot levelFill easyPi easySig
    rw [Fin.sum_univ_one]
    norm_num
  refine ⟨hmass, by rw [hd, hm]; norm_num, ?_⟩
  intro ξ U hξ hU _
  have heval : (evaluatePrepared 1 (resamplingEmbeddedOracle U)
      (List.nil : List (PreparedStep ((Fin 1 × Fin 1) × Bool)))) = 1 := rfl
  have hout : ApplyGate (evaluatePrepared 1 (resamplingEmbeddedOracle U)
      (List.nil : List (PreparedStep ((Fin 1 × Fin 1) × Bool)))) (Ket ((0, 0), false))
      = Ket ((0, 0), false) := by
    rw [heval]
    exact Matrix.one_mulVec _
  refine ⟨?_, ?_, ?_⟩
  · rw [hout]
    exact normalized_ket _
  · rw [hout]
    show (∑ i ∈ waterEvent 1 1, BornProb (Ket ((0, 0), false)) i) = 0
    apply Finset.sum_eq_zero
    intro p hp
    have hb : p.2 = true := (Finset.mem_filter.mp hp).2
    have hne : p ≠ ((0, 0), false) := by
      intro hh
      rw [hh] at hb
      simp at hb
    simp [BornProb, Ket, hne]
  · have hinner : Inner (resamplingFamily (fun i => (easySig i : ℝ)) ξ)
        (Ket ((0, 0), false)) = (starRingEnd ℂ) (ξ 0 0) := by
      rw [inner_apply]
      have hket : ∀ p : ((Fin 1 × Fin 1) × Bool),
          Ket ((0, 0), false) p = if p = ((0, 0), false) then 1 else 0 := fun _ => rfl
      conv_lhs => simp only [hket, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_univ, if_true]
      simp [resamplingFamily, easySig]
    have hnorm : Complex.normSq (ξ 0 0) = 1 := by
      have h := hξ 0
      have hsum : (∑ d : Fin 1, ‖(ξ 0) d‖ ^ 2) = 1 := h
      rw [Fin.sum_univ_one] at hsum
      rw [Complex.normSq_eq_norm_sq]
      exact hsum
    rw [hout, hinner]
    show (1 : ℝ) ≤ Complex.normSq ((starRingEnd ℂ) (ξ 0 0))
    have hconj : Complex.normSq ((starRingEnd ℂ) (ξ 0 0)) = Complex.normSq (ξ 0 0) :=
      Complex.normSq_conj _
    rw [hconj, hnorm]

/-- Derives the source-query bound `c / (2 * sqrt(levelMass))` conditionally on a filtered
gamma-two lower-bound consumer. It also excludes such consumers whenever a successful
zero-query word exists and records the explicit one-dimensional counterexample. -/
theorem gext3_complete :
    ∀ (m D : ℕ) (π σ : Fin m → ℚ) (γ p δ c cδ : ℝ),
      0 < levelMass π σ γ →
      (FilteredGamma2LowerConsumer (D := D) π σ γ p δ c cδ →
        SourceQueryBound (D := D) π σ γ p c) ∧
      (∀ (j₀ : Fin m × Fin D) (W : List (PreparedStep ((Fin m × Fin D) × Bool))),
        ReweightingSuccess j₀ π σ γ p W → preparedInputQueries W = 0 →
          ¬ FilteredGamma2LowerConsumer (D := D) π σ γ p δ c cδ) ∧
      (¬ FilteredGamma2LowerConsumer (D := 1) easyPi easySig (1 : ℝ) 1 (0 : ℝ) 1 1) := by
  intro m D π σ γ p δ c cδ hmass

  have hbound : FilteredGamma2LowerConsumer (D := D) π σ γ p δ c cδ →
      SourceQueryBound (D := D) π σ γ p c := by
    intro hcons
    obtain ⟨_, hc, _, _, hex⟩ := hcons
    obtain ⟨_, _, _, n, R, input, ρ, τ, hemp, hge, _⟩ := hex
    refine ⟨hc, ?_⟩
    intro j₀ W hsucc
    obtain ⟨hρ, _, himb⟩ := hemp
    obtain ⟨C, T, hT, hTle, hunit, hgram⟩ := himb j₀ W hsucc
    have hcert := gram_exact_state_conversion_filteredCert input ρ τ C hT hunit hρ hgram
    have hfg := filteredGamma2_le_of_gramFilteredCert hcert
    have hle : ENNReal.ofReal (c / Real.sqrt (levelMass π σ γ))
        ≤ ENNReal.ofReal (2 * T) := le_trans hge hfg
    have hreal : c / Real.sqrt (levelMass π σ γ) ≤ 2 * (T : ℝ) :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
    have hTreal : (T : ℝ) ≤ (preparedInputQueries W : ℝ) := by exact_mod_cast hTle
    have hne : Real.sqrt (levelMass π σ γ) ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos hmass)
    have hhalf : c / (2 * Real.sqrt (levelMass π σ γ)) ≤ (preparedInputQueries W : ℝ) := by
      have hid : c / (2 * Real.sqrt (levelMass π σ γ))
          = (c / Real.sqrt (levelMass π σ γ)) / 2 := by field_simp
      rw [hid]
      linarith
    exact hhalf

  have hzero : ∀ (j₀ : Fin m × Fin D) (W : List (PreparedStep ((Fin m × Fin D) × Bool))),
      ReweightingSuccess j₀ π σ γ p W → preparedInputQueries W = 0 →
        ¬ FilteredGamma2LowerConsumer (D := D) π σ γ p δ c cδ :=
    fun j₀ W hsucc hzero => gext3_filtered_consumer_of_zero_query_word π σ γ p c cδ δ
      hmass hsucc hzero

  have heasy : ¬ FilteredGamma2LowerConsumer (D := 1) easyPi easySig (1 : ℝ) 1 (0 : ℝ) 1 1 := by
    have hmass' : 0 < levelMass easyPi easySig (1 : ℝ) := by
      have hm : levelMass easyPi easySig (1 : ℝ) = 1 := by
        unfold levelMass levelFill easyPi easySig
        rw [Fin.sum_univ_one]
        norm_num
      rw [hm]; norm_num
    exact gext3_filtered_consumer_of_zero_query_word easyPi easySig (1 : ℝ) 1 1 1 0 hmass'
      easyInstance_success (by
        show preparedInputQueries (List.nil : List (PreparedStep ((Fin 1 × Fin 1) × Bool))) = 0
        rfl)
  exact ⟨hbound, hzero, heasy⟩

end Qatlib.Concepts.Waterfill.LevelFidelity
