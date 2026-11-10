/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WaterLevel.WaterPrecision.CoherentReweightingDefs
import Qatlib.Concepts.Waterfill.LevelFidelity.RealTableWaterLevel
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 2000000

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
open Qatlib.Concepts.WaterLevel.WaterPrecision
open scoped BigOperators ComplexOrder

open Qatlib.Concepts.NativeNumerics.WaterFilling
open Qatlib.Concepts.Waterfill.LevelFidelity.RealTableWaterLevel
open Qatlib.Concepts.Waterfill.LevelSearch

namespace Qatlib.Concepts.Waterfill.LevelFidelity.EffectiveFidelitySearch
variable {m : ℕ} (π σ : Fin m → ℝ)
variable {m : ℕ} (π σ : Fin m → ℚ)

theorem computedWaterHigh_pos (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) :
    1 ≤ computedWaterHigh π σ := by
  have hsum : (0 : ℚ) ≤ ∑ j, π j / σ j :=
    Finset.sum_nonneg fun j _ => div_nonneg (hπ j) (hσ j)
  unfold computedWaterHigh
  linarith

theorem waterFill_zero (hπ : ∀ j, 0 ≤ π j) (j : Fin m) : waterFill π σ 0 j = 0 := by
  unfold waterFill
  rw [zero_mul, min_eq_right (hπ j)]

theorem computedMass_dot_zero (hπ : ∀ j, 0 ≤ π j) :
    computedMass π σ 0 = 0 ∧ computedDot π σ 0 = 0 := by
  refine ⟨?_, ?_⟩
  · show (∑ j, (waterFill π σ 0 j)^2) = 0
    exact Finset.sum_eq_zero fun j _ => by rw [waterFill_zero π σ hπ j]; ring
  · show (∑ j, σ j * waterFill π σ 0 j) = 0
    exact Finset.sum_eq_zero fun j _ => by rw [waterFill_zero π σ hπ j]; ring

private theorem fidelityBracket_props {m : ℕ} (π σ : Fin m → ℚ) (q : ℚ)
    (hH0 : 0 ≤ computedWaterHigh π σ)
    (hr0 : fidelityReaches π σ q 0)
    (hnr : ¬ fidelityReaches π σ q (computedWaterHigh π σ))
    (k : ℕ) :
    let b := fidelityBracket π σ q k
    0 ≤ b.1 ∧ b.1 ≤ b.2 ∧ b.2 ≤ computedWaterHigh π σ ∧
      b.2 - b.1 = computedWaterHigh π σ / 2 ^ k ∧
      fidelityReaches π σ q b.1 ∧ ¬ fidelityReaches π σ q b.2 := by
  induction k with
  | zero =>
    dsimp only [fidelityBracket]
    refine ⟨le_rfl, hH0, le_rfl, ?_, hr0, hnr⟩
    rw [pow_zero, div_one, sub_zero]
  | succ k ih =>
    dsimp only [fidelityBracket]
    obtain ⟨hl, hll, hlu, hw, hrl, hru⟩ := ih
    split_ifs with hmid
    · refine ⟨?_, ?_, hlu, ?_, hmid, hru⟩
      · nlinarith
      · nlinarith
      · have h2 : (fidelityBracket π σ q k).2 -
            ((fidelityBracket π σ q k).1 + (fidelityBracket π σ q k).2) / 2 =
            ((fidelityBracket π σ q k).2 - (fidelityBracket π σ q k).1) / 2 := by
          ring
        rw [h2, hw, pow_succ, div_div]
    · refine ⟨hl, ?_, ?_, ?_, hrl, hmid⟩
      · nlinarith
      · nlinarith
      · have h2 : ((fidelityBracket π σ q k).1 + (fidelityBracket π σ q k).2) / 2 -
            (fidelityBracket π σ q k).1 =
            ((fidelityBracket π σ q k).2 - (fidelityBracket π σ q k).1) / 2 := by
          ring
        rw [h2, hw, pow_succ, div_div]

private theorem schedule_windows (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    1 / 2 ≤ resamplingExactScale β ∧ resamplingExactScale β ≤ 1 ∧
      0 < resamplingExactAngle β ∧ resamplingExactAngle β ≤ Real.pi / 2 ∧
      Real.sin (resamplingExactAngle β) = resamplingExactScale β * β ∧
      (2 * (resamplingExactRounds β : ℝ) + 1) * resamplingExactAngle β = Real.pi / 2 ∧
      ((2 * resamplingExactRounds β + 1 : ℕ) : ℝ) ≤ Real.pi / (2 * β) + 2 ∧
      (β = 1 → resamplingExactRounds β = 0 ∧ resamplingExactScale β = 1) ∧
      β / 2 ≤ Real.sin (resamplingExactAngle β) ∧
      Real.sin (resamplingExactAngle β) ≤ β ∧
      (∀ β' δ : ℝ, 0 ≤ δ → |β - β'| ≤ δ →
        (β' - δ) / 2 ≤ Real.sin (resamplingExactAngle β) ∧
          Real.sin (resamplingExactAngle β) ≤ β' + δ) := by
  obtain ⟨hscaleLo, hscaleHi, hangPos, hangHi, hsin, htotal, hqueries, hend⟩ :=
    resamplingExactSchedule β hβ hβ1
  have hβ0 : 0 ≤ β := le_of_lt hβ
  refine ⟨hscaleLo, hscaleHi, hangPos, hangHi, hsin, htotal, hqueries, hend, ?_, ?_, ?_⟩
  · rw [hsin]
    nlinarith [hscaleLo]
  · rw [hsin]
    nlinarith [hscaleHi]
  · intro β' δ hδ happrox
    have habs := abs_le.mp happrox
    constructor
    · rw [hsin]
      nlinarith [hscaleLo]
    · rw [hsin]
      nlinarith [hscaleHi]

theorem gext2 :
    ∀ (m : ℕ) (π σ : Fin m → ℚ) (p : ℚ),
    (∀ i, 0 ≤ π i) → (∀ i, 0 ≤ σ i) →
    (∑ i, (π i : ℝ) ^ 2) = 1 → (∑ i, (σ i : ℝ) ^ 2) = 1 →
    computedFidelity π σ (computedWaterHigh π σ) < p →
    p ≤ computedPmax π σ →
    (∀ k : ℕ,
      let b := fidelityBracket π σ p k
      0 ≤ b.1 ∧ b.1 ≤ b.2 ∧ b.2 ≤ computedWaterHigh π σ ∧
      b.2 - b.1 = computedWaterHigh π σ / 2 ^ k ∧
      fidelityReaches π σ p b.1 ∧ ¬ fidelityReaches π σ p b.2 ∧
      (searchWork m k).divisions = m ∧
      (searchWork m k).energyEvaluations = m * k ∧
      (searchWork m k).comparisons = k) ∧
    (∀ k : ℕ,
      ∃ γbar : ℝ,
        |(selectedLevel π σ p k : ℝ) - γbar| ≤
          ((computedWaterHigh π σ : ℝ) / 2 ^ k) ∧
        realDot (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) γbar ^ 2 =
          (p : ℝ) * realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) γbar) ∧
    (∀ (p' : ℚ) (k : ℕ), p ≤ p' → p' ≤ computedPmax π σ →
      selectedLevel π σ p' k ≤ selectedLevel π σ p k + computedWaterHigh π σ / 2 ^ k) ∧
    (∀ k : ℕ,
      let γhat := selectedLevel π σ p k
      let βhat := selectedBeta π σ γhat
      let sch := selectedSchedule π σ γhat
      0 < βhat → βhat ≤ 1 →
      1 / 2 ≤ sch.2.2 ∧ sch.2.2 ≤ 1 ∧
      0 < sch.2.1 ∧ sch.2.1 ≤ Real.pi / 2 ∧
      Real.sin sch.2.1 = sch.2.2 * βhat ∧
      (2 * (sch.1 : ℝ) + 1) * sch.2.1 = Real.pi / 2 ∧
      ((2 * sch.1 + 1 : ℕ) : ℝ) ≤ Real.pi / (2 * βhat) + 2 ∧
      (βhat = 1 → sch.1 = 0 ∧ sch.2.2 = 1) ∧
      βhat / 2 ≤ Real.sin sch.2.1 ∧ Real.sin sch.2.1 ≤ βhat ∧
      (∀ β δ : ℝ, 0 ≤ δ → |βhat - β| ≤ δ →
        (β - δ) / 2 ≤ Real.sin sch.2.1 ∧ Real.sin sch.2.1 ≤ β + δ)) := by
  intro m π σ p hπ hσ hπn hσn hfid hmax
  have hπ1 : (∑ i, π i ^ 2) = 1 := by exact_mod_cast hπn
  have hσ1 : (∑ i, σ i ^ 2) = 1 := by exact_mod_cast hσn
  have nonnegMass : ∀ γ : ℚ, 0 ≤ computedMass π σ γ := by
    intro γ
    show 0 ≤ ∑ i, (waterFill π σ γ i) ^ 2
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hH1 : 1 ≤ computedWaterHigh π σ := computedWaterHigh_pos π σ hπ hσ
  have hH0 : 0 ≤ computedWaterHigh π σ := le_trans (by norm_num : (0:ℚ) ≤ 1) hH1
  have hfp : 0 ≤ computedFidelity π σ (computedWaterHigh π σ) := by
    unfold computedFidelity
    split_ifs with hm
    · exact le_rfl
    · have hpos : 0 ≤ computedMass π σ (computedWaterHigh π σ) := nonnegMass _
      have hne : computedMass π σ (computedWaterHigh π σ) ≠ 0 := hm
      refine div_nonneg (sq_nonneg _) ?_
      by_contra hng
      push Not at hng
      exact hne (le_antisymm hng.le hpos)
  have hp : 0 < p := lt_of_le_of_lt hfp hfid
  have hex : ∃ i, 0 < π i ∧ 0 < σ i := by
    by_contra hn
    have hn' : ∀ i, 0 < π i → σ i = 0 := by
      intro i hi
      by_contra h
      exact hn ⟨i, hi, lt_of_le_of_ne (hσ i) (Ne.symm h)⟩
    have hzero : computedPmax π σ = 0 := by
      unfold computedPmax
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : 0 < π i
      · rw [if_pos hi, hn' i hi]
        ring
      · rw [if_neg hi]
    linarith
  obtain ⟨i₀, hi₀π, hi₀σ⟩ := hex
  have hfillH : 0 < waterFill π σ (computedWaterHigh π σ) i₀ := by
    unfold waterFill
    refine lt_min hi₀π ?_
    exact mul_pos (lt_of_lt_of_le (by norm_num) hH1) hi₀σ
  have hmassH : 0 < computedMass π σ (computedWaterHigh π σ) := by
    show 0 < ∑ i, (waterFill π σ (computedWaterHigh π σ) i) ^ 2
    exact Finset.sum_pos' (f := fun i => (waterFill π σ (computedWaterHigh π σ) i) ^ 2)
      (fun i _ => sq_nonneg _) ⟨i₀, Finset.mem_univ i₀, sq_pos_of_pos hfillH⟩
  have hfidH : computedFidelity π σ (computedWaterHigh π σ)
      = computedDot π σ (computedWaterHigh π σ) ^ 2 / computedMass π σ (computedWaterHigh π σ) := by
    unfold computedFidelity
    rw [if_neg (ne_of_gt hmassH)]
  have hnrH : ¬ fidelityReaches π σ p (computedWaterHigh π σ) := by
    intro hc
    unfold fidelityReaches at hc
    have hlt : computedDot π σ (computedWaterHigh π σ) ^ 2
        / computedMass π σ (computedWaterHigh π σ) < p := by
      rw [← hfidH]; exact hfid
    exact absurd ((div_lt_iff₀ hmassH).mp hlt) (not_lt.mpr hc)
  have reaches0 : ∀ q : ℚ, fidelityReaches π σ q 0 := by
    intro q
    unfold fidelityReaches
    rw [(computedMass_dot_zero π σ hπ).2, (computedMass_dot_zero π σ hπ).1, mul_zero]
    exact sq_nonneg _
  have nrH_of_le : ∀ q : ℚ, p ≤ q → ¬ fidelityReaches π σ q (computedWaterHigh π σ) := by
    intro q hpq hc
    unfold fidelityReaches at hc
    have hlt : computedDot π σ (computedWaterHigh π σ) ^ 2
        / computedMass π σ (computedWaterHigh π σ) < p := by
      rw [← hfidH]; exact hfid
    have hpos : 0 < computedMass π σ (computedWaterHigh π σ) := hmassH
    have h1 : computedDot π σ (computedWaterHigh π σ) ^ 2 < p * computedMass π σ (computedWaterHigh π σ) :=
      (div_lt_iff₀ hpos).mp hlt
    nlinarith [nonnegMass (computedWaterHigh π σ)]

  have antiRat : ∀ (a b : ℚ), 0 ≤ a → a ≤ b →
      computedDot π σ b ^ 2 * computedMass π σ a ≤
        computedDot π σ a ^ 2 * computedMass π σ b := by
    intro a b ha hab
    have h := realFidelity_anti (m := m) (fun i => (π i : ℝ)) (fun i => (σ i : ℝ))
      (fun i => Rat.cast_nonneg.mpr (hπ i)) (fun i => Rat.cast_nonneg.mpr (hσ i))
      (Rat.cast_nonneg.mpr ha) (Rat.cast_le.mpr hab)
    rw [realDot_cast, realMass_cast, realDot_cast, realMass_cast] at h
    exact_mod_cast h

  have hdown : ∀ (q γ γ' : ℚ), 0 ≤ γ → γ ≤ γ' →
      fidelityReaches π σ q γ' → fidelityReaches π σ q γ := by
    intro q γ γ' hγ0 hle hreach
    unfold fidelityReaches at hreach ⊢
    rcases eq_or_lt_of_le hγ0 with hγ | hγ
    · subst hγ
      rw [(computedMass_dot_zero π σ hπ).2, (computedMass_dot_zero π σ hπ).1, mul_zero]
      exact sq_nonneg _
    · have hanti := antiRat γ γ' hγ.le hle
      by_cases hm' : computedMass π σ γ' = 0
      · have hmono : computedMass π σ γ ≤ computedMass π σ γ' := by
          show computedWaterEnergy π σ γ ≤ computedWaterEnergy π σ γ'
          exact computedWaterEnergy_mono π σ (fun i => ⟨hπ i, hσ i⟩) hγ.le hle
        rw [hm'] at hmono
        have hmg : computedMass π σ γ = 0 := le_antisymm hmono (nonnegMass γ)
        rw [hmg, mul_zero]
        exact sq_nonneg _
      · have hpos : 0 < computedMass π σ γ' :=
          lt_of_le_of_ne (nonnegMass γ') (Ne.symm hm')
        have step2 : q * computedMass π σ γ' * computedMass π σ γ ≤
            computedDot π σ γ' ^ 2 * computedMass π σ γ := by nlinarith [nonnegMass γ]
        have step3 : computedDot π σ γ' ^ 2 * computedMass π σ γ ≤
            computedDot π σ γ ^ 2 * computedMass π σ γ' := hanti
        nlinarith [hpos, nonnegMass γ]
  have hsub : ∀ (q γ : ℚ), p ≤ q → fidelityReaches π σ q γ → fidelityReaches π σ p γ := by
    intro q γ hpq hreach
    unfold fidelityReaches at hreach ⊢
    nlinarith [nonnegMass γ]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    (try dsimp only)
    obtain ⟨hl, hll, hlu, hw, hrl, hru⟩ :=
      fidelityBracket_props π σ p hH0 (reaches0 p) hnrH k
    exact ⟨hl, hll, hlu, hw, hrl, hru, by rfl, by rfl, by rfl⟩
  · intro k
    obtain ⟨hl, hll, hlu, hw, hrl, hru⟩ :=
      fidelityBracket_props π σ p hH0 (reaches0 p) hnrH k
    have contFill : ∀ i, Continuous (fun γ : ℝ =>
        realFill (fun j => (π j : ℝ)) (fun j => (σ j : ℝ)) γ i) := by
      intro i
      unfold realFill
      fun_prop
    have hcont : Continuous (fun γ : ℝ =>
        realDot (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) γ ^ 2 -
          (p : ℝ) * realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) γ) := by
      apply Continuous.sub
      · exact Continuous.pow (continuous_finsetSum Finset.univ fun i _ =>
          continuous_const.mul (contFill i)) 2
      · exact continuous_const.mul (continuous_finsetSum Finset.univ fun i _ =>
          (contFill i).pow 2)
    have hgl : (0 : ℝ) ≤
        realDot (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) (fidelityBracket π σ p k).1 ^ 2 -
          (p : ℝ) * realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) (fidelityBracket π σ p k).1 := by
      have h := hrl
      unfold fidelityReaches at h
      rw [realDot_cast, realMass_cast]
      exact_mod_cast (sub_nonneg.mpr h)
    have hgu :
        realDot (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) (fidelityBracket π σ p k).2 ^ 2 -
          (p : ℝ) * realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) (fidelityBracket π σ p k).2 < 0 := by
      have h := hru
      unfold fidelityReaches at h
      rw [realDot_cast, realMass_cast]
      exact_mod_cast (sub_neg.mpr (lt_of_not_ge h))
    have hle : ((fidelityBracket π σ p k).1 : ℝ) ≤ (fidelityBracket π σ p k).2 :=
      by exact_mod_cast hll
    have hivt := intermediate_value_Icc' hle hcont.continuousOn
    have hzero : (0 : ℝ) ∈ Set.Icc
        (realDot (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) (fidelityBracket π σ p k).2 ^ 2 -
          (p : ℝ) * realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) (fidelityBracket π σ p k).2)
        (realDot (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) (fidelityBracket π σ p k).1 ^ 2 -
          (p : ℝ) * realMass (fun i => (π i : ℝ)) (fun i => (σ i : ℝ)) (fidelityBracket π σ p k).1) :=
      ⟨hgu.le, hgl⟩
    obtain ⟨γbar, hmem, hg⟩ := (Set.mem_image _ _ _).mp (hivt hzero)
    have hbounds := Set.mem_Icc.mp hmem
    have hcast : ((fidelityBracket π σ p k).2 : ℝ) - ((fidelityBracket π σ p k).1 : ℝ)
        = ((computedWaterHigh π σ : ℝ) / 2 ^ k) := by
      rw [← Rat.cast_sub, hw]
      push_cast
      rfl
    refine ⟨γbar, ?_, sub_eq_zero.mp hg⟩
    have hsel : ((selectedLevel π σ p k : ℚ) : ℝ) = ((fidelityBracket π σ p k).2 : ℝ) := rfl
    rw [hsel]
    have hR : (0 : ℝ) ≤ ((computedWaterHigh π σ : ℝ) / 2 ^ k) :=
      div_nonneg (Rat.cast_nonneg.mpr hH0) (pow_nonneg (by norm_num) k)
    refine abs_le.mpr ⟨?_, ?_⟩
    · nlinarith [hbounds.2]
    · nlinarith [hcast, hbounds.1]
  · intro p' k hpp' hp'max
    have hnr' : ¬ fidelityReaches π σ p' (computedWaterHigh π σ) := nrH_of_le p' hpp'
    obtain ⟨hl, hll, hlu, hw, hrl, hru⟩ :=
      fidelityBracket_props π σ p' hH0 (reaches0 p') hnr' k
    obtain ⟨hl0, hll0, hlu0, hw0, hrl0, hru0⟩ :=
      fidelityBracket_props π σ p hH0 (reaches0 p) hnrH k
    have hu0 : (0 : ℚ) ≤ (fidelityBracket π σ p k).2 := le_trans hl0 hll0
    have hmem' : fidelityReaches π σ p (fidelityBracket π σ p' k).1 := hsub p' _ hpp' hrl
    have hgoal : (fidelityBracket π σ p' k).2
        ≤ (fidelityBracket π σ p k).2 + computedWaterHigh π σ / 2 ^ k := by
      by_contra hn
      have hlt : (fidelityBracket π σ p k).2 < (fidelityBracket π σ p' k).1 := by
        nlinarith
      exact hru0 (hdown p (fidelityBracket π σ p k).2 (fidelityBracket π σ p' k).1
        hu0 (le_of_lt hlt) hmem')
    have hsel' : selectedLevel π σ p' k = (fidelityBracket π σ p' k).2 := rfl
    have hsel : selectedLevel π σ p k = (fidelityBracket π σ p k).2 := rfl
    rw [hsel', hsel]
    exact hgoal
  · intro k
    (try dsimp only)
    intro hβ hβ1
    exact schedule_windows (selectedBeta π σ (selectedLevel π σ p k)) hβ hβ1
end Qatlib.Concepts.Waterfill.LevelFidelity.EffectiveFidelitySearch
