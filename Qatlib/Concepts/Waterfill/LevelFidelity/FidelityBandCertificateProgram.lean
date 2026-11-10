/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySearchDriver
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.NativeNumerics.WaterFilling
open Qatlib.Concepts.Waterfill.LevelFidelity.EffectiveFidelitySearch
open Qatlib.Concepts.Waterfill.LevelSearch
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.Waterfill.LevelFidelity.FidelityBandCertificateProgram

open Qatlib
open Qatlib
open Qatlib.Concepts.Waterfill.LevelFidelity.RealTableWaterLevel
open Qatlib.Concepts.WaterLevel.WaterPrecision
open Qatlib.Concepts.Waterfill.ExactResampling
open Qatlib
open Qatlib.Concepts.Waterfill.LevelFidelity.WaterLevelFidelity
open Qatlib.Concepts.Waterfill.LevelFidelity.FidelityBracketCertifiedSearch
open Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySearchDriver
open scoped BigOperators

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

def crossBreakSource : Fin 3 → ℚ := fun i =>
  if i.val = 0 then 1 / 4 else if i.val = 1 then 1 / 2 else 3 / 4

def crossBreakTarget : Fin 3 → ℚ := fun _ => 1

def crossBreakFidelity : ℚ := 25 / 9

def crossBreakRate : ℚ := 1 / 4

theorem crossBreakSource_nonneg : ∀ j, 0 ≤ crossBreakSource j := by
  intro j
  fin_cases j <;> norm_num [crossBreakSource]

theorem crossBreakTarget_nonneg : ∀ j, 0 ≤ crossBreakTarget j := by
  intro j
  simp [crossBreakTarget]

theorem crossBreakFidelity_pos : 0 < crossBreakFidelity := by
  norm_num [crossBreakFidelity]

theorem crossBreak_fin3_sum (f : Fin 3 → ℚ) : (∑ j : Fin 3, f j) = f 0 + f 1 + f 2 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  ring

theorem crossBreak_satDot_low :
    satDot crossBreakSource crossBreakTarget ({0} : Finset (Fin 3)) = 1 / 4 := by
  unfold satDot
  rw [crossBreak_fin3_sum]
  simp only [Finset.mem_singleton]
  simp
  norm_num [crossBreakSource, crossBreakTarget]

theorem crossBreak_freeSq_low :
    freeSq crossBreakSource crossBreakTarget ({0} : Finset (Fin 3)) = 2 := by
  unfold freeSq
  rw [crossBreak_fin3_sum]
  simp only [Finset.mem_singleton]
  simp
  norm_num [crossBreakSource, crossBreakTarget]

theorem crossBreak_satDot_high :
    satDot crossBreakSource crossBreakTarget ({0, 1} : Finset (Fin 3)) = 3 / 4 := by
  unfold satDot
  rw [crossBreak_fin3_sum]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  simp
  norm_num [crossBreakSource, crossBreakTarget]

theorem crossBreak_freeSq_high :
    freeSq crossBreakSource crossBreakTarget ({0, 1} : Finset (Fin 3)) = 1 := by
  unfold freeSq
  rw [crossBreak_fin3_sum]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  simp
  norm_num [crossBreakSource, crossBreakTarget]

theorem crossBreak_sat_of_below {γ : ℚ} (hlo : 2045 / 4096 ≤ γ) (hhi : γ < 1 / 2) :
    satSet crossBreakSource crossBreakTarget γ = ({0} : Finset (Fin 3)) := by
  ext j
  fin_cases j <;>
    simp [satSet, crossBreakSource, crossBreakTarget] <;>
    norm_num at hlo hhi ⊢ <;> linarith

theorem crossBreak_sat_of_above {γ : ℚ} (hlo : 1 / 2 < γ) (hhi : γ ≤ 515 / 1024) :
    satSet crossBreakSource crossBreakTarget γ = ({0, 1} : Finset (Fin 3)) := by
  ext j
  fin_cases j <;>
    simp [satSet, crossBreakSource, crossBreakTarget] <;>
    norm_num at hlo hhi ⊢ <;> linarith

theorem crossBreak_slope_low (γ₁ γ₂ : ℚ) :
    pieceSegmentSlope crossBreakSource crossBreakTarget crossBreakFidelity
      ({0} : Finset (Fin 3)) γ₁ γ₂ = -(14 / 9) * (γ₁ + γ₂) + 1 := by
  rw [pieceSegmentSlope, crossBreak_satDot_low, crossBreak_freeSq_low]
  norm_num [crossBreakFidelity]

theorem crossBreak_slope_high (γ₁ γ₂ : ℚ) :
    pieceSegmentSlope crossBreakSource crossBreakTarget crossBreakFidelity
      ({0, 1} : Finset (Fin 3)) γ₁ γ₂ = -(16 / 9) * (γ₁ + γ₂) + 3 / 2 := by
  rw [pieceSegmentSlope, crossBreak_satDot_high, crossBreak_freeSq_high]
  norm_num [crossBreakFidelity]

theorem crossBreak_piece_break :
    pieceBreak crossBreakSource crossBreakTarget (1 / 2) ({0} : Finset (Fin 3))
      ({0, 1} : Finset (Fin 3)) := by
  intro j hj
  have hjmem : j ∈ ({0, 1} : Finset (Fin 3)) ∧ j ∉ ({0} : Finset (Fin 3)) :=
    Finset.mem_sdiff.mp hj
  have h1 : j = 0 ∨ j = 1 := by
    rcases Finset.mem_insert.mp hjmem.1 with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_singleton.mp h)
  have h2 : j ≠ 0 := by
    intro hc
    exact hjmem.2 (by rw [hc]; simp)
  rcases h1 with h | h
  · exact absurd h h2
  · subst h
    exact ⟨by norm_num [crossBreakSource], by norm_num [crossBreakSource, crossBreakTarget]⟩

theorem crossBreak_chainRate_low {γ₁ γ₂ : ℚ}
    (hlo₁ : 2045 / 4096 ≤ γ₁) (hhi₁ : γ₁ < 1 / 2)
    (hlo₂ : 2045 / 4096 ≤ γ₂) (hhi₂ : γ₂ < 1 / 2) (hlt : γ₁ < γ₂) :
    chainPieceRate crossBreakSource crossBreakTarget crossBreakFidelity γ₁ γ₂ crossBreakRate := by
  let segs : List (ChainSegment (m := 3)) := [⟨{0}, γ₁, γ₂⟩]
  refine ⟨segs, by simp [segs], ?_, Or.inr ?_, Or.inl ?_⟩
  · simp only [segs, ChainWellFormed]
    exact ⟨by linarith, hlt.le⟩
  · simp only [segs, chainSlopeLowerDown, chainMin, crossBreak_slope_low]
    unfold crossBreakRate
    norm_num at *
    linarith
  · refine ⟨by simp [segs, chainFirstSeg], by simp [segs, chainLastSeg], ?_, ?_⟩
    · simpa [segs, chainFirstSeg] using! crossBreak_sat_of_below hlo₁ hhi₁
    · simpa [segs, chainLastSeg] using! crossBreak_sat_of_below hlo₂ hhi₂

theorem crossBreak_chainRate_high {γ₁ γ₂ : ℚ}
    (hlo₁ : 1 / 2 < γ₁) (hhi₁ : γ₁ ≤ 515 / 1024)
    (hlo₂ : 1 / 2 < γ₂) (hhi₂ : γ₂ ≤ 515 / 1024) (hlt : γ₁ < γ₂) :
    chainPieceRate crossBreakSource crossBreakTarget crossBreakFidelity γ₁ γ₂ crossBreakRate := by
  let segs : List (ChainSegment (m := 3)) := [⟨{0, 1}, γ₁, γ₂⟩]
  refine ⟨segs, by simp [segs], ?_, Or.inr ?_, Or.inl ?_⟩
  · simp only [segs, ChainWellFormed]
    exact ⟨by linarith, hlt.le⟩
  · simp only [segs, chainSlopeLowerDown, chainMin, crossBreak_slope_high]
    unfold crossBreakRate
    norm_num at *
    linarith
  · refine ⟨by simp [segs, chainFirstSeg], by simp [segs, chainLastSeg], ?_, ?_⟩
    · simpa [segs, chainFirstSeg] using! crossBreak_sat_of_above hlo₁ hhi₁
    · simpa [segs, chainLastSeg] using! crossBreak_sat_of_above hlo₂ hhi₂

theorem crossBreak_chainRate_cross {γ₁ γ₂ : ℚ}
    (hlo₁ : 2045 / 4096 ≤ γ₁) (hhi₁ : γ₁ < 1 / 2)
    (hlo₂ : 1 / 2 < γ₂) (hhi₂ : γ₂ ≤ 515 / 1024) :
    chainPieceRate crossBreakSource crossBreakTarget crossBreakFidelity γ₁ γ₂ crossBreakRate := by
  let segs : List (ChainSegment (m := 3)) :=
    [⟨{0}, γ₁, 1 / 2⟩, ⟨{0, 1}, 1 / 2, γ₂⟩]
  refine ⟨segs, by simp [segs], ?_, Or.inr ?_, Or.inl ?_⟩
  · simp only [segs, ChainWellFormed]
    exact ⟨by linarith, hhi₁.le, trivial, by simp, crossBreak_piece_break, by linarith, hlo₂.le⟩
  · simp only [segs, chainSlopeLowerDown, chainMin, crossBreak_slope_low,
      crossBreak_slope_high]
    unfold crossBreakRate
    apply le_min <;> norm_num at * <;> linarith
  · refine ⟨by simp [segs, chainFirstSeg], by simp [segs, chainLastSeg], ?_, ?_⟩
    · simpa [segs, chainFirstSeg] using! crossBreak_sat_of_below hlo₁ hhi₁
    · simpa [segs, chainLastSeg] using! crossBreak_sat_of_above hlo₂ hhi₂

theorem crossBreak_chainRate_ordered {γ₁ γ₂ : ℚ}
    (hlo₁ : 2045 / 4096 ≤ γ₁) (hhi₁ : γ₁ ≤ 515 / 1024)
    (hlo₂ : 2045 / 4096 ≤ γ₂) (hhi₂ : γ₂ ≤ 515 / 1024)
    (hne₁ : γ₁ ≠ 1 / 2) (hne₂ : γ₂ ≠ 1 / 2) (hlt : γ₁ < γ₂) :
    chainPieceRate crossBreakSource crossBreakTarget crossBreakFidelity γ₁ γ₂ crossBreakRate := by
  rcases lt_or_gt_of_ne hne₁ with h₁ | h₁
  · rcases lt_or_gt_of_ne hne₂ with h₂ | h₂
    · exact crossBreak_chainRate_low hlo₁ h₁ hlo₂ h₂ hlt
    · exact crossBreak_chainRate_cross hlo₁ h₁ h₂ hhi₂
  · rcases lt_or_gt_of_ne hne₂ with h₂ | h₂
    · linarith
    · exact crossBreak_chainRate_high h₁ hhi₁ h₂ hhi₂ hlt

theorem chainPieceRate_symm {m : ℕ} (π σ : Fin m → ℚ) (p c γ₁ γ₂ : ℚ)
    (h : chainPieceRate π σ p γ₁ γ₂ c) : chainPieceRate π σ p γ₂ γ₁ c := by
  obtain ⟨segs, hne, hv, hrate, hends⟩ := h
  refine ⟨segs, hne, hv, hrate, ?_⟩
  rcases hends with hends | hends
  · exact Or.inr hends
  · exact Or.inl hends

theorem crossBreak_chainRate {γ₁ γ₂ : ℚ}
    (hlo₁ : 2045 / 4096 ≤ γ₁) (hhi₁ : γ₁ ≤ 515 / 1024)
    (hlo₂ : 2045 / 4096 ≤ γ₂) (hhi₂ : γ₂ ≤ 515 / 1024)
    (hne₁ : γ₁ ≠ 1 / 2) (hne₂ : γ₂ ≠ 1 / 2) (hne : γ₁ ≠ γ₂) :
    chainPieceRate crossBreakSource crossBreakTarget crossBreakFidelity γ₁ γ₂ crossBreakRate := by
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact crossBreak_chainRate_ordered hlo₁ hhi₁ hlo₂ hhi₂ hne₁ hne₂ hlt
  · exact chainPieceRate_symm crossBreakSource crossBreakTarget crossBreakFidelity crossBreakRate
      _ _ (crossBreak_chainRate_ordered hlo₂ hhi₂ hlo₁ hhi₁ hne₂ hne₁ hlt)

theorem crossBreak_levels :
    bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 0 = 5 / 4 ∧
    bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 1 = 5 / 8 ∧
    bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 2 = 5 / 16 ∧
    bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 3 = 15 / 32 ∧
    bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 4 = 35 / 64 ∧
    bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 5 = 65 / 128 ∧
    bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 6 = 125 / 256 ∧
    bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 7 = 255 / 512 ∧
    bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 8 = 515 / 1024 ∧
    bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 9 = 1025 / 2048 ∧
    bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 10 = 2045 / 4096 ∧
    bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 11 = 4095 / 8192 ∧
    bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 12 = 8195 / 16384 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals norm_num [bracketMidpoint, fidelityBracket, computedDot, computedMass,
    computedWaterEnergy, waterFill, computedWaterHigh, crossBreakSource, crossBreakTarget,
    crossBreakFidelity, Fin.sum_univ_succ]

theorem crossBreak_gaps :
    fidelityGap crossBreakSource crossBreakTarget crossBreakFidelity
        (bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 0) = -(13 / 72) ∧
    fidelityGap crossBreakSource crossBreakTarget crossBreakFidelity
        (bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 1) = -(1 / 16) ∧
    fidelityGap crossBreakSource crossBreakTarget crossBreakFidelity
        (bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 2) = 19 / 384 ∧
    fidelityGap crossBreakSource crossBreakTarget crossBreakFidelity
        (bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 3) = 73 / 4608 ∧
    fidelityGap crossBreakSource crossBreakTarget crossBreakFidelity
        (bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 4) = -(13 / 768) ∧
    fidelityGap crossBreakSource crossBreakTarget crossBreakFidelity
        (bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 5) = -(7 / 3072) ∧
    fidelityGap crossBreakSource crossBreakTarget crossBreakFidelity
        (bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 6) = 619 / 98304 ∧
    fidelityGap crossBreakSource crossBreakTarget crossBreakFidelity
        (bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 7) = 1273 / 1179648 ∧
    fidelityGap crossBreakSource crossBreakTarget crossBreakFidelity
        (bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 8) = -(163 / 196608) ∧
    fidelityGap crossBreakSource crossBreakTarget crossBreakFidelity
        (bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 9) = -(107 / 786432) ∧
    fidelityGap crossBreakSource crossBreakTarget crossBreakFidelity
        (bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 10) = 10219 / 25165824 ∧
    fidelityGap crossBreakSource crossBreakTarget crossBreakFidelity
        (bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 11) = 20473 / 301989888 ∧
    fidelityGap crossBreakSource crossBreakTarget crossBreakFidelity
        (bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 12) = -(2563 / 50331648) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals norm_num [fidelityGap, bracketMidpoint, fidelityBracket, computedDot, computedMass,
    computedWaterEnergy, waterFill, computedWaterHigh, crossBreakSource, crossBreakTarget,
    crossBreakFidelity, Fin.sum_univ_succ]

theorem crossBreak_band_bound :
    ambiguityBandBound crossBreakSource crossBreakTarget 15 crossBreakFidelity
      = 1703963 / 1610612736 := by
  norm_num [ambiguityBandBound, computedDot, computedMass, computedWaterEnergy, waterFill,
    computedWaterHigh, crossBreakSource, crossBreakTarget, crossBreakFidelity, gridStep,
    Fin.sum_univ_succ]

theorem crossBreak_band_depth :
    ∀ j, j < 13 →
      (|fidelityGap crossBreakSource crossBreakTarget crossBreakFidelity
          (bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity j)|
        ≤ ambiguityBandBound crossBreakSource crossBreakTarget 15 crossBreakFidelity) →
      j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 := by
  intro j hj hband
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, thresholdGoal, clause11, clause12⟩ :=
      crossBreak_gaps
  have hB := crossBreak_band_bound
  interval_cases j <;>
    norm_num [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, thresholdGoal, clause11, clause12, hB] at hband <;>
    first
    | exact hband.elim
    | decide

theorem crossBreak_bandRate :
    bandRate crossBreakSource crossBreakTarget 15 crossBreakFidelity crossBreakRate 13 := by
  apply bandRate_of_chain_lower crossBreakSource crossBreakTarget 15 crossBreakFidelity
    crossBreakRate 13 crossBreakSource_nonneg crossBreakTarget_nonneg
    (by norm_num [crossBreakRate])
  intro j j' hj hj' hne hband hband'
  have hd := crossBreak_band_depth j hj hband
  have hd' := crossBreak_band_depth j' hj' hband'
  obtain ⟨m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12⟩ := crossBreak_levels
  rcases hd with rfl | rfl | rfl | rfl | rfl <;>
    rcases hd' with rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact absurd rfl hne
    | (simp only [m8, m9, m10, m11, m12]
       apply crossBreak_chainRate <;> norm_num)

theorem crossBreak_ambiguityCount_le :
    (intervalFidelitySearch 15 crossBreakSource crossBreakTarget crossBreakFidelity 13).2.ambiguities
      ≤ Nat.floor (2 * ambiguityBandBound crossBreakSource crossBreakTarget 15 crossBreakFidelity
          / crossBreakRate * (2 : ℚ) ^ 13 / computedWaterHigh crossBreakSource crossBreakTarget) + 1 := by
  exact ambiguityCount_le 15 crossBreakSource crossBreakTarget crossBreakFidelity 13
    crossBreakSource_nonneg crossBreakTarget_nonneg crossBreakFidelity_pos.le
    crossBreakRate (by norm_num [crossBreakRate]) crossBreak_bandRate

theorem crossBreak_intervalSearch_budget_of_width (ε πi : ℚ)
    (hε : 0 < ε) (hπi : 0 < πi)
    (hb : gridStep 15 ≤ intervalWidthOpBitBudget
      (ε := ε) (p := crossBreakFidelity) (πi := πi) 3 13
      (2 * ambiguityBandBound crossBreakSource crossBreakTarget 15 crossBreakFidelity / crossBreakRate)
      (computedWaterHigh crossBreakSource crossBreakTarget)) :
    (intervalRunOperationCount 3 13
        (intervalFidelitySearch 15 crossBreakSource crossBreakTarget crossBreakFidelity 13).2.ambiguities : ℚ)
        * (gridStep 15 / 2) / πi ≤ ε * πi / crossBreakFidelity ∧
    (intervalRunOperationCount 3 13
        (intervalFidelitySearch 15 crossBreakSource crossBreakTarget crossBreakFidelity 13).2.ambiguities : ℚ)
        * (gridStep 15 / 2) ≤ πi ^ 2 / 2 := by
  exact intervalSearch_budget_of_width crossBreakSource crossBreakTarget crossBreakFidelity
    ε πi 15 13 hε crossBreakFidelity_pos hπi crossBreakSource_nonneg crossBreakTarget_nonneg
    crossBreakRate (by norm_num [crossBreakRate]) crossBreak_bandRate hb

def bandRateOn {m : ℕ} (D : Finset ℕ) (π σ : Fin m → ℚ) (b : ℕ) (p c : ℚ) (k : ℕ) : Prop :=
  ∀ j ∈ D, ∀ j' ∈ D, j < k → j' < k → j ≠ j' →
    |fidelityGap π σ p (bracketMidpoint π σ p j)| ≤ ambiguityBandBound π σ b p →
    |fidelityGap π σ p (bracketMidpoint π σ p j')| ≤ ambiguityBandBound π σ b p →
    c * |bracketMidpoint π σ p j - bracketMidpoint π σ p j'|
      ≤ |fidelityGap π σ p (bracketMidpoint π σ p j)
          - fidelityGap π σ p (bracketMidpoint π σ p j')|

structure BandShard {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ) (k : ℕ) where
  depths : Finset ℕ
  rate : ℚ
  rate_pos : 0 < rate
  rate_certificate : bandRateOn depths π σ b p rate k

theorem bandRateOn_of_bandRate {m : ℕ} (D : Finset ℕ) (π σ : Fin m → ℚ)
    (b : ℕ) (p c : ℚ) (k : ℕ) (h : bandRate π σ b p c k) :
    bandRateOn D π σ b p c k := by
  intro j _ j' _
  exact h j j'

theorem bandRateOn_mono {m : ℕ} (D : Finset ℕ) (π σ : Fin m → ℚ)
    (b : ℕ) (p c c' : ℚ) (k : ℕ) (hle : c' ≤ c) (h : bandRateOn D π σ b p c k) :
    bandRateOn D π σ b p c' k := by
  intro j hj j' hj' hjk hjk' hne hband hband'
  exact le_trans (mul_le_mul_of_nonneg_right hle (abs_nonneg _))
    (h j hj j' hj' hjk hjk' hne hband hband')

def shardAmbiguousDepths {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (D : Finset ℕ) : Finset ℕ :=
  (ambiguousDepths b π σ p k).filter (fun j => j ∈ D)

def shardAmbiguousLevels {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (D : Finset ℕ) : Finset ℚ :=
  (shardAmbiguousDepths b π σ p k D).image (bracketMidpoint π σ p)

def shardAmbiguityBound {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ) (k : ℕ)
    (s : BandShard π σ b p k) : ℕ :=
  Nat.floor (2 * ambiguityBandBound π σ b p / s.rate * (2 : ℚ) ^ k
    / computedWaterHigh π σ) + 1

def shardAmbiguityBudget {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ) (k : ℕ)
    (shards : List (BandShard π σ b p k)) (cuts : Finset ℕ) : ℕ :=
  cuts.card + (shards.map (shardAmbiguityBound π σ b p k)).sum

theorem shardAmbiguousLevels_card {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (D : Finset ℕ) :
    (shardAmbiguousLevels b π σ p k D).card = (shardAmbiguousDepths b π σ p k D).card := by
  unfold shardAmbiguousLevels
  refine Finset.card_image_of_injOn ?_
  intro i _ j _ hij
  by_contra hne
  exact absurd hij (bracketMidpoint_ne π σ p hπ hσ hne)

theorem shardLevel_mem_ambiguousLevels {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ)
    (p : ℚ) (k : ℕ) (D : Finset ℕ) {x : ℚ} (hx : x ∈ shardAmbiguousLevels b π σ p k D) :
    x ∈ ambiguousLevels b π σ p k := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨j, (Finset.mem_filter.mp hj).1, rfl⟩

theorem ambiguityBandBound_nonneg {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p : ℚ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p) :
    0 ≤ ambiguityBandBound π σ b p := by
  unfold ambiguityBandBound
  have hgrid : 0 ≤ gridStep b := by unfold gridStep; positivity
  have hsum : 0 ≤ ∑ j, π j * σ j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hπ j) (hσ j)
  have h1 : 0 ≤ 2 * (m : ℚ) * gridStep b := by positivity
  have h2 : 0 ≤ 2 * (∑ j, π j * σ j) + (m : ℚ) * gridStep b + p := by linarith
  exact mul_nonneg h1 h2

theorem shardAmbiguousLevels_diam {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p)
    (s : BandShard π σ b p k) {x y : ℚ}
    (hx : x ∈ shardAmbiguousLevels b π σ p k s.depths)
    (hy : y ∈ shardAmbiguousLevels b π σ p k s.depths) :
    |x - y| ≤ 2 * ambiguityBandBound π σ b p / s.rate := by
  have hB := ambiguityBandBound_nonneg π σ b p hπ hσ hp
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, abs_zero]
    exact div_nonneg (mul_nonneg (by norm_num) hB) s.rate_pos.le
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hy
  have hjD : j ∈ s.depths := (Finset.mem_filter.mp hj).2
  have hjD' : j' ∈ s.depths := (Finset.mem_filter.mp hj').2
  have hjA : j ∈ ambiguousDepths b π σ p k := (Finset.mem_filter.mp hj).1
  have hjA' : j' ∈ ambiguousDepths b π σ p k := (Finset.mem_filter.mp hj').1
  have hjk : j < k := Finset.mem_range.mp (Finset.mem_filter.mp hjA).1
  have hjk' : j' < k := Finset.mem_range.mp (Finset.mem_filter.mp hjA').1
  have hne : j ≠ j' := by
    intro h
    subst j'
    exact hxy rfl
  have hγ : 0 ≤ bracketMidpoint π σ p j := by
    have hb := fidelityBracket_bounds π σ p j hπ hσ
    dsimp only [bracketMidpoint]
    linarith
  have hγ' : 0 ≤ bracketMidpoint π σ p j' := by
    have hb := fidelityBracket_bounds π σ p j' hπ hσ
    dsimp only [bracketMidpoint]
    linarith
  have hband := intervalAmbiguity_gap_le π σ b p hπ hσ hγ hp (Finset.mem_filter.mp hjA).2
  have hband' := intervalAmbiguity_gap_le π σ b p hπ hσ hγ' hp (Finset.mem_filter.mp hjA').2
  have hrate := s.rate_certificate j hjD j' hjD' hjk hjk' hne hband hband'
  have hdiff : |fidelityGap π σ p (bracketMidpoint π σ p j)
      - fidelityGap π σ p (bracketMidpoint π σ p j')| ≤ 2 * ambiguityBandBound π σ b p := by
    have hsum : |fidelityGap π σ p (bracketMidpoint π σ p j)
        - fidelityGap π σ p (bracketMidpoint π σ p j')|
        ≤ |fidelityGap π σ p (bracketMidpoint π σ p j)|
          + |fidelityGap π σ p (bracketMidpoint π σ p j')| := by
      have hkey : fidelityGap π σ p (bracketMidpoint π σ p j)
          - fidelityGap π σ p (bracketMidpoint π σ p j')
          = fidelityGap π σ p (bracketMidpoint π σ p j)
            + -(fidelityGap π σ p (bracketMidpoint π σ p j')) := by ring
      rw [hkey]
      simpa only [abs_neg] using!
        abs_add_le (fidelityGap π σ p (bracketMidpoint π σ p j))
          (-(fidelityGap π σ p (bracketMidpoint π σ p j')))
    linarith
  rw [le_div_iff₀ s.rate_pos]
  nlinarith

theorem shardAmbiguityCount_le {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p)
    (s : BandShard π σ b p k) :
    (shardAmbiguousDepths b π σ p k s.depths).card ≤ shardAmbiguityBound π σ b p k s := by
  rw [← shardAmbiguousLevels_card b π σ p k hπ hσ s.depths]
  have hH : 0 < computedWaterHigh π σ :=
    lt_of_lt_of_le zero_lt_one (computedWaterHigh_pos π σ hπ hσ)
  have hsp : 0 < computedWaterHigh π σ / (2 : ℚ) ^ k := div_pos hH (by positivity)
  have hsep : ∀ x ∈ shardAmbiguousLevels b π σ p k s.depths,
      ∀ y ∈ shardAmbiguousLevels b π σ p k s.depths,
      x ≠ y → computedWaterHigh π σ / (2 : ℚ) ^ k ≤ |x - y| := by
    intro x hx y hy hxy
    exact ambiguousLevels_separation b π σ p k hπ hσ
      (shardLevel_mem_ambiguousLevels b π σ p k s.depths hx)
      (shardLevel_mem_ambiguousLevels b π σ p k s.depths hy) hxy
  have hdiam : ∀ x ∈ shardAmbiguousLevels b π σ p k s.depths,
      ∀ y ∈ shardAmbiguousLevels b π σ p k s.depths,
      |x - y| ≤ 2 * ambiguityBandBound π σ b p / s.rate := by
    intro x hx y hy
    exact shardAmbiguousLevels_diam b π σ p k hπ hσ hp s hx hy
  have hbound := Finset.card_le_of_separated_diam (shardAmbiguousLevels b π σ p k s.depths)
    (computedWaterHigh π σ / (2 : ℚ) ^ k) (2 * ambiguityBandBound π σ b p / s.rate)
    hsp hsep hdiam
  have hconv : (2 * ambiguityBandBound π σ b p / s.rate)
      / (computedWaterHigh π σ / (2 : ℚ) ^ k)
      = 2 * ambiguityBandBound π σ b p / s.rate * (2 : ℚ) ^ k / computedWaterHigh π σ := by
    have hb : computedWaterHigh π σ / (2 : ℚ) ^ k ≠ 0 := by positivity
    rw [div_eq_div_iff hb (ne_of_gt hH)]
    field_simp
  rw [hconv] at hbound
  exact hbound

theorem mem_foldr_union {j : ℕ} {D : Finset ℕ} (hj : j ∈ D) :
    ∀ (l : List (Finset ℕ)), D ∈ l → j ∈ l.foldr (· ∪ ·) ∅ := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons a rest ih =>
      intro h
      rcases List.mem_cons.mp h with rfl | h
      · simp [hj]
      · exact Finset.mem_union.mpr (Or.inr (ih h))

theorem card_foldr_union_le :
    ∀ (l : List (Finset ℕ)), (l.foldr (· ∪ ·) ∅).card ≤ (l.map Finset.card).sum := by
  intro l
  induction l with
  | nil => simp
  | cons a rest ih =>
      simp only [List.foldr_cons, List.map_cons, List.sum_cons]
      exact le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left ih _)

theorem list_sum_le {α : Type} (l : List α) (f g : α → ℕ)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

def coveredDepths {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (A cuts : Finset ℕ) (shards : List (BandShard π σ b p k)) : Finset ℕ :=
  cuts ∪ (shards.map (fun s => A.filter (fun j => j ∈ s.depths))).foldr (· ∪ ·) ∅

theorem mem_coveredDepths {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (A cuts : Finset ℕ) (shards : List (BandShard π σ b p k)) {j : ℕ} (hj : j ∈ A)
    (hcover : j ∈ cuts ∨ ∃ s ∈ shards, j ∈ s.depths) : j ∈ coveredDepths b π σ p k A cuts shards := by
  apply Finset.mem_union.mpr
  rcases hcover with hcut | ⟨s, hs, hjs⟩
  · exact Or.inl hcut
  · apply Or.inr
    have hmem : j ∈ A.filter (fun j => j ∈ s.depths) := Finset.mem_filter.mpr ⟨hj, hjs⟩
    exact mem_foldr_union hmem _ (List.mem_map.mpr ⟨s, hs, rfl⟩)

theorem coveredDepths_card_le {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (A cuts : Finset ℕ) (shards : List (BandShard π σ b p k)) :
    (coveredDepths b π σ p k A cuts shards).card ≤
      cuts.card + (shards.map (fun s => (A.filter (fun j => j ∈ s.depths)).card)).sum := by
  unfold coveredDepths
  refine le_trans (Finset.card_union_le _ _) (Nat.add_le_add_left ?_ _)
  simpa only [List.map_map, Function.comp_def] using!
    (card_foldr_union_le (shards.map (fun s => A.filter (fun j => j ∈ s.depths))))

theorem ambiguityCount_le_of_shards {m : ℕ} (b : ℕ) (π σ : Fin m → ℚ) (p : ℚ) (k : ℕ)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j) (hp : 0 ≤ p)
    (shards : List (BandShard π σ b p k)) (cuts : Finset ℕ)
    (hcover : ∀ j ∈ ambiguousDepths b π σ p k, j ∈ cuts ∨ ∃ s ∈ shards, j ∈ s.depths) :
    (intervalFidelitySearch b π σ p k).2.ambiguities ≤ shardAmbiguityBudget π σ b p k shards cuts := by
  rw [intervalFidelitySearch_ambiguities_depths b π σ p k hπ hσ hp]
  let A := ambiguousDepths b π σ p k
  calc
    A.card ≤ (coveredDepths b π σ p k A cuts shards).card :=
      Finset.card_le_card (fun j hj => mem_coveredDepths b π σ p k A cuts shards hj (hcover j hj))
    _ ≤ cuts.card + (shards.map (fun s => (shardAmbiguousDepths b π σ p k s.depths).card)).sum :=
      coveredDepths_card_le b π σ p k A cuts shards
    _ ≤ cuts.card + (shards.map (shardAmbiguityBound π σ b p k)).sum := by
      apply Nat.add_le_add_left
      exact list_sum_le shards _ _ (fun s _ => shardAmbiguityCount_le b π σ p k hπ hσ hp s)
    _ = shardAmbiguityBudget π σ b p k shards cuts := rfl

def intervalShardOpBitBudget {m : ℕ} (π σ : Fin m → ℚ) (b : ℕ) (p ε πi : ℚ) (k : ℕ)
    (shards : List (BandShard π σ b p k)) (cuts : Finset ℕ) : ℚ :=
  intervalSearchOpBitBudget ε p πi m k (shardAmbiguityBudget π σ b p k shards cuts)

theorem intervalSearch_budget_of_shards {m : ℕ} (π σ : Fin m → ℚ) (p ε πi : ℚ) (b k : ℕ)
    (hε : 0 < ε) (hp : 0 < p) (hπi : 0 < πi)
    (hπ : ∀ j, 0 ≤ π j) (hσ : ∀ j, 0 ≤ σ j)
    (shards : List (BandShard π σ b p k)) (cuts : Finset ℕ)
    (hcover : ∀ j ∈ ambiguousDepths b π σ p k, j ∈ cuts ∨ ∃ s ∈ shards, j ∈ s.depths)
    (hb : gridStep b ≤ intervalShardOpBitBudget π σ b p ε πi k shards cuts) :
    (intervalRunOperationCount m k (intervalFidelitySearch b π σ p k).2.ambiguities : ℚ)
        * (gridStep b / 2) / πi ≤ ε * πi / p ∧
    (intervalRunOperationCount m k (intervalFidelitySearch b π σ p k).2.ambiguities : ℚ)
        * (gridStep b / 2) ≤ πi ^ 2 / 2 := by
  have hcount := ambiguityCount_le_of_shards b π σ p k hπ hσ hp.le shards cuts hcover
  have hop := intervalRunOperationCount_mono m k hcount
  have hn : 0 < intervalRunOperationCount m k (intervalFidelitySearch b π σ p k).2.ambiguities :=
    intervalRunOperationCount_pos m k _
  have hbud : opBitBudget ε p πi
        (intervalRunOperationCount m k (shardAmbiguityBudget π σ b p k shards cuts))
      ≤ opBitBudget ε p πi
        (intervalRunOperationCount m k (intervalFidelitySearch b π σ p k).2.ambiguities) :=
    opBitBudget_mono hn hε hp hπi hop
  have hb' : gridStep b ≤ intervalSearchOpBitBudget ε p πi m k
      (intervalFidelitySearch b π σ p k).2.ambiguities := by
    calc gridStep b ≤ intervalShardOpBitBudget π σ b p ε πi k shards cuts := hb
      _ = intervalSearchOpBitBudget ε p πi m k (shardAmbiguityBudget π σ b p k shards cuts) := rfl
      _ ≤ intervalSearchOpBitBudget ε p πi m k
          (intervalFidelitySearch b π σ p k).2.ambiguities := by
        unfold intervalSearchOpBitBudget
        exact hbud
  exact intervalSearchOpBitBudget_sufficient hε hp hπi b hb'

theorem crossBreak_satDot_zero :
    satDot crossBreakSource crossBreakTarget (∅ : Finset (Fin 3)) = 0 := by
  simp [satDot]

theorem crossBreak_freeSq_zero :
    freeSq crossBreakSource crossBreakTarget (∅ : Finset (Fin 3)) = 3 := by
  unfold freeSq
  rw [crossBreak_fin3_sum]
  norm_num [crossBreakSource, crossBreakTarget]

theorem crossBreak_slope_zero (γ₁ γ₂ : ℚ) :
    pieceSegmentSlope crossBreakSource crossBreakTarget crossBreakFidelity
      (∅ : Finset (Fin 3)) γ₁ γ₂ = (2 / 3) * (γ₁ + γ₂) := by
  rw [pieceSegmentSlope, crossBreak_satDot_zero, crossBreak_freeSq_zero]
  norm_num [crossBreakFidelity]

theorem crossBreak_pieceBreak_zero :
    pieceBreak crossBreakSource crossBreakTarget (1 / 4) (∅ : Finset (Fin 3))
      ({0} : Finset (Fin 3)) := by
  intro j hj
  have hj0 : j = 0 := Finset.mem_singleton.mp (Finset.mem_sdiff.mp hj).1
  subst j
  exact ⟨by norm_num [crossBreakSource], by norm_num [crossBreakSource, crossBreakTarget]⟩

theorem crossBreak_breakpointCutsRate :
    breakpointCutsRate crossBreakSource crossBreakTarget crossBreakFidelity
      (∅ : Finset (Fin 3)) ({0} : Finset (Fin 3)) (1 / 8) (1 / 4) (15 / 32) := by
  simp only [breakpointCutsRate]
  rw [crossBreak_slope_zero, crossBreak_slope_low]
  norm_num

theorem crossBreak_no_common_rate :
    ¬ (∃ c : ℚ, 0 < c ∧
      (c ≤ crossPieceRateLower crossBreakSource crossBreakTarget crossBreakFidelity
          (∅ : Finset (Fin 3)) ({0} : Finset (Fin 3)) (1 / 8) (1 / 4) (15 / 32) ∨
       c ≤ crossPieceRateLowerDown crossBreakSource crossBreakTarget crossBreakFidelity
          (∅ : Finset (Fin 3)) ({0} : Finset (Fin 3)) (1 / 8) (1 / 4) (15 / 32))) := by
  exact breakpointCutsRate_no_common_rate crossBreakSource crossBreakTarget crossBreakFidelity
    (∅ : Finset (Fin 3)) ({0} : Finset (Fin 3)) (1 / 8) (1 / 4) (15 / 32)
    crossBreak_breakpointCutsRate

def crossBreakLowShard : BandShard crossBreakSource crossBreakTarget 15 crossBreakFidelity 13 where
  depths := {10, 11}
  rate := crossBreakRate
  rate_pos := by norm_num [crossBreakRate]
  rate_certificate :=
    bandRateOn_of_bandRate {10, 11} crossBreakSource crossBreakTarget 15 crossBreakFidelity
      crossBreakRate 13 crossBreak_bandRate

def crossBreakHighShard : BandShard crossBreakSource crossBreakTarget 15 crossBreakFidelity 13 where
  depths := {8, 9, 12}
  rate := 1 / 5
  rate_pos := by norm_num
  rate_certificate := by
    apply bandRateOn_mono {8, 9, 12} crossBreakSource crossBreakTarget 15 crossBreakFidelity
      crossBreakRate (1 / 5) 13 (by norm_num [crossBreakRate])
    exact bandRateOn_of_bandRate {8, 9, 12} crossBreakSource crossBreakTarget 15
      crossBreakFidelity crossBreakRate 13 crossBreak_bandRate

def crossBreakShards : List (BandShard crossBreakSource crossBreakTarget 15 crossBreakFidelity 13) :=
  [crossBreakLowShard, crossBreakHighShard]

def crossBreakCuts : Finset ℕ := {3}

theorem crossBreak_cut_depth_three :
    3 ∈ crossBreakCuts ∧
    bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity 3 = 15 / 32 ∧
    breakpointCutsRate crossBreakSource crossBreakTarget crossBreakFidelity
      (∅ : Finset (Fin 3)) ({0} : Finset (Fin 3)) (1 / 8) (1 / 4) (15 / 32) := by
  exact ⟨by simp [crossBreakCuts], crossBreak_levels.2.2.2.1, crossBreak_breakpointCutsRate⟩

theorem crossBreak_shard_cover :
    ∀ j ∈ ambiguousDepths 15 crossBreakSource crossBreakTarget crossBreakFidelity 13,
      j ∈ crossBreakCuts ∨ ∃ s ∈ crossBreakShards, j ∈ s.depths := by
  intro j hj
  have hjk : j < 13 := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have hγ : 0 ≤ bracketMidpoint crossBreakSource crossBreakTarget crossBreakFidelity j := by
    have hb := fidelityBracket_bounds crossBreakSource crossBreakTarget crossBreakFidelity j
      crossBreakSource_nonneg crossBreakTarget_nonneg
    dsimp only [bracketMidpoint]
    linarith
  have hband := intervalAmbiguity_gap_le crossBreakSource crossBreakTarget 15 crossBreakFidelity
    crossBreakSource_nonneg crossBreakTarget_nonneg hγ crossBreakFidelity_pos.le
    (Finset.mem_filter.mp hj).2
  rcases crossBreak_band_depth j hjk hband with rfl | rfl | rfl | rfl | rfl <;>
    simp [crossBreakCuts, crossBreakShards, crossBreakLowShard, crossBreakHighShard]

theorem crossBreak_shardedAmbiguityCount_le :
    (intervalFidelitySearch 15 crossBreakSource crossBreakTarget crossBreakFidelity 13).2.ambiguities
      ≤ shardAmbiguityBudget crossBreakSource crossBreakTarget 15 crossBreakFidelity 13
        crossBreakShards crossBreakCuts := by
  exact ambiguityCount_le_of_shards 15 crossBreakSource crossBreakTarget crossBreakFidelity 13
    crossBreakSource_nonneg crossBreakTarget_nonneg crossBreakFidelity_pos.le
    crossBreakShards crossBreakCuts crossBreak_shard_cover

theorem crossBreak_intervalSearch_budget_of_shards (ε πi : ℚ)
    (hε : 0 < ε) (hπi : 0 < πi)
    (hb : gridStep 15 ≤ intervalShardOpBitBudget crossBreakSource crossBreakTarget 15
      crossBreakFidelity ε πi 13 crossBreakShards crossBreakCuts) :
    (intervalRunOperationCount 3 13
        (intervalFidelitySearch 15 crossBreakSource crossBreakTarget crossBreakFidelity 13).2.ambiguities : ℚ)
        * (gridStep 15 / 2) / πi ≤ ε * πi / crossBreakFidelity ∧
    (intervalRunOperationCount 3 13
        (intervalFidelitySearch 15 crossBreakSource crossBreakTarget crossBreakFidelity 13).2.ambiguities : ℚ)
        * (gridStep 15 / 2) ≤ πi ^ 2 / 2 := by
  exact intervalSearch_budget_of_shards crossBreakSource crossBreakTarget crossBreakFidelity
    ε πi 15 13 hε crossBreakFidelity_pos hπi crossBreakSource_nonneg crossBreakTarget_nonneg
    crossBreakShards crossBreakCuts crossBreak_shard_cover hb

theorem frontier1 :
    bandRate crossBreakSource crossBreakTarget 15 crossBreakFidelity crossBreakRate 13 ∧
    (intervalFidelitySearch 15 crossBreakSource crossBreakTarget crossBreakFidelity 13).2.ambiguities
      ≤ Nat.floor (2 * ambiguityBandBound crossBreakSource crossBreakTarget 15 crossBreakFidelity
          / crossBreakRate * (2 : ℚ) ^ 13 / computedWaterHigh crossBreakSource crossBreakTarget) + 1 ∧
    (∀ ε πi : ℚ, 0 < ε → 0 < πi →
      (gridStep 15 ≤ intervalWidthOpBitBudget
        (ε := ε) (p := crossBreakFidelity) (πi := πi) 3 13
        (2 * ambiguityBandBound crossBreakSource crossBreakTarget 15 crossBreakFidelity / crossBreakRate)
        (computedWaterHigh crossBreakSource crossBreakTarget)) →
      (intervalRunOperationCount 3 13
          (intervalFidelitySearch 15 crossBreakSource crossBreakTarget crossBreakFidelity 13).2.ambiguities : ℚ)
          * (gridStep 15 / 2) / πi ≤ ε * πi / crossBreakFidelity ∧
      (intervalRunOperationCount 3 13
          (intervalFidelitySearch 15 crossBreakSource crossBreakTarget crossBreakFidelity 13).2.ambiguities : ℚ)
          * (gridStep 15 / 2) ≤ πi ^ 2 / 2) ∧
    breakpointCutsRate crossBreakSource crossBreakTarget crossBreakFidelity
      (∅ : Finset (Fin 3)) ({0} : Finset (Fin 3)) (1 / 8) (1 / 4) (15 / 32) ∧
    (intervalFidelitySearch 15 crossBreakSource crossBreakTarget crossBreakFidelity 13).2.ambiguities
      ≤ shardAmbiguityBudget crossBreakSource crossBreakTarget 15 crossBreakFidelity 13
        crossBreakShards crossBreakCuts ∧
    (∀ ε πi : ℚ, 0 < ε → 0 < πi →
      (gridStep 15 ≤ intervalShardOpBitBudget crossBreakSource crossBreakTarget 15
        crossBreakFidelity ε πi 13 crossBreakShards crossBreakCuts) →
      (intervalRunOperationCount 3 13
          (intervalFidelitySearch 15 crossBreakSource crossBreakTarget crossBreakFidelity 13).2.ambiguities : ℚ)
          * (gridStep 15 / 2) / πi ≤ ε * πi / crossBreakFidelity ∧
      (intervalRunOperationCount 3 13
          (intervalFidelitySearch 15 crossBreakSource crossBreakTarget crossBreakFidelity 13).2.ambiguities : ℚ)
          * (gridStep 15 / 2) ≤ πi ^ 2 / 2) := by
  exact ⟨crossBreak_bandRate, crossBreak_ambiguityCount_le,
    crossBreak_intervalSearch_budget_of_width, crossBreak_breakpointCutsRate,
    crossBreak_shardedAmbiguityCount_le, crossBreak_intervalSearch_budget_of_shards⟩

end Qatlib.Concepts.Waterfill.LevelFidelity.FidelityBandCertificateProgram
