/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HadamardAnn19.NativeReduction.Actual
set_option warningAsError false

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Papers.HadamardAnn19.ReportedModels
open Qatlib.Foundations.BooleanEnergy.HadamardGram
open Qatlib.Foundations.BooleanEnergy.PenaltyExact
open Qatlib.Papers.HadamardAnn19.NativeReduction.Actual
open Qatlib.Papers.HadamardAnn19.MainResults.EnergyChain

def abstractCount (M : ℕ) : ℚ := ((M:ℚ)^3+(M:ℚ)^2-(M:ℚ))/2

theorem abstract_count_mismatch : abstractCount 4 = 38 ∧ Fintype.card (Variable 4 4) = 40 := by
  constructor
  · norm_num [abstractCount]
  · exact card_variable 4 4

theorem rectangular_count : Fintype.card (Variable 4 3) = 24 ∧
    Fintype.card (Variable 12 3) = 72 := ⟨card_variable 4 3,card_variable 12 3⟩

theorem printed_spin_map_failure : (1-(1:ℝ))/2 = 0 ∧
    ¬((1-(1:ℝ))/2 = -1 ∨ (1-(1:ℝ))/2 = 1) := by norm_num

theorem corrected_transform (q : ℝ) : (1-(1-2*q))/2 = q := by ring

theorem printed_spin_ancilla_failure : spin (true && true) ≠ spin true*spin true := by
  norm_num [spin,bit]

def reported22 (s0 s1 s2 s3 s4 s5 : ℝ) : ℝ :=
  e2S s0 s1 s2 s3 s4 s5 - 2*s0*s2

theorem printed22_mismatch : reported22 1 1 1 1 1 1 ≠ e2S 1 1 1 1 1 1 := by
  norm_num [reported22,e2S]

def badFive : Configuration 2 2 := fromSix (fun i => decide (i.val=0 ∨ i.val=2 ∨ i.val=5))

theorem badFive_energy : paperEnergy 5 badFive = -8 := by
  unfold paperEnergy
  rw [pairs_two_univ,Finset.sum_singleton]
  unfold paperPair
  rw [pairs_two_univ,Finset.sum_singleton]
  norm_num [badFive,pairPenalty,Fin.sum_univ_two,pair01,left,right,main,ancilla,
    fromSix,rowLinear,andPenalty,bit]

theorem valid_paper_nonneg {M N : ℕ} (δ : ℝ) (x : Configuration M N) (h : Valid x) :
    0 ≤ paperEnergy δ x := by
  rw [paperEnergy_eq_squareEnergy,squareEnergy_valid _ x h]
  exact energy_nonneg _

theorem bare_threshold_counterexample : (4:ℝ)<5 ∧
    ∃ x : Configuration 2 2, IsGround (paperEnergy 5) x ∧ ¬Valid x := by
  refine ⟨by norm_num,?_⟩
  obtain ⟨x,hx⟩ := exists_ground (paperEnergy (M:=2) (N:=2) 5)
  refine ⟨x,hx,?_⟩
  intro hv
  have hn := valid_paper_nonneg 5 x hv
  have hb := hx badFive
  rw [badFive_energy] at hb
  linarith

end Qatlib.Papers.HadamardAnn19.ReportedModels
