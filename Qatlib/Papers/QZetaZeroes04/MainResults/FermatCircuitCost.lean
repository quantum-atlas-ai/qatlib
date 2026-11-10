/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QZetaZeroes04.MainResults.ZetaHypersurfaceDefs
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QZetaZeroes04.MainResults.FermatCircuitCost

inductive Step where

  | chiPrep

  | mulDiv

  | fourier

  | charPhase

  | phaseFlip
  deriving DecidableEq, Repr

def blockWord : List Step := [Step.mulDiv, Step.fourier, Step.mulDiv]

def algorithm1Word (n : ℕ) : List Step :=
  [Step.chiPrep] ++
    (List.range (n + 1)).flatMap (fun _ => blockWord) ++
    (List.range (n + 1)).map (fun _ => Step.charPhase) ++
    [Step.phaseFlip]

theorem algorithm1Word_length (n : ℕ) :
    (algorithm1Word n).length = 4 * n + 6 := by
  have hblock : ∀ l : List ℕ, (l.flatMap (fun _ => blockWord)).length = 3 * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons h t ih => simp [blockWord, Nat.mul_succ]; omega
  unfold algorithm1Word
  simp only [List.length_append, List.length_singleton, List.length_map,
    List.length_range]
  rw [hblock]
  simp only [List.length_range]
  omega

def stepCost (logq : ℕ) : Step → ℕ
  | Step.chiPrep => logq + 1
  | Step.mulDiv => logq + 1
  | Step.fourier => (logq + 1) ^ 2
  | Step.charPhase => 1
  | Step.phaseFlip => 1

def algorithm1Cost (n logq : ℕ) : ℕ :=
  ((algorithm1Word n).map (stepCost logq)).sum

theorem stepCost_le (logq : ℕ) (s : Step) : stepCost logq s ≤ (logq + 1) ^ 2 := by
  cases s <;> simp only [stepCost] <;> nlinarith [Nat.one_le_pow' 2 logq,
    Nat.zero_le logq]

theorem sum_cost_le_length_mul (l : List Step) (logq : ℕ) :
    ((l.map (stepCost logq)).sum) ≤ l.length * (logq + 1) ^ 2 := by
  induction l with
  | nil => simp
  | cons h t ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hh := stepCost_le logq h
      nlinarith

theorem algorithm1Cost_le (n logq : ℕ) :
    algorithm1Cost n logq ≤ (4 * n + 6) * (logq + 1) ^ 2 := by
  unfold algorithm1Cost
  have h := sum_cost_le_length_mul (algorithm1Word n) logq
  rw [algorithm1Word_length] at h
  exact h

theorem algorithm1Cost_poly (n logq logm : ℕ) (hn : 1 ≤ n)
    (hlogq : 1 ≤ logq) (hlogm : 1 ≤ logm) :
    algorithm1Cost n logq ≤
      16 * ((logq + 1) * (n * (logm + 1))) ^ 3 := by
  set B : ℕ := (logq + 1) * (n * (logm + 1)) with hBdef
  have hlogq1 : 1 ≤ logq + 1 := by omega
  have hlogm1 : 2 ≤ logm + 1 := by omega
  have hB1 : logq + 1 ≤ B := by
    rw [hBdef]
    have : 1 ≤ n * (logm + 1) := by
      have : 2 ≤ logm + 1 := hlogm1
      nlinarith
    calc logq + 1 = (logq + 1) * 1 := by ring
      _ ≤ (logq + 1) * (n * (logm + 1)) := Nat.mul_le_mul_left _ this
  have hB2 : 2 * n ≤ B := by
    rw [hBdef]
    have h2 : 2 ≤ logq + 1 := by omega
    have h3 : 2 * n ≤ n * (logm + 1) := by nlinarith
    calc 2 * n ≤ 2 * (n * (logm + 1)) := by nlinarith
      _ ≤ (logq + 1) * (n * (logm + 1)) := Nat.mul_le_mul_right _ h2

  have hB3 : (logq + 1) ^ 2 * (2 * n) ≤ B ^ 3 := by
    have hp1 : (logq + 1) ^ 2 ≤ B ^ 2 := by
      apply Nat.pow_le_pow_left hB1
    calc (logq + 1) ^ 2 * (2 * n) ≤ B ^ 2 * B := Nat.mul_le_mul hp1 hB2
      _ = B ^ 3 := by ring
  have hc := algorithm1Cost_le n logq

  have h4n : 4 * n + 6 ≤ 16 * (2 * n) := by nlinarith
  have hfin : (4 * n + 6) * (logq + 1) ^ 2 ≤ 16 * ((logq + 1) ^ 2 * (2 * n)) := by
    nlinarith [Nat.mul_le_mul_right ((logq + 1) ^ 2) h4n]
  calc algorithm1Cost n logq ≤ (4 * n + 6) * (logq + 1) ^ 2 := hc
    _ ≤ 16 * ((logq + 1) ^ 2 * (2 * n)) := hfin
    _ ≤ 16 * B ^ 3 := Nat.mul_le_mul_left 16 hB3

end Qatlib.Papers.QZetaZeroes04.MainResults.FermatCircuitCost
