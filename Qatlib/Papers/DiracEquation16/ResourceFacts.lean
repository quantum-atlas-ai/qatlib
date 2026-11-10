/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBoundsRefinedDefs
import Mathlib.Tactic
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DiracEquation16.ResourceFacts

open Qatlib.Concepts.ResourceBounds.AsymBounds (uniformUpperBound)
set_option warningAsError false

def circuitWidth (nx : ℕ) : ℕ := 4 * nx + 2

theorem circuitWidth_ten : circuitWidth 10 = 42 := by
  unfold circuitWidth; norm_num

theorem circuitWidth_hundred : circuitWidth 100 = 402 := by
  unfold circuitWidth; norm_num

def latticePointsPerAxis (nx : ℕ) : ℕ := 2 ^ nx

def totalLatticePoints (nx : ℕ) : ℕ := (2 ^ nx) ^ 3

theorem latticePointsPerAxis_ten : latticePointsPerAxis 10 = 1024 := by
  unfold latticePointsPerAxis; norm_num

theorem totalLatticePoints_ten : totalLatticePoints 10 = 1073741824 := by
  unfold totalLatticePoints
  norm_num

theorem perAxis_scale_at_100 :
    10 ^ 30 < latticePointsPerAxis 100 ∧ latticePointsPerAxis 100 < 2 * 10 ^ 30 := by
  unfold latticePointsPerAxis
  exact ⟨by norm_num, by norm_num⟩

theorem total_scale_at_100 :
    10 ^ 90 < totalLatticePoints 100 ∧ totalLatticePoints 100 < 10 ^ 91 := by
  unfold totalLatticePoints
  have hlo : (10 : ℕ) ^ 30 < 2 ^ 100 := by norm_num
  have hhi : (2 : ℕ) ^ 100 < 2 * 10 ^ 30 := by norm_num
  constructor
  · have h30 : ((10 : ℕ) ^ 30) ^ 3 = 10 ^ 90 := by rw [← pow_mul]
    calc (10 : ℕ) ^ 90 = ((10 ^ 30) ^ 3) := h30.symm
      _ < (2 ^ 100) ^ 3 := Nat.pow_lt_pow_left hlo (by norm_num)
  · have h30 : ((10 : ℕ) ^ 30) ^ 3 = 10 ^ 90 := by rw [← pow_mul]
    have hcube : ((2 : ℕ) ^ 100) ^ 3 < (2 * 10 ^ 30) ^ 3 :=
      Nat.pow_lt_pow_left hhi (by norm_num)
    calc ((2 : ℕ) ^ 100) ^ 3 < (2 * 10 ^ 30) ^ 3 := hcube
      _ = 8 * 10 ^ 90 := by rw [mul_pow, h30]; norm_num
      _ < 10 * 10 ^ 90 := Nat.mul_lt_mul_of_pos_right (by norm_num) (by positivity)
      _ = 10 ^ 91 := by rw [mul_comm, ← pow_succ]

def massGateCount : ℕ := 245

def vectorPotentialGateCount : ℕ := 3330

def oneStepGateCountAtTen : ℕ := 12773

theorem localGates_lt_stepGates :
    massGateCount + vectorPotentialGateCount < oneStepGateCountAtTen := by
  unfold massGateCount vectorPotentialGateCount oneStepGateCountAtTen
  norm_num

theorem classical_exceeds_quantum_at_ten :
    10 ^ 4 * oneStepGateCountAtTen < totalLatticePoints 10 := by
  unfold oneStepGateCountAtTen totalLatticePoints
  norm_num

theorem classical_ops_at_ten :
    10 ^ 9 < totalLatticePoints 10 ∧ totalLatticePoints 10 < 2 * 10 ^ 9 := by
  unfold totalLatticePoints
  norm_num

def oneDimensionalWidth (nz : ℕ) : ℕ := 2 * nz - 1

def oneDimensionalPoints (nz : ℕ) : ℕ := 2 ^ nz

theorem tableI_row_two :
    oneDimensionalWidth 2 = 3 ∧ oneDimensionalPoints 2 = 4 := by
  unfold oneDimensionalWidth oneDimensionalPoints; norm_num

theorem tableI_row_seven :
    oneDimensionalWidth 7 = 13 ∧ oneDimensionalPoints 7 = 128 := by
  unfold oneDimensionalWidth oneDimensionalPoints; norm_num

def oneDimensionalDepth (nz : ℕ) : ℕ :=
  match nz with
  | 2 => 60
  | 3 => 182
  | 4 => 376
  | 5 => 642
  | 6 => 980
  | 7 => 1390
  | _ => 0

theorem oneDimensionalDepth_monotone_tabulated :
    oneDimensionalDepth 2 < oneDimensionalDepth 3 ∧
    oneDimensionalDepth 3 < oneDimensionalDepth 4 ∧
    oneDimensionalDepth 4 < oneDimensionalDepth 5 ∧
    oneDimensionalDepth 5 < oneDimensionalDepth 6 ∧
    oneDimensionalDepth 6 < oneDimensionalDepth 7 := by
  unfold oneDimensionalDepth; norm_num

def hadamardGates : ℕ := 72
def cliffordGates : ℕ := 92
def tGates : ℕ := 94
def cnotGates : ℕ := 50

theorem massive_one_dimensional_depth :
    hadamardGates + cliffordGates + tGates + cnotGates = 308 := by
  unfold hadamardGates cliffordGates tGates cnotGates
  norm_num

def stepGateCountModel (K n : ℕ) : ℕ := 3 * n * n + K

theorem stepGateCountModel_le (K n : ℕ) :
    stepGateCountModel K n ≤ (K + 3) * (n + 1) ^ 2 := by
  unfold stepGateCountModel
  have hA : 3 * n * n ≤ (K + 3) * (n * n) := by
    have h := Nat.mul_le_mul_right (n * n) (by omega : 3 ≤ K + 3)
    simpa [mul_assoc, mul_comm, mul_left_comm] using! h
  have hB : K ≤ K + 3 := by omega
  have h1 : 3 * n * n + K ≤ (K + 3) * (n * n) + (K + 3) :=
    Nat.add_le_add hA hB
  have he : (K + 3) * (n * n) + (K + 3) = (K + 3) * (n * n + 1) := by ring
  have h2 : n * n + 1 ≤ (n + 1) ^ 2 := by
    have e : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
    rw [e]; omega
  calc 3 * n * n + K ≤ (K + 3) * (n * n) + (K + 3) := h1
    _ = (K + 3) * (n * n + 1) := he
    _ ≤ (K + 3) * (n + 1) ^ 2 := Nat.mul_le_mul_left (K + 3) h2

theorem stepGateCountModel_ge (K n : ℕ) :
    3 * n * n ≤ stepGateCountModel K n := by
  unfold stepGateCountModel
  omega

theorem stepGateCountModel_uniformUpperBound (K : ℕ) :
    uniformUpperBound (fun n => stepGateCountModel K n) (K + 3) 2 := by
  intro n
  simpa [pow_two] using! stepGateCountModel_le K n

end Qatlib.Papers.DiracEquation16.ResourceFacts
