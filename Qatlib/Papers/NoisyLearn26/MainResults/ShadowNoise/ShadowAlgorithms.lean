/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoisyLearn26.MainResults.Models.InterfaceModels
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyLearn26.MainResults.ShadowNoise

open Qatlib.Papers.NoisyLearn26.MainResults

open scoped BigOperators

def pauliBits (a : PauliChar) : Bool × Bool :=
  if a = 0 then (false, false)
  else if a = 1 then (true, false)
  else if a = 2 then (true, true)
  else (false, true)

def symplecticBit (a b : PauliChar) : Bool :=
  Bool.xor ((pauliBits a).1 && (pauliBits b).2) ((pauliBits a).2 && (pauliBits b).1)

def symplecticParity {n : ℕ} (s P : Pauli n) : ℕ :=
  (Finset.univ.filter (fun i => symplecticBit (s i) (P i))).card

def bellSign {n : ℕ} (s P : Pauli n) : ℝ := (-1 : ℝ) ^ symplecticParity s P

def bellOutcomeProb {n : ℕ} (lam : ℝ) (P s : Pauli n) : ℝ :=
  (4 : ℝ) ^ (-(n : ℝ)) * (1 + (1 - lam) ^ (2 * pauliWeight P) * bellSign s P)

def bellTestThreshold (n : ℕ) (lam : ℝ) : ℝ := (1 - lam) ^ (2 * (n : ℝ)) / 2

theorem symplecticBit_self (a : PauliChar) : symplecticBit a a = false := by
  fin_cases a <;> simp [symplecticBit, pauliBits]

theorem symplecticParity_self {n : ℕ} (P : Pauli n) : symplecticParity P P = 0 := by
  simp [symplecticParity, symplecticBit_self]

theorem bellSign_self {n : ℕ} (P : Pauli n) : bellSign P P = 1 := by
  simp [bellSign, symplecticParity_self]

theorem bell_law_via_depolScale {n : ℕ} {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P s : Pauli n) :
    bellOutcomeProb lam P s =
      (4 : ℝ) ^ (-(n : ℝ)) * (1 + depolScale lam P ^ 2 * bellSign s P) := by
  unfold bellOutcomeProb depolScale
  rw [← pow_mul, mul_comm (pauliWeight P) 2]

theorem bell_outcome_law_zero_noise {n : ℕ} (P s : Pauli n) :
    bellOutcomeProb 0 P s = (4 : ℝ) ^ (-(n : ℝ)) * (1 + bellSign s P) := by
  unfold bellOutcomeProb
  norm_num

theorem bell_outcome_zero_of_orthogonal {n : ℕ} (P s : Pauli n) (h : bellSign s P = -1) :
    bellOutcomeProb 0 P s = 0 := by
  rw [bell_outcome_law_zero_noise, h]
  ring

theorem bell_outcome_max_of_commuting {n : ℕ} (P s : Pauli n) (h : bellSign s P = 1) :
    bellOutcomeProb 0 P s = 2 * (4 : ℝ) ^ (-(n : ℝ)) := by
  rw [bell_outcome_law_zero_noise, h]
  ring

end Qatlib.Papers.NoisyLearn26.MainResults.ShadowNoise
