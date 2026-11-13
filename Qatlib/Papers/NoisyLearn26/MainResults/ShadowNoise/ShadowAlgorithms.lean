/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoisyLearn26.MainResults.Models.InterfaceModels

/-!
# Pauli signs and noisy Bell outcome formulas

Encodes Pauli labels by Boolean pairs and defines the associated symplectic count and Bell sign.
The explicit function `bellOutcomeProb` is rewritten using `depolScale`, and its zero-noise
values are computed for signs `-1` and `1`. See [CotlerGongKannan2025] for the surrounding
analysis.

## Main statements

* `bell_law_via_depolScale`: For noise in `[0, 1]`, `bellOutcomeProb` equals `4^(-n) * (1 +
  (depolScale lam P)² * bellSign s P)`.
* `bell_outcome_zero_of_orthogonal`: At zero noise, a Bell sign of `-1` makes the outcome
  expression zero.
* `bell_outcome_max_of_commuting`: At zero noise, a Bell sign of `1` makes the outcome
  expression equal to `2 * 4^(-n)`.

## References

* [Cotler et al., 2025][CotlerGongKannan2025]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyLearn26.MainResults.ShadowNoise

open Qatlib.Papers.NoisyLearn26.MainResults

open scoped BigOperators

/-- The Boolean pair encoding of the four Pauli labels as `(0, 0)`, `(1, 0)`, `(1, 1)`, and `(0,
1)`. -/
def pauliBits (a : PauliChar) : Bool × Bool :=
  if a = 0 then (false, false)
  else if a = 1 then (true, false)
  else if a = 2 then (true, true)
  else (false, true)

/-- The Boolean symplectic pairing of the two Pauli-label encodings. -/
def symplecticBit (a b : PauliChar) : Bool :=
  Bool.xor ((pauliBits a).1 && (pauliBits b).2) ((pauliBits a).2 && (pauliBits b).1)

/-- The number of positions where the Boolean symplectic pairing of two Pauli strings is true. -/
def symplecticParity {n : ℕ} (s P : Pauli n) : ℕ :=
  (Finset.univ.filter (fun i => symplecticBit (s i) (P i))).card

/-- The sign `(-1) ^ symplecticParity s P`. -/
def bellSign {n : ℕ} (s P : Pauli n) : ℝ := (-1 : ℝ) ^ symplecticParity s P

/-- The scalar Bell outcome expression `4^(-n) * (1 + (1 - lam)^(2 * pauliWeight P) * bellSign s
P)`. -/
def bellOutcomeProb {n : ℕ} (lam : ℝ) (P s : Pauli n) : ℝ :=
  (4 : ℝ) ^ (-(n : ℝ)) * (1 + (1 - lam) ^ (2 * pauliWeight P) * bellSign s P)

/-- The scalar Bell-test threshold `(1 - lam)^(2n) / 2`. -/
def bellTestThreshold (n : ℕ) (lam : ℝ) : ℝ := (1 - lam) ^ (2 * (n : ℝ)) / 2

/-- The Boolean symplectic pairing of a Pauli label with itself is false. -/
theorem symplecticBit_self (a : PauliChar) : symplecticBit a a = false := by
  fin_cases a <;> simp [symplecticBit, pauliBits]

/-- The symplectic count of a Pauli string with itself is zero. -/
theorem symplecticParity_self {n : ℕ} (P : Pauli n) : symplecticParity P P = 0 := by
  simp [symplecticParity, symplecticBit_self]

/-- The Bell sign of a Pauli string paired with itself is one. -/
theorem bellSign_self {n : ℕ} (P : Pauli n) : bellSign P P = 1 := by
  simp [bellSign, symplecticParity_self]

/-- For noise in `[0, 1]`, `bellOutcomeProb` equals `4^(-n) * (1 + (depolScale lam P)² *
bellSign s P)`. -/
theorem bell_law_via_depolScale {n : ℕ} {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P s : Pauli n) :
    bellOutcomeProb lam P s =
      (4 : ℝ) ^ (-(n : ℝ)) * (1 + depolScale lam P ^ 2 * bellSign s P) := by
  unfold bellOutcomeProb depolScale
  rw [← pow_mul, mul_comm (pauliWeight P) 2]

/-- At zero noise, the Bell outcome expression is `4^(-n) * (1 + bellSign s P)`. -/
theorem bell_outcome_law_zero_noise {n : ℕ} (P s : Pauli n) :
    bellOutcomeProb 0 P s = (4 : ℝ) ^ (-(n : ℝ)) * (1 + bellSign s P) := by
  unfold bellOutcomeProb
  norm_num

/-- At zero noise, a Bell sign of `-1` makes the outcome expression zero. -/
theorem bell_outcome_zero_of_orthogonal {n : ℕ} (P s : Pauli n) (h : bellSign s P = -1) :
    bellOutcomeProb 0 P s = 0 := by
  rw [bell_outcome_law_zero_noise, h]
  ring

/-- At zero noise, a Bell sign of `1` makes the outcome expression equal to `2 * 4^(-n)`. -/
theorem bell_outcome_max_of_commuting {n : ℕ} (P s : Pauli n) (h : bellSign s P = 1) :
    bellOutcomeProb 0 P s = 2 * (4 : ℝ) ^ (-(n : ℝ)) := by
  rw [bell_outcome_law_zero_noise, h]
  ring

end Qatlib.Papers.NoisyLearn26.MainResults.ShadowNoise
