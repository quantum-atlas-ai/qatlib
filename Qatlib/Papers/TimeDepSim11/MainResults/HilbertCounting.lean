/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Exponentially small reachable volume in Hilbert space

Source: Poulin–Qarry–Somma–Verstraete, "Quantum simulation of time-dependent
Hamiltonians and the convenient illusion of Hilbert space", fixed arXiv:1102.1360v1
(7 Feb 2011). Counting argument on p. 4:

`N_circuits = (M K²)^{K^α}` distinct circuits/states;
`S = 2 π^{2^K} / Γ(2^K)` surface area of the `(2^{K+1}-1)`-sphere;
`V = 2 π^{2^K - 1} ε^{2^{K+1}-2} / Γ(2^K)` volume of an ε-ball;
hence `N_circuits V / S = O(K^K ε^{2^K})`.

This module formalises the exact ratio `V/S = ε^{2^{K+1}-2}/π` and the resulting
`N_circuits ε^{2^{K+1}-2}/π` fraction, together with the exponential-smallness
bound `ε^{2^{K+1}-2} ≤ ε^{2^K}` for `0 < ε ≤ 1`, `K ≥ 1`. The paper's Big-O is the
asymptotic reading of the exact count; the exact exponent `2^{K+1}-2` dominates `2^K`
and makes the fraction doubly-exponentially small in `K` for `ε < 1`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.TimeDepSim11.MainResults.HilbertCounting

/-- Surface area `S = 2 π^{2^K} / Γ(2^K)` of the `(2^{K+1}-1)`-dimensional sphere
in the paper's counting argument (p. 4). -/
noncomputable def ballSurface (K : ℕ) : ℝ :=
  2 * Real.pi ^ (2 ^ K) / Real.Gamma ((2 ^ K : ℕ) : ℝ)

/-- Volume `V = 2 π^{2^K-1} ε^{2^{K+1}-2} / Γ(2^K)` of an ε-ball in that sphere
(p. 4). -/
noncomputable def ballVolume (K : ℕ) (ε : ℝ) : ℝ :=
  2 * Real.pi ^ (2 ^ K - 1) * ε ^ (2 ^ (K + 1) - 2) / Real.Gamma ((2 ^ K : ℕ) : ℝ)

/-- Number `N_circuits = (M K²)^{K^α}` of distinct polynomial-size circuits with a
`M`-element gate set and `M K²` choices per gate (p. 4). -/
noncomputable def circuitCount (M : ℝ) (K : ℕ) (α : ℝ) : ℝ :=
  Real.rpow (M * (K : ℝ) ^ 2) (Real.rpow (K : ℝ) α)

/-- Exact ratio of the ε-ball volume to the sphere surface:
`V/S = ε^{2^{K+1}-2}/π`. This is the `K`-independent-cancellation step of the paper's
`N_circuits V/S = O(K^K ε^{2^K})` computation (p. 4). -/
theorem volume_ratio_eq (K : ℕ) (ε : ℝ) :
    ballVolume K ε / ballSurface K = ε ^ (2 ^ (K + 1) - 2) / Real.pi := by
  unfold ballVolume ballSurface
  have hπ : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hΓ : Real.Gamma ((2 ^ K : ℕ) : ℝ) ≠ 0 := by
    apply ne_of_gt
    exact Real.Gamma_pos_of_pos (by positivity)
  have hpow : Real.pi ^ (2 ^ K) = Real.pi ^ (2 ^ K - 1) * Real.pi := by
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_two_pow)]
  field_simp
  rw [hpow]
  ring

/-- The fraction of Hilbert space occupied by the ε-balls of all reachable states:
`N_circuits · (V/S) = N_circuits · ε^{2^{K+1}-2}/π`. -/
theorem circuit_balls_fraction_eq (M : ℝ) (K : ℕ) (α ε : ℝ) :
    circuitCount M K α * (ballVolume K ε / ballSurface K)
      = circuitCount M K α * (ε ^ (2 ^ (K + 1) - 2) / Real.pi) := by
  rw [volume_ratio_eq]

/-- The ε-exponent comparison `2^{K+1}-2 ≥ 2^K` for `K ≥ 1`, hence for `0 < ε ≤ 1` the
ball fraction exponent dominates `2^K`. -/
theorem epsilon_power_exponent_le (K : ℕ) (hK : 1 ≤ K) (ε : ℝ)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ε ^ (2 ^ (K + 1) - 2) ≤ ε ^ (2 ^ K) := by
  apply pow_le_pow_of_le_one hε0.le hε1
  have h2 : 2 ≤ 2 ^ K := by
    have hlt : 1 < 2 ^ K := Nat.one_lt_two_pow (Nat.ne_of_gt hK)
    omega
  have hpow : 2 ^ (K + 1) = 2 * 2 ^ K := by rw [pow_succ]; ring
  rw [hpow]
  omega

/-- Exponential-smallness of the reachable fraction: for `0 < ε ≤ 1` and `K ≥ 1`,
`N_circuits · (V/S) ≤ N_circuits · ε^{2^K}/π`. Since `0 < ε < 1`, `ε^{2^K}` is
doubly-exponentially small in `K`; this is the paper's conclusion that the
overwhelming majority of Hilbert space is unreachable in polynomial time. -/
theorem circuit_balls_fraction_bound (M : ℝ) (K : ℕ) (hK : 1 ≤ K) (α ε : ℝ)
    (hM : 0 ≤ M) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    circuitCount M K α * (ballVolume K ε / ballSurface K)
      ≤ circuitCount M K α * (ε ^ (2 ^ K) / Real.pi) := by
  rw [volume_ratio_eq]
  apply mul_le_mul_of_nonneg_left
  · apply div_le_div_of_nonneg_right (epsilon_power_exponent_le K hK ε hε0 hε1)
    exact Real.pi_pos.le
  · unfold circuitCount
    apply Real.rpow_nonneg
    have : 0 ≤ (K : ℝ) ^ 2 := sq_nonneg _
    positivity

end Qatlib.Papers.TimeDepSim11.MainResults.HilbertCounting
