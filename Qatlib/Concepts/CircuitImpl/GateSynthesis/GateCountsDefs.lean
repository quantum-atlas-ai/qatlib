/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.MultiControl.BarencoSharp
import Qatlib.Concepts.ResourceBounds.AsymBounds.GatesBitDefs
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Two-level synthesis counts and parameter arithmetic

This module defines the two-level counts, per-instruction cost, and primitive budget used in the
Section 8 gate-synthesis accounting [BarencoEtAl1995]. It proves elementary relations and
exponential bounds between these numerical quantities.

The module also defines unitary and special-unitary parameter counts and computes the real
vector-space dimension of all complex operators on an `n`-qubit register.

## Main statements

* `section8TwoLevelCount_eq`: the upper count differs from the lower count by `2 ^ n` for
  positive `n`.
* `section8TwoLevelCount_bounds`: comparison of the two-level counts with `4 ^ n`.
* `unitaryParamCount_two_pow`: the unitary parameter count is `4 ^ n`.
* `qubitOperatorSpace_finrank`: the ambient real operator space has dimension `2 * 4 ^ n`.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CircuitImpl.MultiControl

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.CircuitImpl.GateSynthesis

open Matrix
open scoped Classical BigOperators

/-- For positive `n`, the power `2 ^ n` is `2 ^ (n - 1) * 2`. -/
theorem pow_two_mul_two (n : ℕ) (hn : 1 ≤ n) : 2 ^ n = 2 ^ (n - 1) * 2 := by
  calc 2 ^ n = 2 ^ (n - 1 + 1) := by congr 1; omega
    _ = 2 ^ (n - 1) * 2 := Nat.pow_succ 2 (n - 1)

/-- The `n`-th power of `2 ^ 2` equals `2 ^ (2 * n)`. -/
theorem pow_two_two (n : ℕ) : (2 ^ 2) ^ n = 2 ^ (2 * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Nat.pow_succ, ih, show 2 * (n + 1) = 2 * n + 2 from by omega, Nat.pow_add]

/-- The power `4 ^ n` equals `2 ^ (2 * n)`. -/
theorem pow_four (n : ℕ) : 4 ^ n = 2 ^ (2 * n) := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_two_two]

/-- The numerical two-level count `2 ^ (n - 1) * (2 ^ n + 1)` used in the Section 8 accounting. -/
def section8TwoLevelCount (n : ℕ) : ℕ := 2 ^ (n - 1) * (2 ^ n + 1)

/-- The numerical lower count `2 ^ (n - 1) * (2 ^ n - 1)` for two-level synthesis accounting. -/
def reckTwoLevelLower (n : ℕ) : ℕ := 2 ^ (n - 1) * (2 ^ n - 1)

/-- The per-instruction cost `(2 * n - 1) * (48 * n * n + 2 * n + 3699)`. -/
def section8InstructionCost (n : ℕ) : ℕ := (2 * n - 1) * (48 * n * n + 2 * n + 3699)

/-- The product of the Section 8 two-level count and its per-instruction cost. -/
def section8PrimitiveBudget (n : ℕ) : ℕ :=
  section8TwoLevelCount n * section8InstructionCost n

/-- The lower two-level count is at most `section8TwoLevelCount n`. -/
theorem reckTwoLevelLower_le (n : ℕ) :
    reckTwoLevelLower n ≤ section8TwoLevelCount n := by
  unfold reckTwoLevelLower section8TwoLevelCount
  exact Nat.mul_le_mul_left (2 ^ (n - 1))
    (Nat.le_trans (Nat.sub_le _ _) (Nat.le_add_right _ _))

/-- For positive `n`, the Section 8 two-level count equals the lower count plus `2 ^ n`. -/
theorem section8TwoLevelCount_eq (n : ℕ) (hn : 1 ≤ n) :
    section8TwoLevelCount n = reckTwoLevelLower n + 2 ^ n := by
  have hp : 2 ^ (n - 1) * 2 = 2 ^ n := by
    rw [← pow_two_mul_two n hn]
  have hone : 2 ^ n - 1 + 2 = 2 ^ n + 1 := by
    have h0 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h1 : 2 ^ n - 1 + 1 = 2 ^ n := Nat.sub_add_cancel h0
    omega
  have hsplit : 2 ^ (n - 1) * (2 ^ n + 1)
      = 2 ^ (n - 1) * (2 ^ n - 1) + 2 ^ (n - 1) * 2 := by
    rw [← hone, Nat.mul_add]
  unfold section8TwoLevelCount reckTwoLevelLower
  rw [hsplit, hp]

/-- For positive `n`, the lower and upper two-level counts lie between the stated constant
multiples of `4 ^ n`. -/
theorem section8TwoLevelCount_bounds (n : ℕ) (hn : 1 ≤ n) :
    4 ^ n ≤ 4 * reckTwoLevelLower n ∧
    reckTwoLevelLower n ≤ section8TwoLevelCount n ∧
    section8TwoLevelCount n ≤ 4 ^ n := by
  have hA : 1 ≤ 2 ^ (n - 1) := Nat.one_le_two_pow
  have hkey : 2 ^ (n - 1) ≤ 2 ^ n - 1 := by
    have h1 : 2 ^ (n - 1) + 1 ≤ 2 ^ n := by
      rw [pow_two_mul_two n hn]
      have hstep : 2 ^ (n - 1) + 1 ≤ 2 ^ (n - 1) + 2 ^ (n - 1) :=
        Nat.add_le_add_left hA (2 ^ (n - 1))
      rwa [show 2 ^ (n - 1) * 2 = 2 ^ (n - 1) + 2 ^ (n - 1) from by ring]
    have h3 : 2 ^ n - 1 + 1 = 2 ^ n := Nat.sub_add_cancel (Nat.one_le_two_pow)
    rw [← h3] at h1
    exact Nat.le_of_succ_le_succ h1
  have h4 : 4 ^ n = 2 ^ (n - 1) * 2 ^ (n - 1) * 4 := by
    have e1 : 2 ^ (2 * n) = 2 ^ ((n - 1) + (n - 1) + 2) := by
      rw [show 2 * n = (n - 1) + (n - 1) + 2 from by omega]
    have e2 : 2 ^ ((n - 1) + (n - 1) + 2) = 2 ^ (n - 1) * 2 ^ (n - 1) * 4 := by
      calc 2 ^ ((n - 1) + (n - 1) + 2)
          = 2 ^ ((n - 1) + (n - 1)) * 2 ^ 2 := Nat.pow_add 2 ((n - 1) + (n - 1)) 2
        _ = (2 ^ (n - 1) * 2 ^ (n - 1)) * 2 ^ 2 := by
              have hh : 2 ^ ((n - 1) + (n - 1)) = 2 ^ (n - 1) * 2 ^ (n - 1) :=
                Nat.pow_add 2 (n - 1) (n - 1)
              rw [hh]
        _ = 2 ^ (n - 1) * 2 ^ (n - 1) * 4 := by
              rw [show 2 ^ 2 = 4 from by norm_num]
    calc 4 ^ n = 2 ^ (2 * n) := pow_four n
      _ = 2 ^ ((n - 1) + (n - 1) + 2) := e1
      _ = 2 ^ (n - 1) * 2 ^ (n - 1) * 4 := e2
  refine ⟨?_, reckTwoLevelLower_le n, ?_⟩
  · have hmul : 2 ^ (n - 1) * 2 ^ (n - 1) ≤ 2 ^ (n - 1) * (2 ^ n - 1) :=
      Nat.mul_le_mul_left (2 ^ (n - 1)) hkey
    calc 4 ^ n = 2 ^ (n - 1) * 2 ^ (n - 1) * 4 := h4
      _ = 4 * (2 ^ (n - 1) * 2 ^ (n - 1)) := by ac_rfl
      _ ≤ 4 * (2 ^ (n - 1) * (2 ^ n - 1)) := Nat.mul_le_mul_left 4 hmul
      _ = 4 * reckTwoLevelLower n := by rfl
  · have h4a : 2 ^ (n - 1) * 2 + 1 ≤ 2 ^ (n - 1) * 4 := by omega
    calc section8TwoLevelCount n
        = 2 ^ (n - 1) * (2 ^ (n - 1) * 2 + 1) := by
          rw [section8TwoLevelCount, pow_two_mul_two n hn]
      _ ≤ 2 ^ (n - 1) * (2 ^ (n - 1) * 4) := Nat.mul_le_mul_left _ h4a
      _ = 2 ^ (n - 1) * 2 ^ (n - 1) * 4 := by ac_rfl
      _ = 4 ^ n := h4.symm

/-- The numerical unitary parameter count `d * d` at matrix dimension `d`. -/
def unitaryParamCount (d : ℕ) : ℕ := d * d

/-- The numerical special-unitary parameter count `d * d - 1`, using natural-number subtraction. -/
def suParamCount (d : ℕ) : ℕ := d * d - 1

/-- For positive `d`, the unitary parameter count equals `d + d * (d - 1)`. -/
theorem unitaryParamCount_eq (d : ℕ) (hd : 1 ≤ d) :
    unitaryParamCount d = d + d * (d - 1) := by
  have h : d + d * (d - 1) = d * d := by
    calc d + d * (d - 1) = d * 1 + d * (d - 1) := by rw [Nat.mul_one]
      _ = 1 * d + (d - 1) * d := by rw [Nat.mul_comm d 1, Nat.mul_comm d (d - 1)]
      _ = (1 + (d - 1)) * d := (Nat.add_mul 1 (d - 1) d).symm
      _ = d * d := by rw [show 1 + (d - 1) = d from by omega]
  exact h.symm

/-- At matrix dimension `2 ^ n`, the unitary parameter count equals `4 ^ n`. -/
theorem unitaryParamCount_two_pow (n : ℕ) : unitaryParamCount (2 ^ n) = 4 ^ n := by
  unfold unitaryParamCount
  have h1 : 2 ^ n * 2 ^ n = 2 ^ (n + n) := (Nat.pow_add 2 n n).symm
  rw [h1, pow_four]
  congr 1
  omega

/-- At matrix dimension `2 ^ n`, the special-unitary parameter count equals `4 ^ n - 1`. -/
theorem suParamCount_two_pow (n : ℕ) : suParamCount (2 ^ n) = 4 ^ n - 1 := by
  have h := unitaryParamCount_two_pow n
  show 2 ^ n * 2 ^ n - 1 = 4 ^ n - 1
  rw [← h]
  rfl

/-- At positive matrix dimension, the special-unitary parameter count is strictly smaller than
the unitary parameter count. -/
theorem suParamCount_lt (d : ℕ) (hd : 1 ≤ d) : suParamCount d < unitaryParamCount d := by
  unfold suParamCount unitaryParamCount
  exact Nat.sub_lt_of_pos_le (by norm_num : (0 : ℕ) < 1)
    (Nat.mul_le_mul (by omega) (by omega))

/-- The space of complex matrices indexed by pairs of `n`-qubit computational basis labels. -/
abbrev qubitOperatorSpace (n : ℕ) : Type :=
  (Fin n → Fin 2) → (Fin n → Fin 2) → ℂ

/-- The real dimension of the complex operator space on `n` qubits is `2 * 4 ^ n`. -/
theorem qubitOperatorSpace_finrank (n : ℕ) :
    Module.finrank ℝ (qubitOperatorSpace n) = 2 * 4 ^ n := by
  simp only [Module.finrank_pi_fintype, Fintype.card_fin, Finset.card_univ,
    Finset.sum_const, smul_eq_mul, Fintype.card_fun]
  rw [Complex.finrank_real_complex]
  calc 2 ^ n * (2 ^ n * 2) = 2 * (2 ^ n * 2 ^ n) := by ring
    _ = 2 * 2 ^ (n + n) := by rw [Nat.pow_add]
    _ = 2 * 2 ^ (2 * n) := by congr 2; omega
    _ = 2 * 4 ^ n := by rw [← pow_four]

end Qatlib.Concepts.CircuitImpl.GateSynthesis

end
