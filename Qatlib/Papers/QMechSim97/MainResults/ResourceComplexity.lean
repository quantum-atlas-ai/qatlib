/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMechSim97.MainResults.Defs
import Mathlib.Tactic

/-!
# Lattice simulation resource arithmetic

Derives explicit bounds for the resource expressions used in the lattice simulation of
[BoghosianTaylor1998]. The module compares classical component counts with quantum gate counts,
computes the register basis cardinality, and verifies numerical resource examples.

## Main statements

* `quantum_register_card`: The lattice quantum register has `2 ^ qubitCount d l` basis
  configurations.
* `classical_exponential_in_particles`: For `l ≥ 2` and `d ≥ 1`, the classical component count
  for `n` particles is at least `2 ^ n`.

## References

* [Boghosian and Taylor, 1998][BoghosianTaylor1998]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QMechSim97.MainResults.ResourceComplexity

open Qatlib.Papers.QMechSim97.MainResults.Defs

/-- The interaction gate count equals `d ^ 2 * (l ^ d) ^ 2`. -/
theorem interactionGates_eq (d l : ℕ) :
    interactionGates d l = d ^ 2 * (l ^ d) ^ 2 := by
  unfold interactionGates
  rw [show l ^ (2 * d) = (l ^ d) ^ 2 by rw [mul_comm 2 d, pow_mul]]

/-- The classical component count for `n` particles equals `(l ^ d) ^ n`. -/
theorem classicalComponents_eq (d l n : ℕ) :
    classicalComponents d l n = (l ^ d) ^ n := by
  unfold classicalComponents
  exact pow_mul l d n

/-- For `l ≥ 1`, the total quantum gate count is at most `(d + 2 * d ^ 2) * (l ^ d) ^ 2`. -/
theorem totalQuantumGates_le (d l : ℕ) (hl : 1 ≤ l) :
    totalQuantumGates d l ≤ (d + 2 * d ^ 2) * (l ^ d) ^ 2 := by
  have hl1 : 1 ≤ l ^ d := one_le_pow₀ hl
  have hpow2 : l ^ d ≤ (l ^ d) ^ 2 := by
    simpa using pow_le_pow_right₀ hl1 (show 1 ≤ 2 by norm_num)
  unfold totalQuantumGates propagationGates kineticGates interactionGates
  rw [show l ^ (2 * d) = (l ^ d) ^ 2 by rw [mul_comm 2 d, pow_mul]]
  calc d * l ^ d + d ^ 2 * l ^ d + d ^ 2 * (l ^ d) ^ 2
      ≤ d * (l ^ d) ^ 2 + d ^ 2 * (l ^ d) ^ 2 + d ^ 2 * (l ^ d) ^ 2 := by gcongr
    _ = (d + 2 * d ^ 2) * (l ^ d) ^ 2 := by ring

/-- For `l ≥ 2` and `n ≥ 2`, the classical component count multiplied by `d + 2 * d ^ 2` bounds
the quantum gate count multiplied by `(l ^ d) ^ (n - 2)`. -/
theorem classical_dominates (d l n : ℕ) (hl : 2 ≤ l) (hn : 2 ≤ n) :
    (d + 2 * d ^ 2) * classicalComponents d l n ≥
      (l ^ d) ^ (n - 2) * totalQuantumGates d l := by
  have hl1 : 1 ≤ l := by omega
  have hqn : classicalComponents d l n = (l ^ d) ^ (n - 2) * (l ^ d) ^ 2 := by
    rw [classicalComponents_eq]
    conv_lhs => rw [show n = (n - 2) + 2 by omega]
    rw [pow_add]
  have hfactor : (d + 2 * d ^ 2) * ((l ^ d) ^ (n - 2) * (l ^ d) ^ 2)
      = (l ^ d) ^ (n - 2) * ((d + 2 * d ^ 2) * (l ^ d) ^ 2) := by
    rw [← mul_assoc, mul_comm (d + 2 * d ^ 2) ((l ^ d) ^ (n - 2)), mul_assoc]
  calc (d + 2 * d ^ 2) * classicalComponents d l n
      = (d + 2 * d ^ 2) * ((l ^ d) ^ (n - 2) * (l ^ d) ^ 2) := by rw [hqn]
    _ = (l ^ d) ^ (n - 2) * ((d + 2 * d ^ 2) * (l ^ d) ^ 2) := hfactor
    _ ≥ (l ^ d) ^ (n - 2) * totalQuantumGates d l :=
        Nat.mul_le_mul_left _ (totalQuantumGates_le d l hl1)

/-- The classical component count for twenty particles on a three-dimensional lattice of side
twenty equals `20 ^ 60`. -/
theorem example_classical_eq : classicalComponents 3 20 20 = 20 ^ 60 := by
  unfold classicalComponents; norm_num

/-- The classical component count for the specified twenty-particle lattice exceeds `10 ^ 77`. -/
theorem example_classical_gt_10_77 : classicalComponents 3 20 20 > 10 ^ 77 := by
  rw [example_classical_eq]; norm_num

/-- The interaction gate count for a three-dimensional lattice of side twenty equals `9 * 20 ^
6`. -/
theorem example_interaction_eq : interactionGates 3 20 = 9 * 20 ^ 6 := by
  unfold interactionGates; norm_num

/-- The total quantum gate count for a three-dimensional lattice of side twenty is less than
`2300000000`. -/
theorem example_quantum_lt : totalQuantumGates 3 20 < 2300000000 := by
  unfold totalQuantumGates propagationGates kineticGates interactionGates; norm_num

/-- A register of `N` Boolean occupation wires has `2 ^ N` basis configurations. -/
theorem register_card (N : ℕ) : Fintype.card (Fin N → Bool) = 2 ^ N := by
  simp

/-- The lattice quantum register has `2 ^ qubitCount d l` basis configurations. -/
theorem quantum_register_card (d l : ℕ) :
    Fintype.card (Fin (qubitCount d l) → Bool) = 2 ^ qubitCount d l :=
  register_card (qubitCount d l)

/-- For `l ≥ 2` and `d ≥ 1`, the classical component count for `n` particles is at least `2 ^
n`. -/
theorem classical_exponential_in_particles (d l n : ℕ) (hl : 2 ≤ l) (hd : 1 ≤ d) :
    2 ^ n ≤ classicalComponents d l n := by
  rw [classicalComponents_eq]
  have hl1 : 1 ≤ l := by omega
  have hld : l ≤ l ^ d := le_self_pow hl1 (by omega)
  have h2l : 2 ≤ l ^ d := le_trans hl hld
  exact pow_le_pow_left' h2l n

end Qatlib.Papers.QMechSim97.MainResults.ResourceComplexity
